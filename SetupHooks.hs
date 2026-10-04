{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 914
{-# OPTIONS_GHC -fobject-determinism #-}
#endif
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StaticPointers #-}

-- Build-local generated modules and deterministic dependency loading for the
-- monolithic compiler library, tools and test runners. Native solver builds run
-- once, sequentially, for the main library; they still use their vendor trees.
module SetupHooks (setupHooks) where

import Control.Monad (filterM, forM, forM_, unless, when)
import Control.Monad.IO.Class (liftIO)
import Data.Char (isSpace)
import Data.List (isPrefixOf, nub, sort)
import Data.Maybe (fromMaybe)
import Data.String (fromString)
import Distribution.Compiler (CompilerFlavor (..))
import Distribution.InstalledPackageInfo (ExposedModule (..))
import qualified Distribution.InstalledPackageInfo as IPI
import Distribution.ModuleName (ModuleName)
import Distribution.Pretty (prettyShow)
import Distribution.Simple.Compiler (compilerFlavor, compilerVersion)
import Distribution.Simple.Configure (getInstalledPackages)
import Distribution.Simple.Glob (matchDirFileGlob)
import Distribution.Simple.LocalBuildInfo
  ( hostPlatform,
    interpretSymbolicPathLBI,
    mbWorkDirLBI,
    withPackageDB,
    withPrograms,
  )
import qualified Distribution.Simple.LocalBuildInfo as LBI
import Distribution.Simple.PackageIndex (lookupUnitId)
import Distribution.Simple.PreProcess (PreProcessor (runPreProcessor), ppUnlit)
import Distribution.Simple.Setup (fromFlagOrDefault)
import Distribution.Simple.SetupHooks
import Distribution.Simple.Utils (die')
import Distribution.System (OS (..))
import qualified Distribution.Types.LocalBuildConfig as LBC
import Distribution.Types.Flag (FlagAssignment, lookupFlagAssignment, mkFlagName)
import Distribution.Utils.Path
  ( makeSymbolicPath,
    makeRelativePathEx,
    moduleNameSymbolicPath,
    getSymbolicPath,
    (<.>),
  )
import Distribution.Verbosity (normal)
import Distribution.Version (mkVersion)
import System.Directory
  ( canonicalizePath,
    createDirectoryIfMissing,
    doesFileExist,
    findExecutable,
    makeAbsolute,
    removeFile,
  )
import System.Environment (getEnvironment, lookupEnv)
import System.Exit (ExitCode (..))
import System.FilePath (takeDirectory, takeExtension, takeFileName, (</>))
import System.IO (readFile')
import System.Process
  ( CreateProcess (..),
    callProcess,
    createProcess,
    proc,
    readProcess,
    readProcessWithExitCode,
    waitForProcess,
  )

setupHooks :: SetupHooks
setupHooks =
  compilerSetupHooks
    <> warmupSetupHooks
    <> sourceViewSetupHooks
    <> generatedModulesSetupHooks
    <> solverSetupHooks
    <> tclSetupHooks

repoRoot :: FilePath
repoRoot = "."

-- | Run a process to completion, failing if it does.
--
-- process-1.6.28 exports this as callCreateProcess, but GHC 9.14.1 bundles
-- 1.6.26, and a floor that excludes the bundled version makes cabal build
-- process from Hackage. Spelling it out keeps the hooks on the compiler's
-- own bundled process.
callCreateProcess :: CreateProcess -> IO ()
callCreateProcess cp = do
  (_, _, _, handle) <- createProcess cp
  code <- waitForProcess handle
  case code of
    ExitSuccess -> pure ()
    ExitFailure n -> ioError (userError ("setup command failed with " <> show n))

isMainLib :: Component -> Bool
isMainLib (CLib Library {libName = LMainLibName}) = True
isMainLib _ = False

-- | Write the file only if its content changes, so an unchanged generated
-- module keeps its timestamp.
writeFileChanged :: FilePath -> String -> IO ()
writeFileChanged path new = do
  createDirectoryIfMissing True (takeDirectory path)
  exists <- doesFileExist path
  same <- if exists then (== new) <$> readFile' path else pure False
  unless same (writeFile path new)

-- | The autogen location of a generated module of the component.
autogenLocation :: LocalBuildInfo -> ComponentLocalBuildInfo -> ModuleName -> Location
autogenLocation lbi clbi m =
  Location (autogenComponentModulesDir lbi clbi) (moduleNameSymbolicPath m <.> "hs")

-- | A location as the file path the action that writes it uses.
locationFilePath :: LocalBuildInfo -> Location -> FilePath
locationFilePath lbi loc = interpretSymbolicPathLBI lbi (location loc)

-- | Fail early if the compiler cannot build this Hooks/GHC2021 package.
--
compilerSetupHooks :: SetupHooks
compilerSetupHooks = noSetupHooks {configureHooks}
  where
    configureHooks = noConfigureHooks {preConfPackageHook}

    preConfPackageHook :: Maybe PreConfPackageHook
    preConfPackageHook = Just $ \inputs -> do
      let comp = inputs.compiler
          verbosity = fromFlagOrDefault normal (configVerbosity inputs.configFlags)
          supported =
            compilerFlavor comp == GHC && compilerVersion comp >= mkVersion [9, 6]
      unless supported $
        die' verbosity $
          "the Cabal build requires GHC 9.6 or newer; found " <> prettyShow (compilerId comp)
      pure (noPreConfPackageOutputs inputs)

-- | Give every Haskell component its own dependency-loading barrier.
wantsWarmup :: Component -> Bool
wantsWarmup CLib {} = True
wantsWarmup CExe {} = True
wantsWarmup CTest {} = True
wantsWarmup CBench {} = True
wantsWarmup _ = False

-- | Import all modules of direct dependencies in a stable order before the
-- component's roots compile. This stabilizes GHC's external rule/instance
-- visibility under --make -j; -fobject-determinism separately stabilizes uniques.
-- Resolve exact dependency unit IDs against the CURRENT package databases at
-- build time, since in-place dependencies can change exports without changing ID.
warmupSetupHooks :: SetupHooks
warmupSetupHooks = noSetupHooks {buildHooks}
  where
    buildHooks = noBuildHooks {preBuildComponentRules}

    -- Generate the module.
    preBuildComponentRules :: Maybe PreBuildComponentRules
    preBuildComponentRules = Just . rules (static ()) $ \env -> do
      let lbi = env.localBuildInfo
          clbi = env.targetInfo.targetCLBI
          verbosity = buildingWhatVerbosity env.buildingWhat
      when (wantsWarmup (targetComponent env.targetInfo)) $ do
        -- The package databases are read here, at build time, not taken from
        -- the configure-time snapshot in installedPkgs lbi. cabal-install does
        -- not reconfigure a package when a dependency's exposed-modules
        -- change (an in-place unit id such as bsc-2026.1-inplace is
        -- stable), so the snapshot goes stale as soon as modules move between
        -- packages, and a Warmup generated from it imports modules its
        -- dependency no longer exposes. This computation re-runs on every
        -- build, after the dependencies were registered, so the index is
        -- current; and because the module list is an argument of the rule's
        -- command, Cabal re-runs the rule when the list changes. This is the
        -- body of Cabal's getInstalledPackagesById, with die' for its
        -- exception.
        index <-
          liftIO $
            getInstalledPackages
              verbosity
              (LBI.compiler lbi)
              (mbWorkDirLBI lbi)
              (withPackageDB lbi)
              (withPrograms lbi)
        -- The index holds the external packages and every in-place library
        -- built before this component, which Cabal's build order guarantees
        -- for the dependencies; a dependency missing from it would make an
        -- incomplete Warmup, so it is an error rather than a gap.
        direct <- liftIO . forM (componentPackageDeps clbi) $ \(unit, _) ->
          case lookupUnitId index unit of
            Just ipi -> pure ipi
            Nothing ->
              die' verbosity $
                "Warmup: dependency " <> prettyShow unit
                  <> " is not in the installed package index"
        let units = sort [prettyShow (IPI.installedUnitId ipi) | ipi <- direct]
            mods =
              sort . nub $
                [ m
                  | ipi <- direct,
                    e <- IPI.exposedModules ipi,
                    let m = prettyShow (exposedName e),
                    m /= "Warmup"
                ]
            warmup = autogenLocation lbi clbi "Warmup"
        let native = if isMainLib (targetComponent env.targetInfo)
                       then Just (nativeBuildFor lbi) else Nothing
        nativeDeps <- case native of
          Nothing -> pure []
          Just _ -> liftIO $ nativeDependencies lbi
        registerRule_ "Warmup.hs" $
          staticRule
            ( mkCommand
                (static Dict)
                (static writeWarmupHs)
                (locationFilePath lbi warmup, units, mods, native)
            )
            nativeDeps
            [warmup]

writeWarmupHs :: (FilePath, [String], [String], Maybe NativeBuild) -> IO ()
writeWarmupHs (path, units, mods, native) = do
  forM_ native buildNative
  writeFileChanged path . unlines $
    [ "-- Generated by SetupHooks.hs; do not edit.",
      "-- An import of every exposed module of every direct dependency of this",
      "-- component, so that the external interface set enters GHC's EPS in one",
      "-- deterministic order before any other module compiles; see",
      "-- warmupSetupHooks in SetupHooks.hs for why.",
      "-- Direct dependencies, as resolved for this build:"
    ]
      <> ["--   " <> u | u <- units]
      <> ["module Warmup where"]
      <> ["import " <> m <> " ()" | m <- mods]

-- | Stage original library modules as tracked rule outputs (.lhs uses Cabal unlit).
-- GHC searches only this local source view, so a Make-generated source-tree
-- BuildVersion/Warmup cannot shadow the versions belonging to this Cabal build.
-- No module ownership or compiler algorithm changes are involved.
sourceViewSetupHooks :: SetupHooks
sourceViewSetupHooks = noSetupHooks {buildHooks = noBuildHooks {preBuildComponentRules}}
  where
    preBuildComponentRules = Just . rules (static ()) $ \env ->
      case targetComponent env.targetInfo of
        CLib lib | isMainLib (CLib lib) -> do
          let lbi = env.localBuildInfo
              clbi = env.targetInfo.targetCLBI
              modules = filter (\m -> m /= "BuildSystem" && m /= "BuildVersion")
                          (exposedModules lib)
          forM_ modules $ \m -> do
            let relative = getSymbolicPath (moduleNameSymbolicPath m)
            found <- liftIO $ filterM (doesFileExist . snd)
              [(ext, root </> relative <> ext) | root <- sourceRoots, ext <- [".hs", ".lhs"]]
            (_ext, source) <- case found of
              [x] -> pure x
              _ -> liftIO $ ioError (userError ("expected exactly one source for " <> prettyShow m <> ": " <> show found))
            let out = Location (autogenComponentModulesDir lbi clbi)
                         (moduleNameSymbolicPath m <.> "hs")
                input = Location (makeSymbolicPath ".") (makeRelativePathEx source)
            registerRule_ (fromString (prettyShow m <> ".source")) $
              staticRule (mkCommand (static Dict) (static copySource)
                (source, locationFilePath lbi out)) [FileDependency input] [out]
        _ -> pure ()

sourceRoots :: [FilePath]
sourceRoots =
  ["src/Parsec", "src/comp", "src/comp/GHC/posix", "src/comp/Libs",
   "src/vendor/htcl", "src/vendor/stp/HaskellIfc", "src/vendor/yices/v2.6/HaskellIfc"]

copySource :: (FilePath, FilePath) -> IO ()
copySource (source, target)
  | takeExtension source == ".lhs" = do
      -- Hooks demand generated Haskell modules as .hs. Use Cabal's standard
      -- literate preprocessor, retaining source positions and CPP directives.
      createDirectoryIfMissing True (takeDirectory target)
      let temporary = target <> ".new"
      runPreProcessor ppUnlit ("", source) ("", temporary) normal
      contents <- readFile' temporary
      removeFile temporary
      writeFileChanged target contents
  | otherwise = readFile' source >>= writeFileChanged target

-- | Generate platform/version modules locally for the compiler library.
generatedModulesSetupHooks :: SetupHooks
generatedModulesSetupHooks = noSetupHooks {buildHooks}
  where
    buildHooks = noBuildHooks {preBuildComponentRules}

    -- Generate the modules.
    preBuildComponentRules :: Maybe PreBuildComponentRules
    preBuildComponentRules = Just . rules (static ()) $ \env -> do
      let lbi = env.localBuildInfo
          clbi = env.targetInfo.targetCLBI
          buildSystem = autogenLocation lbi clbi "BuildSystem"
          buildVersion = autogenLocation lbi clbi "BuildVersion"
      when (isMainLib (targetComponent env.targetInfo)) $ do
        context <- liftIO (buildVersionContext lbi)
        gitDeps <- liftIO (gitDependencies lbi)
        registerRule_ "BuildSystem.hs" $
          staticRule
            ( mkCommand
                (static Dict)
                (static writeBuildSystemHs)
                (locationFilePath lbi buildSystem, hostPlatform lbi)
            )
            []
            [buildSystem]
        registerRule_ "BuildVersion.hs" $
          staticRule
            ( mkCommand
                (static Dict)
                (static writeBuildVersionHs)
                (interpretSymbolicPathLBI lbi (autogenComponentModulesDir lbi clbi), context)
            )
            (FileDependency (Location (makeSymbolicPath ".")
              (makeRelativePathEx "src/comp/update-build-version.sh")) : gitDeps)
            [buildVersion]

writeBuildSystemHs :: (FilePath, Platform) -> IO ()
writeBuildSystemHs (path, Platform _ os) = do
  binFmtType <- case os of
    Linux -> pure "ELF"
    OSX -> pure "MachO"
    _ -> ioError (userError ("unsupported OS: " <> show os))
  writeFileChanged path . unlines $
    [ "module BuildSystem",
      "  ( BinFmtType(..),",
      "    binFmtToString,",
      "    getBinFmtType,",
      "  )",
      "where",
      "",
      "import Warmup ()",
      "",
      "data BinFmtType = ELF | MachO",
      "",
      "binFmtToString :: BinFmtType -> String",
      "binFmtToString ELF   = \"ELF\"",
      "binFmtToString MachO = \"Mach-O\"",
      "",
      "getBinFmtType :: BinFmtType",
      "getBinFmtType = " <> binFmtType
    ]

-- | Keep Git lookup relative to the source tree, including with an external
-- --builddir, but write only to this component's autogen directory.
flagSet :: FlagAssignment -> String -> Bool
flagSet flags name = fromMaybe False (lookupFlagAssignment (mkFlagName name) flags)

buildVersionContext :: LocalBuildInfo -> IO (String, String, String)
buildVersionContext lbi = do
  let noGit = if flagSet (LBI.flagAssignment lbi) "no-git" then "1" else "0"
      noUpdate = if flagSet (LBI.flagAssignment lbi) "no-update-build-version" then "1" else "0"
  git <- findExecutable "git"
  revision <- case git of
    Just exe | noGit /= "1" && noUpdate /= "1" -> do
      (_, commit, _) <- readProcessWithExitCode exe ["rev-parse", "HEAD"] ""
      (_, describe, _) <- readProcessWithExitCode exe ["describe", "--tags"] ""
      pure (commit <> describe)
    _ -> pure ""
  pure (noGit, noUpdate, revision)

-- Track existing Git metadata through build-rule dependencies, not the source
-- distribution. Configured flags are the reliable way to change version policy;
-- ambient environment changes alone do not invalidate an up-to-date Cabal build.
gitDependencies :: LocalBuildInfo -> IO [Dependency]
gitDependencies lbi
  | flagSet (LBI.flagAssignment lbi) "no-git" = pure []
  | flagSet (LBI.flagAssignment lbi) "no-update-build-version" = pure []
  | otherwise = do
      git <- findExecutable "git"
      case git of
        Nothing -> pure []
        Just exe -> do
          (_, branch, _) <- readProcessWithExitCode exe ["symbolic-ref", "-q", "HEAD"] ""
          let trim = reverse . dropWhile isSpace . reverse
              names = ["HEAD", "packed-refs"] <> [trim branch | not (null branch)]
          paths <- forM names $ \name -> do
            (code, path, _) <- readProcessWithExitCode exe ["rev-parse", "--git-path", name] ""
            pure [trim path | code == ExitSuccess && not (null path)]
          existing <- filterM doesFileExist (concat paths)
          absolute <- mapM makeAbsolute existing
          pure [FileDependency (Location (makeSymbolicPath (takeDirectory path))
                  (makeRelativePathEx (takeFileName path))) | path <- absolute]

writeBuildVersionHs :: (FilePath, (String, String, String)) -> IO ()
writeBuildVersionHs (autogenDir, (noGit, noUpdate, _revision)) = do
  let newVars = [("NOGIT", noGit), ("NOUPDATEBUILDVERSION", noUpdate)]
  -- Remove inherited copies: duplicate environment keys have platform-dependent
  -- precedence, so the configured Cabal flags must be the only values supplied.
  inherited <- filter ((`notElem` map fst newVars) . fst) <$> getEnvironment
  let environment = newVars <> inherited
  dir <- makeAbsolute autogenDir
  callCreateProcess (proc "bash" ["src/comp/update-build-version.sh", dir]) {env = Just environment}

-- | The configure hook bootstraps native libraries because Cabal checks
-- foreign-library availability during configuration. The main library's demanded
-- Warmup rule also tracks native inputs and refreshes them before compilation.
-- Explicit -j1 keeps the recursive native Makefiles serial inside a parallel
-- project build. Independent builds sharing a vendor tree are not covered.
type NativeBuild = (FilePath, Bool, Bool)

nativeBuild :: ConfigFlags -> FlagAssignment -> NativeBuild
nativeBuild config flags =
  (getSymbolicPath (fromFlagOrDefault (makeSymbolicPath "dist") (configDistPref config))
     </> "solver-prefix",
   flagSet flags "stp-stub", flagSet flags "yices-stub")

nativeBuildFor :: LocalBuildInfo -> NativeBuild
nativeBuildFor lbi = nativeBuild (LBI.configFlags lbi) (LBI.flagAssignment lbi)

buildNative :: NativeBuild -> IO ()
buildNative (scratch, stpStub, yicesStub) = do
  prefix <- makeAbsolute scratch
  forM_ (["stp", "yices"] :: [String]) $ \solver ->
    callProcess "make"
      ["-j1", "-C", "src" </> "vendor" </> solver, "install", "PREFIX=" <> prefix,
       "STP_STUB=" <> if stpStub then "1" else "",
       "YICES_STUB=" <> if yicesStub then "1" else ""]

nativeDependencies :: LocalBuildInfo -> IO [Dependency]
nativeDependencies lbi = do
  let pd = LBI.localPkgDescr lbi
      wanted path = path == "platform.mk" || path == "platform.sh"
                  || "src/vendor/stp/" `isPrefixOf` path
                  || "src/vendor/yices/" `isPrefixOf` path
      patterns = filter (wanted . getSymbolicPath) (extraSrcFiles pd)
  files <- concat <$> mapM (matchDirFileGlob normal (specVersion pd) (mbWorkDirLBI lbi)) patterns
  pure [FileDependency (Location (makeSymbolicPath ".") path) | path <- sort (nub files)]

solverSetupHooks :: SetupHooks
solverSetupHooks = noSetupHooks {configureHooks}
  where
    configureHooks = noConfigureHooks {preConfComponentHook}
    preConfComponentHook :: Maybe PreConfComponentHook
    preConfComponentHook = Just $ \inputs ->
      if isMainLib inputs.component
        then do
          let pd = inputs.packageBuildDescr
          buildNative (nativeBuild (LBC.configFlags pd) (LBC.flagAssignment pd))
          dirs <- mapM (canonicalizePath . ("src" </>) . ("vendor" </>)) ["stp/lib", "yices/lib"]
          pure $ PreConfComponentOutputs
            {componentDiff = buildInfoComponentDiff (componentName inputs.component)
              (emptyBuildInfo
                {extraLibs = ["stp", "yices"],
                 extraLibDirs = map makeSymbolicPath dirs,
                 ldOptions = map ("-Wl,-rpath," <>) dirs})}
        else pure $ noPreConfComponentOutputs inputs

-- | Tcl include/link flags belong to the compiler library and propagate to tools.
tclSetupHooks :: SetupHooks
tclSetupHooks = noSetupHooks {configureHooks}
  where
    configureHooks = noConfigureHooks {preConfComponentHook}

    preConfComponentHook :: Maybe PreConfComponentHook
    preConfComponentHook = Just $ \inputs -> do
      let platform arg = readProcess "sh" [repoRoot </> "platform.sh", arg] ""
      let trim = f . f where f = reverse . dropWhile isSpace
      let getArgs flag = fmap (drop (length flag)) . filter (flag `isPrefixOf`)
      if isMainLib inputs.component
        then do
          tclInc <- words <$> platform "tclinc"
          tclLibs <- words <$> platform "tcllibs"
          tclVersion <- trim <$> platform "tclversion"

          cflags <- case tclVersion of
            "8.5" -> pure ["-DTCL85"]
            "8.6" -> pure []
            "9.0" -> pure ["-DTCL9"]
            _ -> ioError (userError ("unsupported Tcl version: " <> tclVersion))
          let includeDirs = makeSymbolicPath <$> getArgs "-I" tclInc
              extraLibDirs = makeSymbolicPath <$> getArgs "-L" tclLibs
              extraLibs = getArgs "-l" tclLibs

          pure $
            PreConfComponentOutputs
              { componentDiff =
                  buildInfoComponentDiff
                    (componentName inputs.component)
                    ( emptyBuildInfo
                        { includeDirs,
                          extraLibDirs,
                          extraLibs,
                          ccOptions = cflags,
                          cppOptions = cflags
                        }
                    )
              }
        else pure $ noPreConfComponentOutputs inputs
