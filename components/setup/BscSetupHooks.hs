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
-- component libraries, tools and test runners. The binding packages own
-- native solver setup, and the Tcl binding owns its C compilation flags.
module BscSetupHooks (bscSetupHooks) where

import Control.Monad (filterM, forM, forM_, unless, when)
import Control.Monad.IO.Class (liftIO)
import Data.Char (isSpace)
import Data.List (isPrefixOf, nub, sort, sortOn)
import Data.Maybe (fromMaybe)
import Distribution.Compiler (CompilerFlavor (..), PerCompilerFlavor (..))
import Distribution.InstalledPackageInfo (ExposedModule (..))
import qualified Distribution.InstalledPackageInfo as IPI
import Distribution.ModuleName (ModuleName)
import Distribution.Package (mkPackageName, pkgName)
import Distribution.PackageDescription (PackageDescription, otherModules)
import Distribution.Pretty (prettyShow)
import Distribution.Simple.Compiler (PackageDBX (..), compilerFlavor, compilerVersion)
import Distribution.Simple.Configure (getInstalledPackages)
import Distribution.Simple.Glob (matchDirFileGlob)
import qualified Distribution.Simple.GHC as GHC
import Distribution.Simple.Program.Db (emptyProgramDb, updateProgram)
import qualified Distribution.Simple.Program.HcPkg as HcPkg
import Distribution.Simple.Program.Run (runProgramInvocation)
import Distribution.Simple.Program.Types (ConfiguredProgram)
import Distribution.Simple.LocalBuildInfo
  ( hostPlatform,
    localPkgDescr,
    interpretSymbolicPathLBI,
    mbWorkDirLBI,
    withPackageDB,
    withPrograms,
  )
import qualified Distribution.Simple.LocalBuildInfo as LBI
import Distribution.Simple.PackageIndex (InstalledPackageIndex, lookupUnitId)
import Distribution.Simple.Setup (flagToMaybe, fromFlagOrDefault)
import Distribution.Simple.SetupHooks
import Distribution.Simple.Utils (die')
import Distribution.System (OS (..))
import qualified Distribution.Types.Component as Component
import qualified Distribution.Types.LocalBuildConfig as LBC
import Distribution.Types.UnitId (UnitId)
import Distribution.Types.Flag (FlagAssignment, lookupFlagAssignment, mkFlagName)
import Distribution.Utils.Path
  ( makeSymbolicPath,
    makeRelativePathEx,
    moduleNameSymbolicPath,
    getSymbolicPath,
    interpretSymbolicPath,
    (<.>),
  )
import Distribution.Verbosity (normal)
import Distribution.Version (mkVersion)
import System.Directory
  ( canonicalizePath,
    createDirectoryIfMissing,
    doesFileExist,
    doesDirectoryExist,
    removeDirectoryRecursive,
    findExecutable,
    makeAbsolute,
  )
import System.Environment (getEnvironment)
import System.Exit (ExitCode (..))
import System.FilePath (isAbsolute, takeDirectory, takeFileName, (</>))
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

bscSetupHooks :: SetupHooks
bscSetupHooks =
  compilerSetupHooks
    <> warmupSetupHooks
    <> generatedModulesSetupHooks
    <> solverSetupHooks
    <> tclSetupHooks

repoRoot :: FilePath
repoRoot = ".." </> ".."

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

-- | Generate the barrier only for components that declare the local module.
-- A library consisting entirely of reexports has no Haskell compilation roots
-- and does not demand a Warmup rule.
wantsWarmup :: Component -> Bool
wantsWarmup component =
  case component of
    CLib lib -> hidden || "Warmup" `elem` exposedModules lib
    CExe {} -> hidden
    CTest {} -> hidden
    CBench {} -> hidden
    _ -> False
  where
    hidden = "Warmup" `elem` otherModules (Component.componentBuildInfo component)

-- | Import all modules of direct dependencies in a stable order before the
-- component's roots compile. This stabilizes GHC's external rule/instance
-- visibility under --make -j; -fobject-determinism separately stabilizes uniques.
-- Resolve exact dependency unit IDs against the CURRENT package databases at
-- build time, since in-place dependencies can change exports without changing ID.
warmupSetupHooks :: SetupHooks
warmupSetupHooks = noSetupHooks {configureHooks, buildHooks}
  where
    configureHooks = noConfigureHooks {preConfComponentHook}
    preConfComponentHook :: Maybe PreConfComponentHook
    preConfComponentHook = Just $ \inputs -> do
      let component = inputs.component
      if wantsWarmup component
        then do
          db <- privatePackageDbPath inputs.packageBuildDescr.configFlags
                  (componentName component)
          let packageView = PerCompilerFlavor
                ["-clear-package-db", "-package-db", db] []
          pure $ (noPreConfComponentOutputs inputs)
            {componentDiff = buildInfoComponentDiff (componentName component)
              (mempty {options = packageView,
                -- Cabal's separate linkLibrary path uses hcStaticOptions,
                -- including for shared/profiling shared libraries; it does
                -- not include the ordinary options used during compilation.
                staticOptions = packageView})}
        else pure (noPreConfComponentOutputs inputs)

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
        closure <- liftIO $ either (die' verbosity) pure $
          canonicalDependencyClosure index (componentUnitId clbi)
            (map IPI.installedUnitId direct)
        db <- liftIO $ privatePackageDbPath (LBI.configFlags lbi)
                (componentName (targetComponent env.targetInfo))
        let privateDb = (db, HcPkg.hcPkgProgram (GHC.hcPkgInfo (withPrograms lbi)), closure)
            cache = Location (makeSymbolicPath db) (makeRelativePathEx "package.cache")
            units = sort [prettyShow (IPI.installedUnitId ipi) | ipi <- direct]
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
                       then nativeBuildFor lbi else Nothing
        nativeDeps <- case native of
          Nothing -> pure []
          Just _ -> liftIO $ nativeDependencies lbi
        registerRule_ "Warmup.hs" $
          staticRule
            ( mkCommand
                (static Dict)
                (static writeWarmupHs)
                (locationFilePath lbi warmup, units, mods, native, privateDb)
            )
            nativeDeps
            [warmup, cache]

-- Cabal's dist prefix already separates package configurations. The component
-- name further separates tools and test suites that share that prefix. Resolve
-- working-dir here in both configure and build, so external builddirs and repl
-- use the exact same absolute path.
privatePackageDbPath :: ConfigFlags -> ComponentName -> IO FilePath
privatePackageDbPath config name = makeAbsolute $
  interpretSymbolicPath (flagToMaybe (configWorkingDir config))
    (fromFlagOrDefault (makeSymbolicPath "dist") (configDistPref config))
    </> "package-views" </> map safe (prettyShow name)
  where
    safe ':' = '-'
    safe c = c

-- Only dependencies of this component belong in its view. Choosing the first
-- ready unit in lexical order gives a deterministic dependency-first order,
-- independent of package registration and index traversal order. Include the
-- compiler's global units (notably rts), but never this component's old entry.
canonicalDependencyClosure
  :: InstalledPackageIndex -> UnitId -> [UnitId]
  -> Either String [IPI.InstalledPackageInfo]
canonicalDependencyClosure index self roots = do
  closure <- gather [] roots
  order [] (sortOn (prettyShow . IPI.installedUnitId) closure)
  where
    gather done [] = Right done
    gather done (unit : rest)
      | unit == self = Left ("Warmup: dependency cycle through " <> prettyShow unit)
      | unit `elem` map IPI.installedUnitId done = gather done rest
      | otherwise = case lookupUnitId index unit of
          Nothing -> Left ("Warmup: missing transitive dependency " <> prettyShow unit)
          Just ipi -> gather (ipi : done) (IPI.depends ipi <> rest)
    order done [] = Right (reverse done)
    order done pending =
      case break (all (`elem` map IPI.installedUnitId done) . IPI.depends) pending of
        (_, []) -> Left ("Warmup: cyclic package dependencies: " <>
                         unwords (map (prettyShow . IPI.installedUnitId) pending))
        (before, next : after) -> order (next : done) (before <> after)

-- Expanded IPI records are rule arguments, so changes to dependency metadata
-- invalidate the view even when unit IDs are unchanged. HcPkg.register itself
-- may recache via directory enumeration for multi-instance registration; call
-- its public invocation builder directly to retain the explicit ordering.
type PrivatePackageDb = (FilePath, ConfiguredProgram, [IPI.InstalledPackageInfo])

writePrivatePackageDb :: PrivatePackageDb -> IO ()
writePrivatePackageDb (db, program, packages) = do
  let hpi = GHC.hcPkgInfo (updateProgram program emptyProgramDb)
      stack = [GlobalPackageDB, SpecificPackageDB (makeSymbolicPath db)]
      options = HcPkg.defaultRegisterOptions {HcPkg.registerMultiInstance = True}
  exists <- doesDirectoryExist db
  when exists (removeDirectoryRecursive db)
  createDirectoryIfMissing True (takeDirectory db)
  HcPkg.init hpi normal False db
  forM_ packages $ \ipi ->
    runProgramInvocation normal $
      HcPkg.registerInvocation hpi normal Nothing stack ipi options

writeWarmupHs :: (FilePath, [String], [String], Maybe NativeBuild, PrivatePackageDb) -> IO ()
writeWarmupHs (path, units, mods, native, privateDb) = do
  forM_ native buildNative
  writePrivatePackageDb privateDb
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

-- | Platform facts belong to the shared library; Git provenance is driver-only.
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
          owner = pkgName (package (localPkgDescr lbi))
          mainLibrary = isMainLib (targetComponent env.targetInfo)
      when (owner == mkPackageName "bsc-common" && mainLibrary) $ do
        registerRule_ "BuildSystem.hs" $
          staticRule
            ( mkCommand
                (static Dict)
                (static writeBuildSystemHs)
                (locationFilePath lbi buildSystem, hostPlatform lbi)
            )
            []
            [buildSystem]
      when (owner == mkPackageName "bsc-driver" && mainLibrary) $ do
        context <- liftIO (buildVersionContext lbi)
        gitDeps <- liftIO (gitDependencies lbi)
        registerRule_ "BuildVersion.hs" $
          staticRule
            ( mkCommand
                (static Dict)
                (static writeBuildVersionHs)
                (interpretSymbolicPathLBI lbi (autogenComponentModulesDir lbi clbi), context)
            )
            (FileDependency (Location (makeSymbolicPath ".")
              (makeRelativePathEx (repoRoot </> "src/comp/update-build-version.sh"))) : gitDeps)
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
      (_, commit, _) <- readProcessWithExitCode exe ["-C", repoRoot, "rev-parse", "HEAD"] ""
      (_, describe, _) <- readProcessWithExitCode exe ["-C", repoRoot, "describe", "--tags"] ""
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
          (_, branch, _) <- readProcessWithExitCode exe ["-C", repoRoot, "symbolic-ref", "-q", "HEAD"] ""
          let trim = reverse . dropWhile isSpace . reverse
              names = ["HEAD", "packed-refs"] <> [trim branch | not (null branch)]
          paths <- forM names $ \name -> do
            (code, path, _) <- readProcessWithExitCode exe ["-C", repoRoot, "rev-parse", "--git-path", name] ""
            pure [if isAbsolute (trim path) then trim path else repoRoot </> trim path
                 | code == ExitSuccess && not (null path)]
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
  script <- makeAbsolute (repoRoot </> "src/comp/update-build-version.sh")
  callCreateProcess (proc "bash" [script, dir]) {cwd = Just repoRoot, env = Just environment}

-- | Each binding configures its own native library. Its demanded Warmup rule
-- also tracks native inputs and refreshes them before Haskell compilation.
-- Explicit -j1 keeps a recursive native Make invocation serial inside the
-- parallel project build; separate builds sharing a vendor tree are not covered.
type NativeBuild = (FilePath, String, Bool)

bindingSolver :: PackageDescription -> Maybe String
bindingSolver pd = lookup (pkgName (package pd))
  [(mkPackageName "bsc-stp", "stp"), (mkPackageName "bsc-yices", "yices")]

nativeBuild :: ConfigFlags -> FlagAssignment -> String -> NativeBuild
nativeBuild config flags solver =
  (getSymbolicPath (fromFlagOrDefault (makeSymbolicPath "dist") (configDistPref config))
     </> "solver-prefix",
   solver, flagSet flags (solver <> "-stub"))

nativeBuildFor :: LocalBuildInfo -> Maybe NativeBuild
nativeBuildFor lbi = nativeBuild (LBI.configFlags lbi) (LBI.flagAssignment lbi)
                    <$> bindingSolver (LBI.localPkgDescr lbi)

buildNative :: NativeBuild -> IO ()
buildNative (scratch, solver, stub) = do
  prefix <- makeAbsolute scratch
  let variable = if solver == "stp" then "STP_STUB=" else "YICES_STUB="
  callProcess "make"
    ["-j1", "-C", repoRoot </> "src" </> "vendor" </> solver,
     "install", "PREFIX=" <> prefix, variable <> if stub then "1" else ""]

nativeDependencies :: LocalBuildInfo -> IO [Dependency]
nativeDependencies lbi = do
  let pd = LBI.localPkgDescr lbi
      patterns = extraSrcFiles pd
  files <- concat <$> mapM (matchDirFileGlob normal (specVersion pd) (mbWorkDirLBI lbi)) patterns
  pure [FileDependency (Location (makeSymbolicPath ".") path) | path <- sort (nub files)]

solverSetupHooks :: SetupHooks
solverSetupHooks = noSetupHooks {configureHooks}
  where
    configureHooks = noConfigureHooks {preConfComponentHook}
    preConfComponentHook :: Maybe PreConfComponentHook
    preConfComponentHook = Just $ \inputs ->
      let pd = inputs.packageBuildDescr
      in case bindingSolver (LBC.localPkgDescr pd) of
        Just solver | isMainLib inputs.component -> do
          buildNative (nativeBuild (LBC.configFlags pd) (LBC.flagAssignment pd) solver)
          dir <- canonicalizePath (repoRoot </> "src" </> "vendor" </> solver </> "lib")
          pure $ PreConfComponentOutputs
            {componentDiff = buildInfoComponentDiff (componentName inputs.component)
              (emptyBuildInfo
                {extraLibs = [solver],
                 extraLibDirs = [makeSymbolicPath dir],
                 ldOptions = ["-Wl,-rpath," <> dir]})}
        _ -> pure $ noPreConfComponentOutputs inputs

-- | Tcl include/link flags belong to its independent binding package.
tclSetupHooks :: SetupHooks
tclSetupHooks = noSetupHooks {configureHooks}
  where
    configureHooks = noConfigureHooks {preConfComponentHook}

    preConfComponentHook :: Maybe PreConfComponentHook
    preConfComponentHook = Just $ \inputs -> do
      let platform arg = readProcess "sh" [repoRoot </> "platform.sh", arg] ""
      let trim = f . f where f = reverse . dropWhile isSpace
      let getArgs flag = fmap (drop (length flag)) . filter (flag `isPrefixOf`)
      if pkgName (package (LBC.localPkgDescr inputs.packageBuildDescr)) == mkPackageName "htcl"
          && isMainLib inputs.component
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
