# Cabal owns Haskell compilation and dependency scheduling.  This adapter
# preserves the existing installation layout for the runtime Makefiles.
TOP := $(abspath ../..)
PREFIX ?= $(TOP)/inst
BINDIR := $(PREFIX)/bin
LICDIR := $(PREFIX)/LICENSES
CABAL ?= cabal
CABAL_BUILDDIR ?= $(TOP)/dist-newstyle
CABAL_FLAGS ?=
CABAL_BUILD_FLAGS = $(CABAL_FLAGS)
INSTALL ?= install

NOGIT ?= 0
NOUPDATEBUILDVERSION ?= 0
export NOGIT NOUPDATEBUILDVERSION

# Build-affecting environment aliases become tracked Cabal configuration.
ifeq ($(NOGIT),1)
CABAL_BUILD_FLAGS += --flags=no-git
else
CABAL_BUILD_FLAGS += --flags=-no-git
endif
ifeq ($(NOUPDATEBUILDVERSION),1)
CABAL_BUILD_FLAGS += --flags=no-update-build-version
else
CABAL_BUILD_FLAGS += --flags=-no-update-build-version
endif
ifneq ($(STP_STUB),)
CABAL_BUILD_FLAGS += --flags=stp-stub
else
CABAL_BUILD_FLAGS += --flags=-stp-stub
endif
ifneq ($(YICES_STUB),)
CABAL_BUILD_FLAGS += --flags=yices-stub
else
CABAL_BUILD_FLAGS += --flags=-yices-stub
endif

ifneq ($(GHC),)
CABAL_BUILD_FLAGS += --with-compiler=$(GHC)
endif

# One Cabal invocation schedules every compiler component.  GHCJOBS remains
# an optional compatibility spelling for the Cabal/GHC shared job limit.
ifneq ($(GHCJOBS),)
CABAL_BUILD_FLAGS += -j$(GHCJOBS) --ghc-options=-j$(GHCJOBS)
endif
ifneq ($(GHCRTSFLAGS),)
CABAL_BUILD_FLAGS += --ghc-options='$(GHCRTSFLAGS)'
endif
ifeq ($(BSC_BUILD),NOOPT)
CABAL_BUILD_FLAGS += --disable-optimization
endif
ifeq ($(BSC_BUILD),DEBUG)
CABAL_BUILD_FLAGS += --ghc-options="-dcore-lint -debug"
endif
ifeq ($(BSC_BUILD),PROF)
CABAL_BUILD_FLAGS += --enable-profiling --enable-library-profiling --ghc-options='-fprof-auto "-with-rtsopts=-H256m -K256m -i1"'
endif

BSCEXES := bsc
TCLEXES := bluetcl
UTILEXES := bsc2bsv bsv2bsc dumpbo dumpba vcdcheck
SHOWRULESEXES := showrules
EXES := $(BSCEXES) $(TCLEXES) $(UTILEXES) $(SHOWRULESEXES)

.PHONY: all cabal-build $(EXES)
all: cabal-build
$(EXES): cabal-build
cabal-build:
	cd "$(TOP)" && $(CABAL) build all --builddir="$(CABAL_BUILDDIR)" $(CABAL_BUILD_FLAGS)

.PHONY: install install-extra install-bsc install-bluetcl install-utils install-showrules
install: install-bsc install-bluetcl
install-extra: install-utils install-showrules
install-bsc: TOOLS = $(BSCEXES)
install-bluetcl: TOOLS = $(TCLEXES)
install-utils: TOOLS = $(UTILEXES)
install-showrules: TOOLS = $(SHOWRULESEXES)
install-bsc install-bluetcl install-utils install-showrules: cabal-build
	$(INSTALL) -d -m 755 "$(BINDIR)" "$(BINDIR)/core"
	@set -e; cd "$(TOP)"; for tool in $(TOOLS); do \
	    binary=$$($(CABAL) list-bin "bsc:exe:$$tool" --builddir="$(CABAL_BUILDDIR)" $(CABAL_BUILD_FLAGS)); \
	    $(INSTALL) -m 755 "$$binary" "$(BINDIR)/core/$$tool"; \
	    $(INSTALL) -m 755 src/comp/wrapper.sh "$(BINDIR)/$$tool"; \
	done

ifneq ($(BSC_BUILD_PKGINFO),)
PACKAGES := base containers array mtl unix regex-compat bytestring directory process filepath time old-time old-locale split syb integer-gmp text deepseq strict-concurrency
.PHONY: package-licenses
install install-extra install-bsc install-bluetcl install-utils install-showrules: package-licenses
package-licenses: cabal-build
	$(INSTALL) -d -m 755 "$(LICDIR)"
	cd "$(TOP)" && $(CABAL) exec --builddir="$(CABAL_BUILDDIR)" -- "$(TOP)/src/comp/make-ghc-pkg-info.sh" $(PACKAGES) > "$(LICDIR)/LICENSE.ghc_pkgs"
endif

.PHONY: clean full_clean
clean:
	cd "$(TOP)" && $(CABAL) clean --builddir="$(CABAL_BUILDDIR)"
full_clean: clean
	rm -f BuildSystem.hs BuildVersion.hs Warmup.hs tags TAGS
