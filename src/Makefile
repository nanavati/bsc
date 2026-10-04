PWD := $(shell pwd)
TOP := $(PWD)/..

include $(TOP)/platform.mk

PREFIX?=$(TOP)/inst

ifndef NO_DEPS_CHECKS
CC_TOOLS=$(CC) $(CXX) $(LD)
BSC_TOOLS=ghc ghc-pkg cabal
YICES_TOOLS=gperf autoconf
STP_TOOLS=flex bison

TOOLS=$(CC_TOOLS) \
      $(BSC_TOOLS) \
      $(YICES_TOOLS) \
      $(STP_TOOLS) \


SUBMODS=vendor/yices/v2.6/yices2

# Check all the necessary build tools are present
pathsearch=$(firstword $(wildcard $(addsuffix /$(1),$(subst :, ,$(PATH)))))
checktool=$(if $(call pathsearch,$(1)),,$(error Tool $(1) could not be found))
$(foreach tool,$(TOOLS),$(call checktool,$(tool)))

# Cabal resolves Haskell package dependencies in its own package database.

# Check all submodules are initialized
submodexists=$(shell git submodule status $(1) 2> /dev/null )
in_git_repo:=$(foreach submod,$(SUBMODS),$(call submodexists,$(submod)))
ifneq ($(in_git_repo),)
define SUBMOD_MSG
Submodule $(1) missing. Initialize with
    git submodule update --init --recursive
endef
checksubmod=$(if $(wildcard $(1)/.git),,$(error $(SUBMOD_MSG)))
else
define SUBMOD_MSG
Submodule $(1) missing.
    This archive was exported from Git without the source files for
    submodules. You will need to acquire those files or, preferably,
    build instead from a clone of the BSC Git repository
endef
checksubmod=$(if $(wildcard $(1)/*),,$(error $(SUBMOD_MSG)))
endif
$(foreach submod,$(SUBMODS),$(call checksubmod,$(submod)))
endif # NO_DEPS_CHECKS

.PHONY: all
all: install

# Keep native/runtime submakes serial even if the caller supplied -j.
.PHONY: install clean full_clean
install clean full_clean:
	$(MAKE) -j1 -C vendor/stp   PREFIX=$(PREFIX)  $@
	$(MAKE) -j1 -C vendor/yices PREFIX=$(PREFIX)  $@
	$(MAKE) -j1 -C vendor/htcl  PREFIX=$(PREFIX)  $@
	# Cabal owns compiler parallelism; the standard libraries need its installed tools.
	$(MAKE) -j1 -C comp   PREFIX=$(PREFIX)  $@
	$(MAKE) -j1 -C Libraries  PREFIX=$(PREFIX)  $@
	$(MAKE) -j1 -C exec       PREFIX=$(PREFIX)  $@
	$(MAKE) -j1 -C VPI        PREFIX=$(PREFIX)  $@
	$(MAKE) -j1 -C Verilog    PREFIX=$(PREFIX)  $@
	$(MAKE) -j1 -C Verilog.Quartus  PREFIX=$(PREFIX)  $@
	$(MAKE) -j1 -C Verilog.Vivado   PREFIX=$(PREFIX)  $@
	$(MAKE) -j1 -C bluetcl    PREFIX=$(PREFIX)  $@
	$(MAKE) -j1 -C bluesim    PREFIX=$(PREFIX)  $@
	$(MAKE) -j1 -C Verilator  PREFIX=$(PREFIX)  $@

