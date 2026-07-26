PWD:=$(shell pwd)
TOP:=$(PWD)/../..

# Common defines use by Makefiles here and in subdirectories
# Requires that TOP be set
include common.mk

DIRS = \
	Base1 \
	Base2 \
	Base3-Contexts \
	Base3-Math \
	Base3-Misc \

# Build order for the libraries
BUILD_ORDER= \
	Base1 \
	Base2 \
	Base3-Misc \
	Base3-Contexts \
	Base3-Math \

# Find files to build tags
SRCS = $(shell find . -name "*.bsv")

BLOOGLEDIR = $(LIBDIR)/bloogle

.PHONY: all build tconcheck install clean full_clean bloogle

all: install TAGS

build:
	$(foreach dir, $(BUILD_ORDER), $(MAKE) -C $(dir) $@ &&) true

bloogle: build
	install -d $(BLOOGLEDIR)
	$(BO2BLOOGLE) bluespec $(BUILDDIR)/*.bo > $(BLOOGLEDIR)/bluespec.txt

# Check that the compiler's handwritten tycon constants agree with the
# just-built Prelude (see src/comp/tconcheck.hs); drift fails the build
TCONCHECK ?= $(BINDIR)/tconcheck

# Run it in BOTH type-sharing configurations rather than whichever is
# currently the default.  The two disagreed: construction-time consing
# keys a leaf on (qualifier, base, kind, sort tag) and not on the sort
# PAYLOAD, so two spellings of one payload -- a .bo carrying a type's
# constructors as the source package wrote them, and the re-qualified
# form MakeSymTab produces -- collapsed onto whichever reached the table
# first, and 8 of the 94 entries drifted under -share-types while all 94
# passed without it.  Checking only the default configuration is what let
# that ship: the fleet runs -share-types and this check did not.
tconcheck: build
	$(TCONCHECK) $(BUILDDIR)
	BSC_OPTIONS=-share-types $(TCONCHECK) $(BUILDDIR)

install: build bloogle tconcheck
	install -d $(INSTALLDIR)
	install -m644 $(BUILDDIR)/* $(INSTALLDIR)

TAGS: $(SRCS)
	$(TOP)/util/scripts/btags $+

clean full_clean:
	$(foreach dir, $(DIRS), $(MAKE) -C $(dir) $@;)
	@rm -f *~ TAGS

