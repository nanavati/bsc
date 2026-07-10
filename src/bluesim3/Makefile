PWD:=$(shell pwd)
TOP:=$(PWD)/../..

INSTALL ?= install

PREFIX?=$(TOP)/inst
BINDIR=$(PREFIX)/bin

CARGO ?= cargo

.PHONY: all
all: install

# The bsim3 executable is a self-contained Rust binary (the interpreter
# needs no BLUESPECDIR or LD_LIBRARY_PATH), so it is installed directly
# in "bin" with no wrapper script.  libbsim3_capi.a (the bk_* C API for
# `bsim3 link --interactive` models) installs beside it — the linker
# searches next to its own binary.
#
# The hybrid JIT needs llvm-sys (LLVM 18 dev headers): when the
# environment provides LLVM_SYS_181_PREFIX, build the full product;
# otherwise the lean interpreter-only fallback (no LLVM required).
ifdef LLVM_SYS_181_PREFIX
BSIM3_FLAGS = --features jit
CAPI_FLAGS  =
else
BSIM3_FLAGS =
CAPI_FLAGS  = --no-default-features
endif

.PHONY: build
build:
	$(CARGO) build --release --locked -p bsim3 $(BSIM3_FLAGS)
	$(CARGO) build --release --locked -p bsim3-capi $(CAPI_FLAGS)

.PHONY: install
install: build
	$(INSTALL) -m 755 -d $(BINDIR)
	$(INSTALL) -m 755 target/release/bsim3 $(BINDIR)/bsim3
	$(INSTALL) -m 644 target/release/libbsim3_capi.a $(BINDIR)/libbsim3_capi.a

.PHONY: clean full_clean
clean full_clean:
	$(CARGO) clean
