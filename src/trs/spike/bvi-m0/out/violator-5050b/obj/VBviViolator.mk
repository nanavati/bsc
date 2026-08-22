# Verilated -*- Makefile -*-
# DESCRIPTION: Verilator output: Makefile for building Verilated archive or executable
#
# Execute this makefile from the object directory:
#    make -f VBviViolator.mk

default: libVBviViolator

### Constants...
# Perl executable (from $PERL, defaults to 'perl' if not set)
PERL = perl
# Python3 executable (from $PYTHON3, defaults to 'python3' if not set)
PYTHON3 = python3
# Path to Verilator kit (from $VERILATOR_ROOT)
VERILATOR_ROOT = /tmp/claude-0/-home-user/f82246ec-2b03-5c15-8a6d-2b96b45b9d69/scratchpad/verilator-new
# SystemC include directory with systemc.h (from $SYSTEMC_INCLUDE)
SYSTEMC_INCLUDE ?=
# SystemC library directory with libsystemc.a (from $SYSTEMC_LIBDIR)
SYSTEMC_LIBDIR ?=

### Switches...
# C++ code coverage  0/1 (from --prof-c)
VM_PROFC = 0
# SystemC output mode?  0/1 (from --sc)
VM_SC = 0
# Legacy or SystemC output mode?  0/1 (from --sc)
VM_SP_OR_SC = $(VM_SC)
# Deprecated
VM_PCLI = 1
# Deprecated: SystemC architecture to find link library path (from $SYSTEMC_ARCH)
VM_SC_TARGET_ARCH = linux

### Vars...
# Design prefix (from --prefix)
VM_PREFIX = VBviViolator
# Module prefix (from --prefix)
VM_MODPREFIX = VBviViolator
# User CFLAGS (from -CFLAGS on Verilator command line)
VM_USER_CFLAGS = \
  -DVL_USER_FATAL -DVL_PRINTF=trs_vlt_printf -include /home/user/bsc-matx/src/trs/spike/bvi-m0/trs_printf_decl.h -fPIC \

# User LDLIBS (from -LDFLAGS on Verilator command line)
VM_USER_LDLIBS = \

# User .cpp files (from .cpp's on Verilator command line)
VM_USER_CLASSES = \

# User .cpp directories (from .cpp's on Verilator command line)
VM_USER_DIR = \
  ../../.. \

### Default rules...
# Include list of all generated classes
include VBviViolator_classes.mk
# Include global rules
include $(VERILATOR_ROOT)/include/verilated.mk

### Library rules (default lib mode)
libVBviViolator.a: $(VK_OBJS) $(VK_USER_OBJS) $(VM_HIER_LIBS)
libverilated.a: $(VK_GLOBAL_OBJS)
libVBviViolator: libVBviViolator.a libverilated.a $(VM_PREFIX)__ALL.a
# Verilated -*- Makefile -*-
