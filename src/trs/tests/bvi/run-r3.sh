#!/bin/sh
# BVI R3 gate battery: the trs link verilate-or-cache pipeline.
#   - counter contract verilates end-to-end into a dlopen-checked .so
#   - cache hit on re-invocation; content invalidation via the depfile
#     manifest; per-class lock survives concurrent builds
#   - delay constructs select the timing link mode (the build always
#     verilates --timing; VM_TIMING in the products says whether the
#     model uses it) and still build end-to-end
#   - refusals: DPI (the __Dpi.h backstop), contract/model mismatch,
#     unresolvable source
#   - the verilator FLOOR is a --timing capability check (any 5.x): the
#     stable-interface metadata (V<top>.h port macros + classes.mk)
#     works across releases, proven by the system-verilator positive
#     legs below; a pre-5.0 binary produces the clear floor error
#     (negative leg, skipped when no such binary exists)
# REQUIRES a pinned Verilator (the plan of record): set TRS_VERILATOR
# (and VERILATOR_ROOT for a source build), or have one on PATH as
# `verilator`.  Optional: TRS_VERILATOR_SYS=/path/to/other/5.x adds the
# cross-release positive legs (defaults to /usr/bin/verilator when
# present); TRS_VERILATOR_OLD=/path/to/pre-5.0/verilator adds the
# floor-refusal negative.
# BSC=/path/bsc TRS=/path/trs sh run-r3.sh [workdir]
BSC=${BSC:-bsc}
TRS=${TRS:-trs}
SRC=$(cd "$(dirname "$0")" && pwd)
RTL=$(cd "$SRC/../../spike/bvi-m0/rtl" && pwd)
case "$BSC" in
    */*) PATH="$(cd "$(dirname "$BSC")" && pwd):$PATH"; export PATH;;
esac
case "$TRS" in
    */*) TRS=$(cd "$(dirname "$TRS")" && pwd)/$(basename "$TRS");;
esac
# the pin applies to every build in this battery (bsc -trs link included)
[ -n "$TRS_VERILATOR" ] && export TRS_VERILATOR
[ -n "$VERILATOR_ROOT" ] && export VERILATOR_ROOT
WK=${1:-$(mktemp -d)}
mkdir -p "$WK"
WK=$(cd "$WK" && pwd)
cd "$WK" || exit 2
fail=0
ok()   { echo "PASS $1"; }
bad()  { echo "FAIL $1"; shift; [ $# -gt 0 ] && printf '%s\n' "$@" | head -5; fail=1; }

# ---- produce the counter .bir (R2 export)
cp "$SRC/PosCounter.bsv" .
$BSC -sim -u -g sysPosCounter PosCounter.bsv >bsc.out 2>&1 || {
    bad "setup (bsc compile)" "$(cat bsc.out)"; exit 1; }
$BSC -sim -trs -e sysPosCounter >link0.out 2>&1
[ -f sysPosCounter.bir ] || { bad "setup (no .bir)"; exit 1; }

C=$WK/cache

# ---- positive build + dlopen check (fails with the floor message if
# the pinned verilator is missing or too old -- that IS the check)
if out=$(TRS_VLT_CACHE=$C "$TRS" vlt build sysPosCounter.bir --vpath "$RTL" 2>&1) \
   && echo "$out" | grep -q "built, contract"; then ok build
else bad build "$out"; fi

# ---- cache hit
if out=$(TRS_VLT_CACHE=$C "$TRS" vlt build sysPosCounter.bir --vpath "$RTL" 2>&1) \
   && echo "$out" | grep -q "cached, contract"; then ok cache-hit
else bad cache-hit "$out"; fi

# ---- content invalidation (same paths, changed source content)
mkdir -p rtl-mod && cp "$RTL/BviCounter.v" rtl-mod/
TRS_VLT_CACHE=$C "$TRS" vlt build sysPosCounter.bir --vpath "$WK/rtl-mod" >/dev/null 2>&1
printf '\n// touched\n' >> rtl-mod/BviCounter.v
if out=$(TRS_VLT_CACHE=$C "$TRS" vlt build sysPosCounter.bir --vpath "$WK/rtl-mod" 2>&1) \
   && echo "$out" | grep -q "built, contract"; then ok invalidate
else bad invalidate "$out"; fi

# ---- refusals
mkdir -p rtl-delay rtl-dpi rtl-mismatch
sed 's/c <= c + bump_amt/c <= #1 c + bump_amt/' "$RTL/BviCounter.v" > rtl-delay/BviCounter.v
awk '/^module BviCounter/{print; print "  import \"DPI-C\" function int add_one(input int x);"; next} {print}' \
    "$RTL/BviCounter.v" > rtl-dpi/BviCounter.v
sed 's/bump_amt/bump_widened/g' "$RTL/BviCounter.v" > rtl-mismatch/BviCounter.v

refusal() { # name vpath tag
    if out=$(TRS_VLT_CACHE=$C "$TRS" vlt build sysPosCounter.bir --vpath "$2" 2>&1); then
        bad "$1 (unexpectedly succeeded)" "$out"
    elif echo "$out" | grep -q "$3"; then ok "$1"
    else bad "$1 (missing tag $3)" "$out"; fi
}
# delay constructs are NOT a refusal: they select the --timing build
# (each vpath is its own class, so this builds fresh)
if out=$(TRS_VLT_CACHE=$C "$TRS" vlt build sysPosCounter.bir --vpath "$WK/rtl-delay" 2>&1) \
   && echo "$out" | grep -q "built, contract"; then ok timing-build
else bad timing-build "$out"; fi

refusal refuse-dpi      "$WK/rtl-dpi"      "REFUSE(dpi)"
refusal refuse-mismatch "$WK/rtl-mismatch" "REFUSE(contract-mismatch)"
refusal refuse-missing  "$WK/empty-nowhere" "source resolution"

# ---- per-class lock: concurrent builds of one class, fresh cache
rm -rf cache-par
( TRS_VLT_CACHE=$WK/cache-par "$TRS" vlt build sysPosCounter.bir --vpath "$RTL" >par1.out 2>&1 ) &
( TRS_VLT_CACHE=$WK/cache-par "$TRS" vlt build sysPosCounter.bir --vpath "$RTL" >par2.out 2>&1 ) &
wait
if grep -q "contract" par1.out && grep -q "contract" par2.out; then ok lock-parallel
else bad lock-parallel "$(cat par1.out par2.out)"; fi

# ---- license notice beside the artifact
if ls "$C"/vlt/*/NOTICE >/dev/null 2>&1; then ok notice
else bad notice; fi

# ---- link chain: verilate step runs inside `bsc -sim -trs -e`
cp "$RTL/BviCounter.v" .
if TRS_VLT_CACHE=$C $BSC -sim -trs -e sysPosCounter >link.out 2>&1; then
    ok link-chain
else bad link-chain "$(tail -5 link.out)"; fi

# ---- cross-release positives: the stable-interface metadata (V<top>.h
# port macros + VM_TIMING in classes.mk) must work on a DIFFERENT 5.x
# release than the pin -- plain and timing builds both
SYS=${TRS_VERILATOR_SYS:-/usr/bin/verilator}
if [ -x "$SYS" ] && env -u VERILATOR_ROOT "$SYS" --version 2>/dev/null | \
       awk '{ split($2, v, "."); exit !(v[1] >= 5) }'; then
    if out=$(env -u VERILATOR_ROOT TRS_VLT_CACHE=$C TRS_VERILATOR="$SYS" \
             "$TRS" vlt build sysPosCounter.bir --vpath "$RTL" 2>&1) \
       && echo "$out" | grep -q "built, contract"; then ok sysver-build
    else bad sysver-build "$out"; fi
    if out=$(env -u VERILATOR_ROOT TRS_VLT_CACHE=$C TRS_VERILATOR="$SYS" \
             "$TRS" vlt build sysPosCounter.bir --vpath "$WK/rtl-delay" 2>&1) \
       && echo "$out" | grep -q "built, contract"; then ok sysver-timing
    else bad sysver-timing "$out"; fi
else
    echo "SKIP sysver-build/sysver-timing (no other 5.x verilator; set TRS_VERILATOR_SYS)"
fi

# ---- floor-refusal negative: a pre-5.0 verilator must produce the
# capability floor error, not a parse failure
OLD=${TRS_VERILATOR_OLD:-/usr/bin/verilator}
if [ -x "$OLD" ] && env -u VERILATOR_ROOT "$OLD" --version 2>/dev/null | \
       awk '{ split($2, v, "."); exit !(v[1] < 5) }'; then
    if out=$(env -u VERILATOR_ROOT TRS_VLT_CACHE=$C TRS_VERILATOR="$OLD" \
             "$TRS" vlt build sysPosCounter.bir --vpath "$RTL" 2>&1); then
        bad floor-refusal "unexpectedly succeeded on $OLD" "$out"
    elif echo "$out" | grep -q "does not support --timing"; then ok floor-refusal
    else bad floor-refusal "(missing floor message)" "$out"; fi
else
    echo "SKIP floor-refusal (no pre-5.0 verilator found; set TRS_VERILATOR_OLD)"
fi

exit $fail
