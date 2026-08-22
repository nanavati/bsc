#!/bin/sh
# BVI R3 gate battery: the trs link verilate-or-cache pipeline.
#   - counter contract verilates end-to-end into a dlopen-checked .so
#   - cache hit on re-invocation; content invalidation via the depfile
#     manifest; per-class lock survives concurrent builds
#   - delay constructs select the --timing build mode (detected via the
#     --timing inspection dump) and still build end-to-end
#   - refusals: DPI (metadata or __Dpi.h backstop), contract/model
#     mismatch, unresolvable source
#   - `bsc -sim -trs -e` chains into the verilate step, then fails only
#     with the tagged R4 runtime placeholder
# Optional: TRS_VERILATOR_NEW=/path/to/post-5.046/bin/verilator (with
# its VERILATOR_ROOT_NEW) adds the JSON-adapter leg.
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

# ---- positive build + dlopen check
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

# ---- link chain: verilate step runs inside `bsc -sim -trs -e`; the
# only acceptable failure is the tagged R4 runtime placeholder
cp "$RTL/BviCounter.v" .
if TRS_VLT_CACHE=$C $BSC -sim -trs -e sysPosCounter >link.out 2>&1; then
    ok link-chain
elif grep -q "plan rung R4" link.out; then ok link-chain
else bad link-chain "$(tail -5 link.out)"; fi

# ---- optional post-5.046 leg (JSON adapter)
if [ -n "$TRS_VERILATOR_NEW" ]; then
    if out=$(TRS_VLT_CACHE=$C TRS_VERILATOR="$TRS_VERILATOR_NEW" \
             VERILATOR_ROOT="$VERILATOR_ROOT_NEW" \
             "$TRS" vlt build sysPosCounter.bir --vpath "$RTL" 2>&1) \
       && echo "$out" | grep -q "contract"; then ok json-adapter
    else bad json-adapter "$out"; fi
    refusal_new() {
        if out=$(TRS_VLT_CACHE=$C TRS_VERILATOR="$TRS_VERILATOR_NEW" \
                 VERILATOR_ROOT="$VERILATOR_ROOT_NEW" \
                 "$TRS" vlt build sysPosCounter.bir --vpath "$2" 2>&1); then
            bad "$1 (unexpectedly succeeded)" "$out"
        elif echo "$out" | grep -q "$3"; then ok "$1"
        else bad "$1 (missing tag $3)" "$out"; fi
    }
    if out=$(TRS_VLT_CACHE=$C TRS_VERILATOR="$TRS_VERILATOR_NEW" \
             VERILATOR_ROOT="$VERILATOR_ROOT_NEW" \
             "$TRS" vlt build sysPosCounter.bir --vpath "$WK/rtl-delay" 2>&1) \
       && echo "$out" | grep -q "built, contract"; then ok json-timing-build
    else bad json-timing-build "$out"; fi
    refusal_new json-refuse-dpi   "$WK/rtl-dpi"   "REFUSE(dpi)"
fi

exit $fail
