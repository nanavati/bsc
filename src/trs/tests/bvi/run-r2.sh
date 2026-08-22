#!/bin/sh
# BVI R2 gate battery: the bsc EXPORT side only (runtime lands at R4).
#   positives: .bir produced under -trs and decodable by `trs ir dump`
#              (decode runs the Rust-side contract verifier)
#   negatives: the -trs link refuses with the expected tag
#   classic:   plain -sim keeps the G0084 refusal, byte-exact class
# BSC=/path/bsc TRS=/path/trs sh run-r2.sh [workdir]
BSC=${BSC:-bsc}
TRS=${TRS:-trs}
SRC=$(cd "$(dirname "$0")" && pwd)
case "$BSC" in
    */*) PATH="$(cd "$(dirname "$BSC")" && pwd):$PATH"; export PATH;;
esac
WK=${1:-$(mktemp -d)}
cd "$WK" || exit 2
fail=0

pos() { # name top
    name=$1; top=$2
    cp "$SRC/$name.bsv" .
    $BSC -sim -u -g "$top" "$name.bsv" >bsc.out 2>&1 || {
        echo "FAIL $name (bsc compile)"; head -3 bsc.out; fail=1; return; }
    # -e chains into `trs link`, whose runtime arm is rung R4: the ONLY
    # acceptable link failure until then is the tagged R4 placeholder.
    # The .bir must exist and decode either way (decode runs the Rust
    # contract verifier).
    if ! $BSC -sim -trs -e "$top" >link.out 2>&1; then
        grep -q "plan rung R4" link.out || {
            echo "FAIL $name (trs export)"; head -5 link.out
            fail=1; return; }
    fi
    [ -f "$top.bir" ] || { echo "FAIL $name (no .bir)"; fail=1; return; }
    "$TRS" ir dump "$top.bir" >dump.out 2>&1 || {
        echo "FAIL $name (ir dump/verify)"; head -5 dump.out; fail=1; return; }
    grep -q "Bvi" dump.out || {
        echo "FAIL $name (no Bvi instance in dump)"; fail=1; return; }
    echo "PASS $name"
}

neg() { # name top expected-substring
    name=$1; top=$2; want=$3
    cp "$SRC/$name.bsv" .
    $BSC -sim -u -g "$top" "$name.bsv" >bsc.out 2>&1 || {
        echo "FAIL $name (bsc compile)"; head -3 bsc.out; fail=1; return; }
    if $BSC -sim -trs -e "$top" >link.out 2>&1; then
        echo "FAIL $name (export unexpectedly succeeded)"; fail=1; return
    fi
    grep -q "$want" link.out || {
        echo "FAIL $name (missing tag '$want')"; head -8 link.out
        fail=1; return; }
    echo "PASS $name"
}

# classic Bluesim: the G0084 refusal is untouched
classic() {
    cp "$SRC/PosCounter.bsv" .
    $BSC -sim -u -g sysPosCounter PosCounter.bsv >bsc.out 2>&1 || {
        echo "FAIL classic (bsc compile)"; fail=1; return; }
    if $BSC -sim -e sysPosCounter >link.out 2>&1; then
        echo "FAIL classic (bluesim link unexpectedly succeeded)"
        fail=1; return
    fi
    grep -q "G0084" link.out || {
        echo "FAIL classic (expected G0084)"; head -5 link.out
        fail=1; return; }
    echo "PASS classic-g0084"
}

pos PosCounter sysPosCounter
pos PosShadowAction sysPosShadowAction
pos PosShadowFixed sysPosShadowFixed
pos PosArgRdy sysPosArgRdy
neg NegShadowCoactive sysNegShadowCoactive "consumes the result"
neg NegCFPath sysNegCFPath "not scheduled SB/SBR before"
neg NegReversedPath sysNegReversedPath "not scheduled SB/SBR before"
neg NegValueArgPath sysNegValueArgPath "value-method argument"
neg NegSharedOut sysNegSharedOut "shared by more than one"
neg NegOutClock sysNegOutClock "output clock"
# dynamic Port args never reach the trs refusal: bsc's own G0058
# (dynamic module arguments) fires first, at code generation
negcompile() { # name top want
    name=$1; top=$2; want=$3
    cp "$SRC/$name.bsv" .
    if $BSC -sim -u -g "$top" "$name.bsv" >bsc.out 2>&1; then
        echo "FAIL $name (compile unexpectedly succeeded)"; fail=1; return
    fi
    grep -q "$want" bsc.out || {
        echo "FAIL $name (missing tag '$want')"; head -8 bsc.out
        fail=1; return; }
    echo "PASS $name"
}
negcompile NegDynPort sysNegDynPort "G0058"
classic

exit $fail
