#!/usr/bin/env bash
# Cascade artefact done-check gate (LonelyRunner/LRC/Cascade/).
#
# What PASS means: every module of the cascade artefact builds, contains no sorry / native_decide / unsafe /
# admit, and EVERY theorem in it depends on [propext, Classical.choice, Quot.sound] only.
#
# What PASS does NOT mean: Existence at order 8 -- that the cascade reaches a clear scale for every arrangement
# and runner -- is proved. It is open and deliberately not stated here; check [4] fails the gate if a declaration
# naming it appears.
#
# Checks: [0] build-artefact integrity (iCloud eviction); [1] explicit build of every module (a plain `lake build`
# does not enter LRC/); [2] sorry inventory; [2b] hygiene scan; [3] #print axioms on every theorem; [4] the open
# statement is not stated.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT" || exit 2
LOG="${1:-/tmp/cascade_gate_build.log}"
SRC=LonelyRunner/LRC/Cascade

echo "== [0] build-artefact integrity =="
DATALESS=$(find .lake/build -name '*.olean' -print0 2>/dev/null \
  | xargs -0 stat -f '%b %N' 2>/dev/null | awk '$1==0 {print $2}')
if [ -n "$DATALESS" ]; then
  echo "  purging dataless (cloud-evicted) oleans:"
  echo "$DATALESS" | sed 's/^/    /'
  echo "$DATALESS" | while read -r f; do
    rm -f "$f" "${f%.olean}.trace" "${f%.olean}.olean.hash" "${f%.olean}.ilean" "${f%.olean}.ilean.hash"
  done
else
  echo "  clean"
fi

echo "== [1] build every cascade module =="
MODS="LonelyRunner.LRC.Cascade.Iteration
LonelyRunner.LRC.Cascade.SmallOrders
LonelyRunner.LRC.Cascade.FourDifferences
LonelyRunner.LRC.Cascade.VersionB
LonelyRunner.LRC.Cascade.Reading
LonelyRunner.LRC.Cascade.Irrational
LonelyRunner.LRC.Cascade.All"
lake build $MODS > "$LOG" 2>&1
BUILD_EXIT=$?
tail -1 "$LOG"
if [ $BUILD_EXIT -ne 0 ]; then
  echo "GATE FAIL: build exit $BUILD_EXIT"; grep -E 'error' "$LOG" | head -20; exit 1
fi

echo "== [2] sorry inventory =="
SORRY=$(grep -nE '(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)' $SRC/*.lean 2>/dev/null \
  | grep -vE ':[0-9]+: *--' | grep -vE '`sorry`')
if [ -n "$SORRY" ]; then echo "$SORRY" | sed 's/^/  /'; else echo "  none"; fi

echo "== [2b] proof-hygiene scan =="
HYG=$(grep -rnE 'native_decide|^[[:space:]]*unsafe[[:space:]]+(def|theorem|lemma|instance)|(^|<;>[[:space:]]*|;[[:space:]]*)[[:space:]]*admit[[:space:]]*$' \
  $SRC/*.lean 2>/dev/null | grep -vE '^[^:]+:[0-9]+:[[:space:]]*--' | grep -vE '`native_decide`|`unsafe`|`admit`')
if [ -n "$HYG" ]; then echo "$HYG" | sed 's/^/  /'; HYG_OK=0; else echo "  clean"; HYG_OK=1; fi

echo "== [3] axiom check, every theorem =="
AX=LonelyRunner/_CascadeGateAxCheck.lean
{
  echo 'import LonelyRunner.LRC.Cascade.All'
  for f in $SRC/Iteration.lean $SRC/SmallOrders.lean $SRC/FourDifferences.lean $SRC/VersionB.lean $SRC/Reading.lean $SRC/Irrational.lean; do
    awk '/^namespace /{ns=$2} /^end /{if($2==ns) ns=""} /^theorem /{name=$2; if(ns!="") print "#print axioms " ns "." name; else print "#print axioms " name}' "$f"
  done
} > "$AX"
NDECL=$(grep -c '^#print axioms' "$AX")
AXOUT=$(lake env lean "$AX" 2>&1)
rm -f "$AX"
NCLEAN=$(echo "$AXOUT" | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]")
echo "  $NCLEAN of $NDECL clean"
BAD=$(echo "$AXOUT" | grep -vE "depends on axioms: \[propext, Classical.choice, Quot.sound\]" | grep -E "axiom|error|sorryAx|unknown")
if [ -n "$BAD" ]; then echo "$BAD" | sed 's/^/  /'; fi
[ "$NCLEAN" = "$NDECL" ] && AX_OK=1 || AX_OK=0

echo "== [4] the open statement (Existence at order 8) must NOT be stated =="
OPEN=$(grep -nE '^[[:space:]]*(theorem|lemma|def|axiom)[[:space:]]+[A-Za-z_.]*([Ll][Rr][Cc]|[Cc]laim|[Ee]xistence|reaches_clear_scale|run_always_ends)' \
  $SRC/*.lean 2>/dev/null)
if [ -n "$OPEN" ]; then echo "$OPEN" | sed 's/^/  /'; OPEN_OK=0; else echo "  clean (unstated, as intended)"; OPEN_OK=1; fi

echo
if [ "$AX_OK" = "1" ] && [ -z "$SORRY" ] && [ "$HYG_OK" = "1" ] && [ "$OPEN_OK" = "1" ]; then
  echo "GATE PASS: $NDECL theorems, axiom-clean."
  echo "           Existence at order 8 is NOT proved -- it remains open and unstated."
  exit 0
fi
echo "GATE FAIL."; exit 1
