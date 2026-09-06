#!/usr/bin/env bash
# n=7 done-check gate. Exit 0 only when intLRC_seven is fully verified.
#
# Checks, in order:
#   0. build-artefact integrity (iCloud eviction leaves dataless .olean files
#      that lake treats as up-to-date but Lean cannot read)
#   1. lake build exits 0
#   2. zero `sorry` warnings anywhere in the IntLRC_7_BS tree
#   2b. no native_decide / unsafe / admit in the n=7 tree
#   3. #print axioms intLRC_seven == [propext, Classical.choice, Quot.sound]
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT" || exit 2
LOG="${1:-/tmp/n7_gate_build.log}"

echo "== [0] build-artefact integrity =="
DATALESS=$(find .lake/build -name '*.olean' -print0 2>/dev/null \
  | xargs -0 stat -f '%b %N' 2>/dev/null | awk '$1==0 {print $2}')
if [ -n "$DATALESS" ]; then
  echo "  purging dataless (cloud-evicted) oleans:"
  echo "$DATALESS" | sed 's/^/    /'
  echo "$DATALESS" | while read -r f; do
    rm -f "$f" "${f%.olean}.trace" "${f%.olean}.olean.hash" \
           "${f%.olean}.ilean" "${f%.olean}.ilean.hash"
  done
else
  echo "  clean"
fi

echo "== [1] lake build =="
lake build LonelyRunner.LRC.SmallN.IntLRC_7 LonelyRunner.LRC.SmallN.IntLRC_6 LonelyRunner.LRC.SmallN.IntLRC_7_BS.Section7_M1 LonelyRunner.LRC.SmallN.IntLRC_7_BS.Case66_Tables LonelyRunner.LRC.SmallN.IntLRC_7_BS.Case61_Place > "$LOG" 2>&1
BUILD_EXIT=$?
tail -3 "$LOG"
if [ $BUILD_EXIT -ne 0 ]; then
  echo "GATE FAIL: build exit $BUILD_EXIT"
  grep -E '^error|error:' "$LOG" | head -20
  exit 1
fi

echo "== [2] sorry inventory (IntLRC_7_BS tree) =="
N7_SORRY=$(grep -nE '(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)' \
  LonelyRunner/LRC/SmallN/IntLRC_7_BS/*.lean LonelyRunner/LRC/SmallN/IntLRC_7.lean 2>/dev/null \
  | grep -vE ':[0-9]+: *--' | grep -vE '`sorry`')
if [ -n "$N7_SORRY" ]; then
  echo "$N7_SORRY" | sed 's/^/  /'
  echo "  count: $(echo "$N7_SORRY" | wc -l | tr -d ' ')"
else
  echo "  none"
fi

echo "== [2b] proof-hygiene scan =="
# Tactic uses only. `admit` must be the whole tactic line (the word also occurs
# in prose: "admit a unit multiplier"); `unsafe` must open a declaration.
HYG=$(grep -rnE 'native_decide|^[[:space:]]*unsafe[[:space:]]+(def|theorem|lemma|instance)|(^|<;>[[:space:]]*|;[[:space:]]*)[[:space:]]*admit[[:space:]]*$' \
  LonelyRunner/LRC/SmallN/IntLRC_7_BS/*.lean LonelyRunner/LRC/SmallN/IntLRC_7.lean 2>/dev/null \
  | grep -vE '^[^:]+:[0-9]+:[[:space:]]*--' | grep -vE '`native_decide`|`unsafe`|`admit`')
if [ -n "$HYG" ]; then
  echo "$HYG" | sed 's/^/  /'
  HYG_OK=0
else
  echo "  clean (no native_decide / unsafe / admit)"
  HYG_OK=1
fi

echo "== [3] axiom check =="
AX=LonelyRunner/_N7GateAxCheck.lean
cat > "$AX" <<'LEAN'
import LonelyRunner.LRC.SmallN.IntLRC_7
#print axioms intLRC_seven
LEAN
AXOUT=$(lake env lean "$AX" 2>&1)
rm -f "$AX"
echo "$AXOUT"

echo "$AXOUT" | grep -q "depends on axioms: \[propext, Classical.choice, Quot.sound\]" \
  && AX_OK=1 || AX_OK=0
echo "$AXOUT" | grep -q "sorryAx" && AX_OK=0

if [ "$AX_OK" = "1" ] && [ -z "$N7_SORRY" ] && [ "$HYG_OK" = "1" ]; then
  echo "GATE PASS: intLRC_seven complete and axiom-clean."
  exit 0
fi
echo "GATE FAIL: n=7 not yet closed."
exit 1
