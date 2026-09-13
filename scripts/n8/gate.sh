#!/usr/bin/env bash
# Construction8 done-check gate.
#
# What PASS means: parts 1-6 of docs/n8/PROOF_CANDIDATE_v3.md are formalised, with no
# sorry, no native_decide/unsafe/admit, and every headline declaration axiom-clean.
#
# What PASS does NOT mean: LRC(8) is proved. Part 7 -- the Claim -- is deliberately not
# stated in this tree, and check [4] FAILS THE GATE if someone states it. The plan's
# reason (docs/n8/PROOF_PLAN_v1.md §2) is that writing it down invites an attack with
# whatever machinery closes it, which is the failure mode the register exists to stop.
#
# Checks, in order:
#   0. build-artefact integrity (the project sits under iCloud; eviction leaves dataless
#      .olean files that lake treats as up to date but Lean cannot read)
#   1. every Construction8 module builds -- a plain `lake build` does NOT, since
#      LonelyRunner.lean imports only LonelyRunner.Basic and never enters LRC/
#   2. zero `sorry` in the Construction8 tree
#   2b. no native_decide / unsafe / admit
#   3. #print axioms on every headline declaration == [propext, Classical.choice, Quot.sound]
#   4. part 7 is NOT stated
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT" || exit 2
LOG="${1:-/tmp/n8_gate_build.log}"
SRC=LonelyRunner/LRC/Construction8

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

echo "== [1] build every Construction8 module =="
MODS="LonelyRunner.LRC.Construction8.Parts
LonelyRunner.LRC.Construction8.LemmaPass
LonelyRunner.LRC.Construction8.Coords
LonelyRunner.LRC.Construction8.Reference
LonelyRunner.LRC.Construction8.Gaps
LonelyRunner.LRC.Construction8.Sorted
LonelyRunner.LRC.Construction8.Grid
LonelyRunner.LRC.Construction8.Integrality
LonelyRunner.LRC.Construction8.Flank
LonelyRunner.LRC.Construction8.Window
LonelyRunner.LRC.Construction8.Bounds"
lake build $MODS > "$LOG" 2>&1
BUILD_EXIT=$?
tail -2 "$LOG"
if [ $BUILD_EXIT -ne 0 ]; then
  echo "GATE FAIL: build exit $BUILD_EXIT"
  grep -E '^error|error:' "$LOG" | head -20
  exit 1
fi

echo "== [2] sorry inventory =="
N8_SORRY=$(grep -nE '(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)' $SRC/*.lean 2>/dev/null \
  | grep -vE ':[0-9]+: *--' | grep -vE '`sorry`')
if [ -n "$N8_SORRY" ]; then
  echo "$N8_SORRY" | sed 's/^/  /'
  echo "  count: $(echo "$N8_SORRY" | wc -l | tr -d ' ')"
else
  echo "  none"
fi

echo "== [2b] proof-hygiene scan =="
HYG=$(grep -rnE 'native_decide|^[[:space:]]*unsafe[[:space:]]+(def|theorem|lemma|instance)|(^|<;>[[:space:]]*|;[[:space:]]*)[[:space:]]*admit[[:space:]]*$' \
  $SRC/*.lean 2>/dev/null \
  | grep -vE '^[^:]+:[0-9]+:[[:space:]]*--' | grep -vE '`native_decide`|`unsafe`|`admit`')
if [ -n "$HYG" ]; then
  echo "$HYG" | sed 's/^/  /'
  HYG_OK=0
else
  echo "  clean (no native_decide / unsafe / admit)"
  HYG_OK=1
fi

echo "== [3] axiom check, headline declarations =="
DECLS="gaps_all_eq
nearest_below
nearest_above
before_floor
displacement
lonely_iff_flanks
lonely_iff_flanks_first
lonely_iff_flanks_last
window_iff
reading_clear_iff
lap_and_phase
ap_reference
survives_of
int_of_pairwise_sep
not_dvd_of_sep
coord_iff
equally_spaced_of_pairwise
grid_of_pairwise
no_solo_closure
wide_gap_core
ratio_condition
lonely_ne_pred
wide_gap_speeds"
AX=LonelyRunner/_N8GateAxCheck.lean
{
  echo 'import LonelyRunner.LRC.Construction8.Window'
  echo 'import LonelyRunner.LRC.Construction8.Integrality'
  echo 'import LonelyRunner.LRC.Construction8.Coords'
  echo 'import LonelyRunner.LRC.Construction8.Bounds'
  for d in $DECLS; do echo "#print axioms Construction8.$d"; done
} > "$AX"
AXOUT=$(lake env lean "$AX" 2>&1)
rm -f "$AX"
NDECL=$(echo "$DECLS" | wc -l | tr -d ' ')
NCLEAN=$(echo "$AXOUT" | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]")
echo "  $NCLEAN of $NDECL clean"
BAD=$(echo "$AXOUT" | grep -vE "depends on axioms: \[propext, Classical.choice, Quot.sound\]" | grep -E "axiom|error|sorryAx")
if [ -n "$BAD" ]; then echo "$BAD" | sed 's/^/  /'; fi
[ "$NCLEAN" = "$NDECL" ] && AX_OK=1 || AX_OK=0
echo "$AXOUT" | grep -q "sorryAx" && AX_OK=0

echo "== [4] part 7 must NOT be stated =="
P7=$(grep -nE '^[[:space:]]*(theorem|lemma|def)[[:space:]]+[A-Za-z_]*([Cc]laim|part_?7|part7|lrc_?8|LRC8)' \
  $SRC/*.lean 2>/dev/null)
if [ -n "$P7" ]; then
  echo "$P7" | sed 's/^/  /'
  echo "  part 7 appears to be stated -- see docs/n8/PROOF_PLAN_v1.md §2"
  P7_OK=0
else
  echo "  clean (part 7 unstated, as intended)"
  P7_OK=1
fi

echo
NTHM=$(grep -c '^theorem' $SRC/*.lean | awk -F: '{s+=$2} END {print s}')
if [ "$AX_OK" = "1" ] && [ -z "$N8_SORRY" ] && [ "$HYG_OK" = "1" ] && [ "$P7_OK" = "1" ]; then
  echo "GATE PASS: $NTHM theorems, parts 1-6 formalised and axiom-clean."
  echo "           LRC(8) is NOT proved -- part 7 remains open and unstated."
  exit 0
fi
echo "GATE FAIL."
exit 1
