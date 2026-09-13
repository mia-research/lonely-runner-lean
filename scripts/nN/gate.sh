#!/usr/bin/env bash
# ConstructionN done-check gate -- the GENERAL-n line.
#
# THIS GATE DOES NOT GATE THE PAPER.  docs/n8/MANUSCRIPT_v1.md cites
# LonelyRunner/LRC/Construction8/, which is frozen and gated by scripts/n8/gate.sh.
# Run that one before trusting anything about the manuscript.
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
#   1. every ConstructionN module builds -- a plain `lake build` does NOT, since
#      LonelyRunner.lean imports only LonelyRunner.Basic and never enters LRC/
#   2. zero `sorry` in the ConstructionN tree
#   2b. no native_decide / unsafe / admit
#   3. #print axioms on every headline declaration == [propext, Classical.choice, Quot.sound]
#   4. part 7 is NOT stated
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT" || exit 2
LOG="${1:-/tmp/nN_gate_build.log}"
SRC=LonelyRunner/LRC/ConstructionN

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

echo "== [1] build every ConstructionN module =="
MODS="LonelyRunner.LRC.ConstructionN.Parts
LonelyRunner.LRC.ConstructionN.LemmaPass
LonelyRunner.LRC.ConstructionN.Coords
LonelyRunner.LRC.ConstructionN.Reference
LonelyRunner.LRC.ConstructionN.Gaps
LonelyRunner.LRC.ConstructionN.Sorted
LonelyRunner.LRC.ConstructionN.Grid
LonelyRunner.LRC.ConstructionN.Integrality
LonelyRunner.LRC.ConstructionN.Flank
LonelyRunner.LRC.ConstructionN.Window
LonelyRunner.LRC.ConstructionN.Bounds
LonelyRunner.LRC.ConstructionN.Instants"
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
wide_gap_speeds
dvd_of_forall_dvd_mul
spine_iff
spine_iff_residues
break_of_not_coprime
isolation_iff_coprime
card_coprime_eq_totient"
AX=LonelyRunner/_NNGateAxCheck.lean
{
  echo 'import LonelyRunner.LRC.ConstructionN.Window'
  echo 'import LonelyRunner.LRC.ConstructionN.Integrality'
  echo 'import LonelyRunner.LRC.ConstructionN.Coords'
  echo 'import LonelyRunner.LRC.ConstructionN.Bounds'
  echo 'import LonelyRunner.LRC.ConstructionN.Instants'
  for d in $DECLS; do echo "#print axioms ConstructionN.$d"; done
} > "$AX"
AXOUT=$(lake env lean "$AX" 2>&1)
rm -f "$AX"
NDECL=$(echo "$DECLS" | wc -l | tr -d ' ')
# A declaration may depend on a SUBSET of the three (a proof that needs no choice is
# cleaner, not worse), so match the allowed set rather than one exact string.
ALLOWED='depends on axioms: \[(propext)?(, )?(Classical\.choice)?(, )?(Quot\.sound)?\]$'
NCLEAN=$(echo "$AXOUT" | grep -cE "$ALLOWED")
echo "  $NCLEAN of $NDECL clean"
BAD=$(echo "$AXOUT" | grep -vE "$ALLOWED" | grep -E "axiom|error|sorryAx")
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
  echo "GATE PASS (general-n line): $NTHM theorems, axiom-clean."
  echo "           This does NOT gate the paper -- run scripts/n8/gate.sh for that."
  echo "           LRC is NOT proved at any n; part 7 remains open and unstated."
  exit 0
fi
echo "GATE FAIL."
exit 1
