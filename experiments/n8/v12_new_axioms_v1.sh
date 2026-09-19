#!/bin/bash
# Axiom witness for the 28 declarations added in MANUSCRIPT_v12 section 13.
# Run from LonelyRunner/.  Output: experiments/n8/v12_new_axioms_v1.out
set -e
cd "$(dirname "$0")/../../LonelyRunner"
T=$(mktemp -d)

cp ../experiments/n8/GapRule_v1.lean "$T/GapRule_v1.lean"
echo "#print axioms GapRule.gap_eq" >> "$T/GapRule_v1.lean"
echo "#print axioms GapRule.gap_ge" >> "$T/GapRule_v1.lean"
echo "#print axioms GapRule.no_gap_iff" >> "$T/GapRule_v1.lean"
lake env lean "$T/GapRule_v1.lean"

cp ../experiments/n8/ReachRule_v1.lean "$T/ReachRule_v1.lean"
echo "#print axioms ReachRule.reach_nil" >> "$T/ReachRule_v1.lean"
echo "#print axioms ReachRule.reach_cons" >> "$T/ReachRule_v1.lean"
echo "#print axioms ReachRule.le_reach" >> "$T/ReachRule_v1.lean"
echo "#print axioms ReachRule.covered_below_reach" >> "$T/ReachRule_v1.lean"
echo "#print axioms ReachRule.covers_of_reach_gt" >> "$T/ReachRule_v1.lean"
echo "#print axioms ReachRule.reach_uncovered" >> "$T/ReachRule_v1.lean"
echo "#print axioms ReachRule.reach_decides" >> "$T/ReachRule_v1.lean"
echo "#print axioms ReachRule.uncovered_witness" >> "$T/ReachRule_v1.lean"
echo "#print axioms ReachRule.reach_mem" >> "$T/ReachRule_v1.lean"
echo "#print axioms ReachRule.reach_in_endpoints" >> "$T/ReachRule_v1.lean"
echo "#print axioms ReachRule.reach_denom" >> "$T/ReachRule_v1.lean"
echo "#print axioms ReachRule.finite_check" >> "$T/ReachRule_v1.lean"
echo "#print axioms ReachRule.witness_normalised" >> "$T/ReachRule_v1.lean"
lake env lean "$T/ReachRule_v1.lean"

cp ../experiments/n8/ArithForm_v1.lean "$T/ArithForm_v1.lean"
echo "#print axioms ArithForm.near_iff_int" >> "$T/ArithForm_v1.lean"
echo "#print axioms ArithForm.covers_iff_int" >> "$T/ArithForm_v1.lean"
lake env lean "$T/ArithForm_v1.lean"

cp ../experiments/n8/Guard_v1.lean "$T/Guard_v1.lean"
echo "#print axioms Guard.guard_blocks_below" >> "$T/Guard_v1.lean"
echo "#print axioms Guard.raising_unguards" >> "$T/Guard_v1.lean"
echo "#print axioms Guard.klein_self_inverse" >> "$T/Guard_v1.lean"
echo "#print axioms Guard.ap_clear_at_odd" >> "$T/Guard_v1.lean"
echo "#print axioms Guard.unguarded_width" >> "$T/Guard_v1.lean"
echo "#print axioms Guard.odd_clear_of_not_dvd" >> "$T/Guard_v1.lean"
echo "#print axioms Guard.block_periodic" >> "$T/Guard_v1.lean"
echo "#print axioms Guard.block_shift" >> "$T/Guard_v1.lean"
lake env lean "$T/Guard_v1.lean"

cp ../experiments/n8/NoFinitePoints_v1.lean "$T/NoFinitePoints_v1.lean"
echo "#print axioms NoFinitePoints.near_eight_blocks" >> "$T/NoFinitePoints_v1.lean"
echo "#print axioms NoFinitePoints.one_reading_blocks_all" >> "$T/NoFinitePoints_v1.lean"
lake env lean "$T/NoFinitePoints_v1.lean"

# --- added after v12: BlockerCount + Rescale (Rescale imports BlockerCount's `blocks`) ---
cat ../experiments/n8/BlockerCount_v1.lean > "$T/Resc.lean"
grep -v '^import' ../experiments/n8/Rescale_v1.lean >> "$T/Resc.lean"
for d in self_residue self_never_blocks unit_never_blocks; do
  echo "#print axioms BlockerCount.$d" >> "$T/Resc.lean"; done
for d in rescaled_residue rescaled_blocks_iff gcd_covariant divisor_reduces; do
  echo "#print axioms Rescale.$d" >> "$T/Resc.lean"; done
lake env lean "$T/Resc.lean"
