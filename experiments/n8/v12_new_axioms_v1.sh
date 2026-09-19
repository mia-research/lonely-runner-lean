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
for d in rescaled_residue rescaled_blocks_iff gcd_covariant divisor_reduces small_b_blocks_iff common_factor_reduces reduced_modulus_dvd blocker_class; do
  echo "#print axioms Rescale.$d" >> "$T/Resc.lean"; done
lake env lean "$T/Resc.lean"

# --- Involution (standalone) ---
cp ../experiments/n8/Involution_v1.lean "$T/Inv.lean"
for d in clear_reflect reflect_fails_zero reflect_fails_one; do
  echo "#print axioms Involution.$d" >> "$T/Inv.lean"; done
lake env lean "$T/Inv.lean"

# --- EdgeWitness (standalone) ---
cp ../experiments/n8/EdgeWitness_v1.lean "$T/EW.lean"
for d in tight_of_step tight_of_step_up edge_witness edge_witness_both; do
  echo "#print axioms EdgeWitness.$d" >> "$T/EW.lean"; done
lake env lean "$T/EW.lean"

# --- TimeReversal (standalone) ---
cp ../experiments/n8/TimeReversal_v1.lean "$T/TR.lean"
for d in bad_reflect clear_reflect_x; do
  echo "#print axioms TimeReversal.$d" >> "$T/TR.lean"; done
lake env lean "$T/TR.lean"

# --- TwoPatterns (standalone) ---
cp ../experiments/n8/TwoPatterns_v1.lean "$T/TP.lean"
for d in unit_on_both reflected_reading blocked_reflect; do
  echo "#print axioms TwoPatterns.$d" >> "$T/TP.lean"; done
lake env lean "$T/TP.lean"

# --- Degenerate2 (standalone) ---
cp ../experiments/n8/Degenerate2_v1.lean "$T/D2.lean"
for d in two_degenerate two_both_patterns contains_two_coincides; do
  echo "#print axioms Degenerate2.$d" >> "$T/D2.lean"; done
lake env lean "$T/D2.lean"

# --- SolutionPair (needs EdgeWitness's Sat) ---
grep -v '^import' ../experiments/n8/EdgeWitness_v1.lean > "$T/SP.lean"
grep -v '^import' ../experiments/n8/SolutionPair_v1.lean >> "$T/SP.lean"
sed -i '' '1i\
import LonelyRunner.LRC.ConstructionN.LemmaPass
' "$T/SP.lean"
for d in two_of_reflect not_singleton zero_not_sat; do
  echo "#print axioms SolutionPair.$d" >> "$T/SP.lean"; done
lake env lean "$T/SP.lean"

# --- GeneralOrder (standalone) ---
cp ../experiments/n8/GeneralOrder_v1.lean "$T/GO.lean"
for d in clear_of_not_dvd spine_all_or_nothing small_b_general; do
  echo "#print axioms GeneralOrder.$d" >> "$T/GO.lean"; done
lake env lean "$T/GO.lean"

# --- SplitLaw (standalone) ---
cp ../experiments/n8/SplitLaw_v1.lean "$T/SL.lean"
for d in lo_split hi_split blocked_split split_law; do
  echo "#print axioms SplitLaw.$d" >> "$T/SL.lean"; done
lake env lean "$T/SL.lean"

# --- GeneralReflect (standalone) ---
cp ../experiments/n8/GeneralReflect_v1.lean "$T/GR.lean"
for d in L_split U_split sum_split obstruction_iff L_small U_small width_pos; do
  echo "#print axioms GeneralReflect.$d" >> "$T/GR.lean"; done
lake env lean "$T/GR.lean"

# --- FlankBridge (standalone) ---
cp ../experiments/n8/FlankBridge_v1.lean "$T/FB.lean"
for d in inWay_mod half_mover_whole half_mover_same_parity no_opposite_parity_halves lonely_of_largest_flank_clear existence_of_largest_flank_clear; do echo "#print axioms FlankBridge.$d" >> "$T/FB.lean"; done
lake env lean "$T/FB.lean"

# --- SmallQFlank (standalone) ---
cp ../experiments/n8/SmallQFlank_v1.lean "$T/SQ.lean"
for d in blocks_zero blocks_zero_of_dvd; do
  echo "#print axioms SmallQFlank.$d" >> "$T/SQ.lean"; done
lake env lean "$T/SQ.lean"
