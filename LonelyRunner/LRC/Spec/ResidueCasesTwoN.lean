import LonelyRunner.LRC.Spec.ResidueCasesN
import LonelyRunner.LRC.Spec.ParityMixedOneThreeN

set_option linter.style.longLine false

/-!
# The residue cases with M(1,3) (order eight)

2026-10-07.  Continues `ResidueCasesN`.  Each case takes the isolation at the grid shifts `j/4`
(quarter level) or `k/8` (eighth level), displaced by an offset.  This file adds the two cases whose
offset is M(1,3) (`ParityMixedOneThreeN`) to the composed statement, on the same counts of a set `S`
of positive whole numbers: `m` multiples of `8`, `o` odd readings, `t` readings `≡ 2 (mod 4)`, `f`
readings `≡ 4 (mod 8)`.  It adds no existence step.

* T9 `lonely_eight_of_quarter_one_three`: `o ≤ 3`, `m + f ≤ 1`, `t ≤ 3`.
* T10 `lonely_eight_of_eighth_one_three`: `CountSplit8 o t 0`, `m ≤ 1`, `f ≤ 3`.
* `SettledCounts8'`: `SettledCounts8` (T1–T5, T7, T8), or T9, or T10.
* `lonely_eight_of_settled_counts'`: `SettledCounts8'` of the counts of `S`, or T6's hypotheses
  `OottCase8 S`, make `S` lonely at `1/8`.
* `lonely_eight_or_open_counts'`: `S` is lonely at `1/8`, or neither holds.
* `lonely_eight_or_residual_open`: under the hypotheses of `lonely_eight_or_residual` (at most seven
  positive readings, no common factor `g ≥ 2`), `S` is lonely at `1/8`, or `EightResidual S` holds,
  `SettledCounts8'` fails on its counts and T6's hypotheses fail.
* `crowded_counts_one_three_m1` … `_m4`, by `decide +kernel`: on the residue patterns of
  `ResidueCasesN.crowdedPatterns`, the number settled by `SettledCounts8'` or `OottCounts8`.  This
  is a consistency check between the Lean predicate and `experiments/nN/redo/lean_case_reach_v3.py`
  (the column "with M(1,3) as well"), not a cascade statement.

**Tags.**  The free shifts of T9 (the quarter shifts, `exists_quarter_shift`) and T10 (the eighth
shifts, `exists_free_shift`) are counts [PROVISIONAL: counting tool; supports: the free shift of
each case].  The count form of the parity split used for T10 is [PROVISIONAL: counting tool;
supports: the count form of the parity split].  M(1,3)'s own counting steps (`qp_arc`, `qp_third`,
`p_choice`) carry their tags in `ParityMixedOneThreeN`.  T1–T8 keep the tags recorded in
`ResidueCasesN`, including T6's [PROVISIONAL: covering; supports: `free_shift_oott`].

**Lower-order inputs.**  T9 and T10 go through `exists_mixed_one_three`, which by its own header
uses no order four (fewer numbers are padded, not passed to `exists_mixed_le_three`).  T1–T8 keep
the lower-order inputs listed in `ResidueCasesN` (order seven for T1 and T2, order four for T3–T8).
`lonely_eight_or_residual_open` also rests on `lonely_eight_or_residual`, whose first rule is
`lonely_eight_of_card_le_six` (order seven) and whose proof also reaches `SpecN.existenceAtN_four`,
`OrderFiveN.lonely_five_nat` and `OrderSixN.lonely_six_nat`.  Checked on the transitive constant
closure of each statement (`experiments/nN/residue_cases_two_lower_order_v1.out`): the closures of
T9 and T10 contain none of `existenceAtN_three`, `existenceAtN_four`, `lonely_five_nat`,
`lonely_seven_nat` and no constant of `LRC.OrderSixN`.  The owner's ruling on such inputs
(compilation ground rule 4) is owed.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.ParityDescent

/-- **The settled counts with M(1,3).**  `SettledCounts8` (T1–T5, T7, T8), or the count form of T9
(`o ≤ 3`, `m + f ≤ 1`, `t ≤ 3`), or the count form of T10 (`CountSplit8 o t 0`, `m ≤ 1`, `f ≤ 3`). -/
def SettledCounts8' (m o t f : ℕ) : Prop :=
  SettledCounts8 m o t f ∨
  (o ≤ 3 ∧ m + f ≤ 1 ∧ t ≤ 3) ∨
  (CountSplit8 o t 0 ∧ m ≤ 1 ∧ f ≤ 3)

instance (m o t f : ℕ) : Decidable (SettledCounts8' m o t f) := by
  unfold SettledCounts8'; infer_instance

end LRC.ParityDescent

namespace LRC.OrderEightN

open ConstructionN LRC.Descent LRC.ParityDescent

/-- **The residue cases with M(1,3), composed.**  A set `S` of positive whole numbers is lonely at
`1/8` when `SettledCounts8'` holds of its counts (`m` multiples of `8`, `o` odd readings, `t`
readings `≡ 2 (mod 4)`, `f` readings `≡ 4 (mod 8)`), or when T6's hypotheses `OottCase8 S` hold.
The new disjuncts are T9 `lonely_eight_of_quarter_one_three` and T10
`lonely_eight_of_eighth_one_three`; the others are `lonely_eight_of_settled_counts`.

Tags inherited from the cases: the free shifts of T1–T5 and T7–T10 are counts
[PROVISIONAL: counting tool; supports: the free shift of each case], and T6's free shift is a
non-cover [PROVISIONAL: covering; supports: `free_shift_oott`].  The count form of the parity split
used for T1, T5, T8 and T10 is [PROVISIONAL: counting tool; supports: the count form of the parity
split].  Lower-order inputs: see the file header. -/
theorem lonely_eight_of_settled_counts' {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d)
    (h : SettledCounts8' (S.filter (fun d => 8 ∣ d)).card (S.filter (fun d => ¬ 2 ∣ d)).card
        (S.filter (fun d => d % 4 = 2)).card (S.filter (fun d => d % 8 = 4)).card ∨ OottCase8 S) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  have h4c := card_four_dvd_eq S
  rcases h with h | hO
  · unfold SettledCounts8' at h
    rcases h with h | ⟨ho, hmf, ht⟩ | ⟨hs, hm, hf⟩
    · exact lonely_eight_of_settled_counts hpos (Or.inl h)
    · exact lonely_eight_of_quarter_one_three hpos ho (by omega) ht
    · exact lonely_eight_of_eighth_one_three hpos ((paritySplit8_rest_iff S).mpr hs) hm hf
  · exact lonely_eight_of_settled_counts hpos (Or.inr hO)

/-- **The residual of the residue cases with M(1,3).**  A set of positive whole numbers is lonely
at `1/8`, or `SettledCounts8'` fails on its counts and T6's hypotheses fail.  The complement of
`lonely_eight_of_settled_counts'`; it carries the same tags. -/
theorem lonely_eight_or_open_counts' {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) :
    (∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t)) ∨
      (¬ SettledCounts8' (S.filter (fun d => 8 ∣ d)).card (S.filter (fun d => ¬ 2 ∣ d)).card
          (S.filter (fun d => d % 4 = 2)).card (S.filter (fun d => d % 8 = 4)).card ∧
        ¬ OottCase8 S) := by
  classical
  by_cases h : SettledCounts8' (S.filter (fun d => 8 ∣ d)).card (S.filter (fun d => ¬ 2 ∣ d)).card
      (S.filter (fun d => d % 4 = 2)).card (S.filter (fun d => d % 8 = 4)).card ∨ OottCase8 S
  · exact Or.inl (lonely_eight_of_settled_counts' hpos h)
  · exact Or.inr (not_or.mp h)

/-- **The residual, combined with the residue cases.**  Under the hypotheses of
`lonely_eight_or_residual` (at most seven positive readings, no common factor `g ≥ 2`), the set is
lonely at `1/8`, or it is in `EightResidual`, `SettledCounts8'` fails on its counts and T6's
hypotheses fail.  It carries the tags of `lonely_eight_of_settled_counts'` and the lower-order
inputs of `lonely_eight_or_residual`: orders four, five, six and seven (see the file header). -/
theorem lonely_eight_or_residual_open {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) (hcard : S.card ≤ 7)
    (hcf : ∀ g, 2 ≤ g → ∃ d ∈ S, ¬ g ∣ d) :
    (∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t)) ∨
      (EightResidual S ∧
        ¬ SettledCounts8' (S.filter (fun d => 8 ∣ d)).card (S.filter (fun d => ¬ 2 ∣ d)).card
          (S.filter (fun d => d % 4 = 2)).card (S.filter (fun d => d % 8 = 4)).card ∧
        ¬ OottCase8 S) := by
  rcases lonely_eight_or_residual hpos hcard hcf with h | hres
  · exact Or.inl h
  · rcases lonely_eight_or_open_counts' hpos with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hres, h1, h2⟩

/-! ## A consistency check on residue patterns, with M(1,3)

The patterns are `crowdedPatterns m` of `ResidueCasesN` (the multisets of `7 − m` residues in
`[1, 7]` with at least two odd and `∑ max 2 (gcd r 8) ≥ 8`).  This compares this file's predicate
with `experiments/nN/redo/lean_case_reach_v3.py`, column "with M(1,3) as well"; it is not a cascade
statement and not a measure of progress. -/

/-- A pattern is settled when `SettledCounts8'` or `OottCounts8` holds of its counts. -/
def PatternSettled8' (m : ℕ) (p : List ℕ) : Prop :=
  SettledCounts8' m (p.countP fun r => decide (¬ 2 ∣ r)) (p.countP fun r => decide (r % 4 = 2))
      (p.countP fun r => decide (r % 8 = 4)) ∨
    OottCounts8 m (p.countP fun r => decide (r % 8 = 1 ∨ r % 8 = 7))
      (p.countP fun r => decide (r % 8 = 3 ∨ r % 8 = 5)) (p.countP fun r => decide (r % 4 = 2))
      (p.countP fun r => decide (r % 8 = 4))

instance (m : ℕ) (p : List ℕ) : Decidable (PatternSettled8' m p) := by
  unfold PatternSettled8'; infer_instance

/-- `m = 4`: 10 patterns, 10 settled. -/
theorem crowded_counts_one_three_m4 : (crowdedPatterns 4).length = 10 ∧
    ((crowdedPatterns 4).filter fun p => decide (PatternSettled8' 4 p)).length = 10 := by
  decide +kernel

/-- `m = 3`: 155 patterns, 102 settled. -/
theorem crowded_counts_one_three_m3 : (crowdedPatterns 3).length = 155 ∧
    ((crowdedPatterns 3).filter fun p => decide (PatternSettled8' 3 p)).length = 102 := by
  decide +kernel

/-- `m = 2`: 381 patterns, 162 settled. -/
theorem crowded_counts_one_three_m2 : (crowdedPatterns 2).length = 381 ∧
    ((crowdedPatterns 2).filter fun p => decide (PatternSettled8' 2 p)).length = 162 := by
  decide +kernel

/-- `m = 1`: 812 patterns, 242 settled. -/
theorem crowded_counts_one_three_m1 : (crowdedPatterns 1).length = 812 ∧
    ((crowdedPatterns 1).filter fun p => decide (PatternSettled8' 1 p)).length = 242 := by
  decide +kernel

end LRC.OrderEightN
