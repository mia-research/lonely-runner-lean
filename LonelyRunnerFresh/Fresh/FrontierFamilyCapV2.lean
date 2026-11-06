import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.KTaxonomy

/-!
# The frontier family cap (outside-J2, T2b/T2c/T3), native — first label-family schema

Written 2026-11-06.  New file; nothing existing is edited.  V2 of `FrontierFamilyCap.lean`, which did not compile (5 errors: `sub_add_eq_sub_sub` rewrite x2, `cascadeSeq_zero` type `1/8` against `1/(8*1)`, `div_pos_iff_of_pos_right` direction, a conjunct `511 / 31 < 17` elaborated in ℕ); the statements are unchanged apart from the ℝ ascription, the proofs are repaired.  Built on `Fresh.Framework`,
`Fresh.Cascade` (`fixed_is_first_isolation`, `not_inWay_iff`, `distInt_le`) and `Fresh.KTaxonomy`
(`StabilizesAtMin`).  Sources: `experiments/n8/outside_j2_t2b_carve_rho7_max_v1.py/.out`,
`outside_j2_t2c_frontier_joint_lift_v1.py/.out`, `outside_j2_t3_mechanism_v1.py/.out` (agent G's
outside-J2 analysis; owner-greenlit "one family as an actual Lean proof").

The frontier family, in the taxonomy's `R`-coordinate (readings normalised, `ρ₁ = 1`, cascade
start `t₀ = 1/8`, phase `t = R/8`, so `InWay ρ t ↔ 8j-1 < ρR < 8j+1` for the zone of lap `j`):

* end-pins of a carve of `[1,7]`: the `R = 7` coverer is a lap-6 strip, `47/7 < ρ₆ < 49/7 = 7`
  (`seven_strip_covers_R7` — natively `InWay ρ₆ (7/8)`); the `R = 1` coverer of the frontier is
  the top reading as a lap-2 strip, `15 < ρ₇ < 17` (`strip_covers_R1` — `InWay ρ₇ (1/8)`);
* the binding seam (G (iii)/(iv)): the handover from `ρ₇`'s lap-9 zone (exit `73/ρ₇`) to `ρ₆`'s
  lap-4 zone (entry `31/ρ₆`) must not leave a gap: `31/ρ₆ ≤ 73/ρ₇` (`seam_nogap`);
* the cap (G (ii)-(iv)): `31/ρ₆ ≤ 73/ρ₇` with `ρ₆ < 7` forces `ρ₇ ≤ 73·7/31 = 511/31 < 17`
  (`frontier_cap`, `five11_lt_17`).  Pure rational arithmetic.

The bridge (G (i)): "landing ∈ W₁ ⟺ [1,7] carved empty"; the crucial half is *a clear point
`R_c` ⇒ every cascade step ≤ `R_c` ⇒ the fixed point exists at or before `R_c`*.  Divergence
from the hand account: in `Fresh` this half is not `Localisation.lean`'s `localisation`
(flank openings) but `Fresh.Cascade`'s no-overshoot machinery (`fixed_is_first_isolation`,
there `seq_le_of_lonely`/`exists_fixed_of_lonely`), which composes directly:
`first_landing_le_lonely` (the first landing is ≤ every positive lonely instant) and
`carved_of_landing_ge_nine_eighths` (a landing at phase `9/8`, i.e. `R ≥ 9` = `W₁`'s left end,
implies `[1/8, 7/8]`, i.e. `[1,7]`, is carved: every point has some reading in the way).
The dual `lonely_witness_of_not_carved` extracts the family's witness (a clear point) from a
failed carve.

Family theorem format (this file sets it; later families instantiate the same shape):
hypotheses = pattern (end-pins + seam), core = arithmetic (`frontier_cap`), conclusion via
bridge (`carved_of_landing_ge_nine_eighths`): `frontier_family_cap`.

Tightness (not formalised): the cap is saturated by the exact joint-lift witness of T2c,
`vector2 = [1, 3221761554497/1099511627776, 4334178521711/1099511627776,
2687190683461/549755813888, 7081933799491/1099511627776, 481036336437/68719476736,
18124207743665/1099511627776]` with `ρ₇ = 16.48387092…` against `511/31 = 16.48387096…`
(carve exact, landing `9`, window `1`), so the constant `511/31` is the tight one to use.

OWED: `FrontierCarveCap` — the classifier step (a carve with the end-pins forces the seam),
i.e. the interval-chain/compactness argument of G (iii).  Not provable from what `Fresh` has
today; the seam is therefore a hypothesis of the family, and the cap core is proved regardless.
-/

open Classical

namespace Fresh.FrontierFamilyCapV2

open Fresh Fresh.Cascade Fresh.KTaxonomy

variable {ds : Finset ℝ} {N : ℕ}

/-! ## The end-pins as native strip conditions -/

/-- A lap-6 strip (`47/7 < ρ < 49/7`) covers `R = 7`: the `R = 7` end-pin, natively. -/
theorem seven_strip_covers_R7 {ρ : ℝ} (h1 : 47 / 7 < ρ) (h2 : ρ < 49 / 7) : InWay ρ (7 / 8) := by
  have hb1 : 47 < 7 * ρ := by nlinarith
  have hb2 : 7 * ρ < 49 := by nlinarith
  have e : ρ * (7 / 8) = (7 * ρ - 48) / 8 + 6 := by ring
  unfold InWay
  rw [e]
  have hle : distInt ((7 * ρ - 48) / 8 + 6) ≤ |(7 * ρ - 48) / 8 + 6 - 6| :=
    Fresh.Cascade.distInt_le _ 6
  have e2 : (7 * ρ - 48) / 8 + 6 - 6 = (7 * ρ - 48) / 8 := by ring
  rw [e2] at hle
  have habs : |(7 * ρ - 48) / 8| < 1 / 8 := by
    rw [abs_lt]
    constructor <;> linarith
  linarith

#print axioms seven_strip_covers_R7

/-- A lap-2 strip (`15 < ρ < 17`) covers `R = 1`: the frontier's `R = 1` end-pin, natively. -/
theorem strip_covers_R1 {ρ : ℝ} (h1 : 15 < ρ) (h2 : ρ < 17) : InWay ρ (1 / 8) := by
  have e : ρ * (1 / 8) = (ρ - 16) / 8 + 2 := by ring
  unfold InWay
  rw [e]
  have hle : distInt ((ρ - 16) / 8 + 2) ≤ |(ρ - 16) / 8 + 2 - 2| :=
    Fresh.Cascade.distInt_le _ 2
  have e2 : (ρ - 16) / 8 + 2 - 2 = (ρ - 16) / 8 := by ring
  rw [e2] at hle
  have habs : |(ρ - 16) / 8| < 1 / 8 := by
    rw [abs_lt]
    constructor <;> linarith
  linarith

#print axioms strip_covers_R1

/-! ## The bridge (G (i)): a clear point bounds the landing -/

/-- The first landing of the cascade from the bound `1/8` (reading `1` present) is at or before
every positive lonely instant: G (i)'s "every cascade step ≤ R_c ⇒ the fixed point exists at or
before R_c", via `fixed_is_first_isolation` (the landing is the FIRST isolation). -/
theorem first_landing_le_lonely (hpos : ∀ d ∈ ds, 0 < d) (hone : (1 : ℝ) ∈ ds)
    (hS : StabilizesAtMin ds (1 / 8) N) {s : ℝ} (hs : 0 < s) (hl : LonelyAt ds s) :
    cascadeSeq ds (1 / 8) N ≤ s :=
  (fixed_is_first_isolation hpos hone (by rw [cascadeSeq_zero ds (1 / 8)]; norm_num)
    (cascadeSeq_isMove ds (1 / 8)) hS.1).2 s hs hl

#print axioms first_landing_le_lonely

/-- A landing at phase `9/8` (`R ≥ 9`, the left end of `W₁`) implies `[1/8, 7/8]` (`[1,7]`) is
carved: every instant of the interval has some reading in the way.  This is the crucial half of
G (i): a clear point `R_c` would be lonely and push the first landing to or below it. -/
theorem carved_of_landing_ge_nine_eighths (hpos : ∀ d ∈ ds, 0 < d) (hone : (1 : ℝ) ∈ ds)
    (hS : StabilizesAtMin ds (1 / 8) N) (hland : 9 / 8 ≤ cascadeSeq ds (1 / 8) N) :
    ∀ t, 1 / 8 ≤ t → t ≤ 7 / 8 → ∃ d ∈ ds, InWay d t := by
  intro t ht₁ ht₂
  by_contra hnp
  push_neg at hnp
  have hl : LonelyAt ds t := fun d hd => not_inWay_iff.mp (hnp d hd)
  have hle := first_landing_le_lonely hpos hone hS (lt_of_lt_of_le (by norm_num) ht₁) hl
  linarith

#print axioms carved_of_landing_ge_nine_eighths

/-- The dual: a failed carve yields the family's witness — a clear (lonely) point of `[1,7]`. -/
theorem lonely_witness_of_not_carved
    (hnp : ¬ ∀ t, 1 / 8 ≤ t → t ≤ 7 / 8 → ∃ d ∈ ds, InWay d t) :
    ∃ t, 1 / 8 ≤ t ∧ t ≤ 7 / 8 ∧ LonelyAt ds t := by
  push_neg at hnp
  obtain ⟨t, h1, h2, hclear⟩ := hnp
  exact ⟨t, h1, h2, fun d hd => not_inWay_iff.mp (hclear d hd)⟩

#print axioms lonely_witness_of_not_carved

/-! ## The core: end-pins + binding seam cap ρ₇ -/

/-- The seam condition is the no-gap condition at the handover: no `R` lies strictly between
`ρ₇`'s lap-9 exit `73/ρ₇` and `ρ₆`'s lap-4 entry `31/ρ₆`. -/
theorem seam_nogap {ρ₆ ρ₇ : ℝ} (h₆ : 0 < ρ₆) (h₇ : 0 < ρ₇) (hseam : 31 / ρ₆ ≤ 73 / ρ₇) :
    ∀ R : ℝ, 73 / ρ₇ < R → R < 31 / ρ₆ → False := by
  intro R h1 h2
  have hc : (31 : ℝ) * ρ₇ ≤ 73 * ρ₆ := (div_le_div_iff₀ h₆ h₇).mp hseam
  nlinarith

#print axioms seam_nogap

/-- **The frontier cap** (G (ii)-(iv)): a lap-6 strip `ρ₆` (`< 7`) whose lap-4 zone takes over
from `ρ₇`'s lap-9 zone without a gap forces `ρ₇ ≤ 511/31`. -/
theorem frontier_cap {ρ₆ ρ₇ : ℝ} (h₆₁ : 47 / 7 < ρ₆) (h₆₂ : ρ₆ < 49 / 7)
    (hseam : 31 / ρ₆ ≤ 73 / ρ₇) : ρ₇ ≤ 511 / 31 := by
  have h₆pos : 0 < ρ₆ := by positivity
  have h₇pos : 0 < ρ₇ := by
    have hc0 : (0 : ℝ) < 31 / ρ₆ := by positivity
    have := lt_of_lt_of_le hc0 hseam
    have h73 : (0 : ℝ) < 73 := by norm_num
    have hgt : (0 : ℝ) < 73 / ρ₇ := this
    by_contra hneg
    push_neg at hneg
    have hle := div_nonpos_of_nonneg_of_nonpos (le_of_lt h73) hneg
    linarith
  have hc : (31 : ℝ) * ρ₇ ≤ 73 * ρ₆ := (div_le_div_iff₀ h₆pos h₇pos).mp hseam
  have h73 : (73 : ℝ) * ρ₆ < 73 * (49 / 7) := by
    apply mul_lt_mul_of_pos_left h₆₂
    norm_num
  have e : (73 : ℝ) * (49 / 7) = 511 := by norm_num
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 31)]
  linarith

#print axioms frontier_cap

theorem five11_lt_17 : (511 : ℝ) / 31 < 17 := by norm_num

#print axioms five11_lt_17

/-! ## The family theorem (schema for the 14 label families) -/

/-- **The frontier family theorem.**  Hypotheses = the pattern (end-pins; the binding seam), the
cascade context, and the label (landing in `W₁`, phase `≥ 9/8`).  Conclusion: `ρ₇ ≤ 511/31 < 17`
(core arithmetic), and `[1,7]` is carved (bridge).  Later label families instantiate this
shape: pattern ⟶ cap core ⟶ bridge conclusion. -/
theorem frontier_family_cap (hpos : ∀ d ∈ ds, 0 < d) (hone : (1 : ℝ) ∈ ds)
    (hS : StabilizesAtMin ds (1 / 8) N) (hland : 9 / 8 ≤ cascadeSeq ds (1 / 8) N)
    {ρ₆ ρ₇ : ℝ} (h₆mem : ρ₆ ∈ ds) (h₇mem : ρ₇ ∈ ds)
    (h₆₁ : 47 / 7 < ρ₆) (h₆₂ : ρ₆ < 49 / 7) (hseam : 31 / ρ₆ ≤ 73 / ρ₇) :
    ρ₇ ≤ 511 / 31 ∧ (511 : ℝ) / 31 < 17 ∧
      ∀ t, 1 / 8 ≤ t → t ≤ 7 / 8 → ∃ d ∈ ds, InWay d t :=
  ⟨frontier_cap h₆₁ h₆₂ hseam, five11_lt_17,
    carved_of_landing_ge_nine_eighths hpos hone hS hland⟩

#print axioms frontier_family_cap

/-! ## The owed classifier -/

/-- A carve of `[1,7]` (in `R`-coordinates: every `R ∈ [1,7]` lies in some reading's zone
`8j-1 < ρR < 8j+1`). -/
-- STANDING: DEFINITION
def CarvesOneSeven (rs : Finset ℝ) : Prop :=
  ∀ R : ℝ, 1 ≤ R → R ≤ 7 → ∃ ρ ∈ rs, ∃ j : ℤ,
    ((j : ℝ)) * 8 - 1 < ρ * R ∧ ρ * R < ((j : ℝ)) * 8 + 1

/-- **OWED — the classifier** (G (iii)/(iv)): a sorted carve of `[1,7]` by six readings with the
`R = 7` end-pin (`47/7 < ρ₆ < 49/7`) and the top reading past `15` forces the binding seam
`31/ρ₆ ≤ 73/ρ₇`, hence (with `frontier_cap`) `ρ₇ ≤ 511/31`.  The hand proof chains the sorted
zone intervals: an interior seam between consecutive zones forces `ρ_b/ρ_a ≥ (8k-1)/(8j+1)`, and
the binding one for this family is the lap-9/lap-4 handover.  The Lean proof needs the
gap-implies-clear-point step along the chain (a finite closed-interval covering argument), which
`Fresh` does not have today; nothing here is assumed.  Divergence, recorded: the specific seam
is binding only relative to the chain's routing — a carver that routes the middle of `[1,7]`
through other readings satisfies other seam inequalities first, so the universal statement
below is the target, not a consequence of the definitions alone. -/
-- STANDING: OWED
def FrontierCarveCap : Prop :=
  ∀ ρ₂ ρ₃ ρ₄ ρ₅ ρ₆ ρ₇ : ℝ,
    1 ≤ ρ₂ → ρ₂ ≤ ρ₃ → ρ₃ ≤ ρ₄ → ρ₄ ≤ ρ₅ → ρ₅ ≤ ρ₆ → ρ₆ ≤ ρ₇ →
      47 / 7 < ρ₆ → ρ₆ < 49 / 7 → 15 < ρ₇ →
        CarvesOneSeven ({ρ₂, ρ₃, ρ₄, ρ₅, ρ₆, ρ₇} : Finset ℝ) →
          31 / ρ₆ ≤ 73 / ρ₇

end Fresh.FrontierFamilyCapV2
