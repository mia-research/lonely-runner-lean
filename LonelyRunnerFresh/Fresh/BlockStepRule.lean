import Fresh.Localisation

/-! The cascade's step on an AP block, in the framework's own terms (log E660; derivation E653, E658, E659).
Signed readings of one AP block of speeds satisfy `e_i = e_j + D` with `D = (i - j) s`. At the exit of reading `j`
(`σ e_j t = M + 1/8`, `σ = ±1` the sign of `e_j`), with `y = σ D t`:
* `block_inWay_iff`: reading `i` is in the way (`InWay |e_i| t`) iff `3/4 < fract y`;
* `block_nextOpening_same`: if `e_i` has the sign of `e_j` and is in the way, its `nextOpening` is
  `t + (1 - fract y)/|e_i|`;
* `block_nextOpening_opp`: if `e_i` has the opposite sign and is in the way, its `nextOpening` is
  `t + (fract y - 3/4)/|e_i|`.
`IsMove` then takes the largest `nextOpening` among in-way readings (its definition); these theorems give each
candidate from the block's phase step alone. No covering or counting step.
-/
namespace Fresh.BlockStepRule
open Fresh

theorem inWay_shift_iff (y : ℝ) : distInt (1/8 + y) < 1/8 ↔ 3/4 < Int.fract y := by
  have hy : y = (⌊y⌋ : ℝ) + Int.fract y := (Int.floor_add_fract y).symm
  have hsh : distInt (1/8 + y) = distInt (1/8 + Int.fract y) := by
    have : (1:ℝ)/8 + y = (1/8 + Int.fract y) + ((⌊y⌋ : ℤ) : ℝ) := by unfold Int.fract; ring
    rw [this, Fresh.Localisation.distInt_add_int]
  rw [hsh]
  have h0 := Int.fract_nonneg y
  have h1 := Int.fract_lt_one y
  constructor
  · intro h
    by_contra hc
    have hc' : Int.fract y ≤ 3/4 := not_lt.mp hc
    have := Fresh.Localisation.clear_of_window (y := 1/8 + Int.fract y) 0 (by push_cast; linarith) (by push_cast; linarith)
    linarith
  · intro hf
    have h2 := Fresh.Localisation.distInt_le (1/8 + Int.fract y) 1
    have habs : |1/8 + Int.fract y - ((1:ℤ):ℝ)| < 1/8 := by
      rw [abs_lt]; push_cast; constructor <;> linarith
    linarith

theorem block_inWay_iff {ej D t σ : ℝ} {M : ℤ} (hσ : σ = 1 ∨ σ = -1) (hj : σ * ej * t = M + 1/8) :
    InWay |ej + D| t ↔ 3/4 < Int.fract (σ * D * t) := by
  unfold InWay
  rw [Fresh.Localisation.distInt_abs_mul]
  have key : distInt ((ej + D) * t) = distInt (1/8 + σ * D * t) := by
    have e1 : distInt ((ej + D) * t) = distInt (σ * ((ej + D) * t)) := by
      rcases hσ with rfl | rfl
      · simp
      · rw [show (-1:ℝ) * ((ej + D) * t) = -((ej + D) * t) by ring, Fresh.Localisation.distInt_neg]
    rw [e1]
    have : σ * ((ej + D) * t) = (1/8 + σ * D * t) + (M : ℤ) := by
      push_cast; nlinarith [hj]
    rw [this, Fresh.Localisation.distInt_add_int]
  rw [key]
  exact inWay_shift_iff _

theorem block_nextOpening_same {ej D t σ : ℝ} {M : ℤ} (hj : σ * ej * t = M + 1/8)
    (hpos : 0 < σ * (ej + D)) (hf : 3/4 < Int.fract (σ * D * t)) :
    nextOpening (σ * (ej + D)) t = t + (1 - Int.fract (σ * D * t)) / (σ * (ej + D)) := by
  set y := σ * D * t with hydef
  have hy : y = (⌊y⌋ : ℝ) + Int.fract y := (Int.floor_add_fract y).symm
  have h1 := Int.fract_lt_one y
  have hdt : σ * (ej + D) * t = (M : ℝ) + 1/8 + (⌊y⌋ : ℝ) + Int.fract y := by
    have : σ * (ej + D) * t = σ * ej * t + y := by rw [hydef]; ring
    rw [this, hj]; linarith [hy]
  have hceil : ⌈σ * (ej + D) * t - 1/8⌉ = M + ⌊y⌋ + 1 := by
    rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  have hd : σ * (ej + D) ≠ 0 := ne_of_gt hpos
  calc nextOpening (σ * (ej + D)) t
      = (((M + ⌊y⌋ + 1 : ℤ) : ℝ) + 1/8) / (σ * (ej + D)) := by unfold nextOpening; rw [hceil]
    _ = (σ * (ej + D) * t + (1 - Int.fract y)) / (σ * (ej + D)) := by
        congr 1; push_cast; linarith [hdt]
    _ = t + (1 - Int.fract y) / (σ * (ej + D)) := by
        rw [add_div]; congr 1; exact mul_div_cancel_left₀ t hd

theorem block_nextOpening_opp {ej D t σ : ℝ} {M : ℤ} (hj : σ * ej * t = M + 1/8)
    (hneg : σ * (ej + D) < 0) (hf : 3/4 < Int.fract (σ * D * t)) :
    nextOpening (-(σ * (ej + D))) t = t + (Int.fract (σ * D * t) - 3/4) / (-(σ * (ej + D))) := by
  set y := σ * D * t with hydef
  have hy : y = (⌊y⌋ : ℝ) + Int.fract y := (Int.floor_add_fract y).symm
  have h1 := Int.fract_lt_one y
  have hdt : -(σ * (ej + D)) * t = -((M : ℝ) + 1/8 + (⌊y⌋ : ℝ) + Int.fract y) := by
    have : -(σ * (ej + D)) * t = -(σ * ej * t + y) := by rw [hydef]; ring
    rw [this, hj]; linarith [hy]
  have hceil : ⌈-(σ * (ej + D)) * t - 1/8⌉ = -M - ⌊y⌋ - 1 := by
    rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  have hd : -(σ * (ej + D)) ≠ 0 := by linarith
  calc nextOpening (-(σ * (ej + D))) t
      = (((-M - ⌊y⌋ - 1 : ℤ) : ℝ) + 1/8) / (-(σ * (ej + D))) := by unfold nextOpening; rw [hceil]
    _ = (-(σ * (ej + D)) * t + (Int.fract y - 3/4)) / (-(σ * (ej + D))) := by
        congr 1; push_cast; linarith [hdt]
    _ = t + (Int.fract y - 3/4) / (-(σ * (ej + D))) := by
        rw [add_div]; congr 1; exact mul_div_cancel_left₀ t hd

#print axioms inWay_shift_iff
#print axioms block_inWay_iff
#print axioms block_nextOpening_same
#print axioms block_nextOpening_opp
end Fresh.BlockStepRule
