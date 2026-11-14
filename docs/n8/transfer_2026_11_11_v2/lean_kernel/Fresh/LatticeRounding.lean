import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Floor.Ring

namespace Fresh.FiniteRelations

open scoped BigOperators RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Round one coefficient against an arbitrary current residual.
A weighted average of the two adjacent choices cancels the cross term. -/
theorem round_one_squared (w u : E) (c : ℝ) :
    ∃ z : ℤ, ‖w+(c-(z:ℝ)) • u‖^2 ≤ ‖w‖^2+‖u‖^2/4 := by
  let a := Int.fract c
  have ha : 0 ≤ a := Int.fract_nonneg c
  have ha' : a ≤ 1 := (Int.fract_lt_one c).le
  have he (x : ℝ) :
      ‖w+x • u‖^2 = ‖w‖^2+2*x*⟪w, u⟫+x^2*‖u‖^2 := by
    rw [norm_add_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    ring
  have hmean :
      (1-a)*‖w+a • u‖^2+a*‖w+(a-1) • u‖^2 =
      ‖w‖^2+a*(1-a)*‖u‖^2 := by rw [he,he]; ring
  have hlim : a*(1-a) ≤ 1/4 := by nlinarith [sq_nonneg (a-1/2)]
  let B := ‖w‖^2+‖u‖^2/4
  have hb : (1-a)*‖w+a • u‖^2+a*‖w+(a-1) • u‖^2 ≤ B := by
    rw [hmean]
    dsimp [B]
    nlinarith only [mul_le_mul_of_nonneg_right hlim (sq_nonneg ‖u‖)]
  by_cases h : ‖w+a • u‖^2 ≤ B
  · exact ⟨⌊c⌋,h⟩
  have h' : ‖w+(a-1) • u‖^2 ≤ B := by
    by_contra! hh
    rcases eq_or_lt_of_le ha with ha0 | hap
    · rw [← ha0] at hb
      norm_num at hb
      exact h (by simpa only [← ha0,zero_smul,add_zero] using hb)
    · have h1 := mul_le_mul_of_nonneg_left (le_of_not_ge h) (sub_nonneg.mpr ha')
      have h2 := mul_lt_mul_of_pos_left hh hap
      nlinarith only [hb,add_lt_add_of_le_of_lt h1 h2]
  refine ⟨⌊c⌋+1,?_⟩
  have hcast : c-((⌊c⌋+1:ℤ):ℝ) = a-1 := by
    rw [Int.cast_add,Int.cast_one]
    change _ = c-(⌊c⌋:ℝ)-1
    ring
  rw [hcast]
  exact h'

/-- Rounding any finite collection of coefficients increases squared
residual norm by at most a quarter of the sum of squared row lengths.
This deterministic induction replaces randomized rounding. -/
theorem round_rows_squared {ι : Type*} (S : Finset ι) (u : ι → E) (c : ι → ℝ) (w : E) :
    ∃ z : ι → ℤ, ‖w+∑ j ∈ S, (c j-(z j:ℝ)) • u j‖^2 ≤
      ‖w‖^2+(∑ j ∈ S, ‖u j‖^2)/4 := by
  classical
  induction S using Finset.induction_on generalizing w with
  | empty => exact ⟨fun _ => 0,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨k,hk⟩ := round_one_squared w (u i) (c i)
    obtain ⟨z,hz⟩ := ih (w+(c i-(k:ℝ)) • u i)
    refine ⟨Function.update z i k,?_⟩
    rw [Finset.sum_insert hi,Finset.sum_insert hi,Function.update_self,← add_assoc]
    have he : (∑ j ∈ S, (c j-((Function.update z i k j:ℤ):ℝ)) • u j) =
        ∑ j ∈ S, (c j-(z j:ℝ)) • u j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      rw [Function.update_of_ne hji]
    rw [he]
    linarith only [hz,hk]

#print axioms round_rows_squared

end Fresh.FiniteRelations
