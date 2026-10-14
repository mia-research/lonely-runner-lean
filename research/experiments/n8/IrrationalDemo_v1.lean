import LonelyRunner.LRC.Construction8.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Pi.Irrational

/-!
Scratch, not part of either tree.  How the existing `Construction8` statements handle a
commensurate and an incommensurate speed set, using `ratio_condition` (Thm 4.8) unchanged.
-/

open Real

namespace IrrationalDemo

/-- Theorem 4.8 read on one real difference `d`: if `dmin ≤ |d| ≤ 7·dmin` then that runner is
clear of the subject at `t = 1/(8·dmin)`.  Only `Construction8.ratio_condition` is used. -/
theorem clear_of_ratio {dmin d : ℝ} (hm : 0 < dmin) (h1 : dmin ≤ |d|) (h7 : |d| ≤ 7 * dmin) :
    (8 : ℝ)⁻¹ ≤ circDist (d * (1 / (8 * dmin))) := by
  have hs1 : 1 ≤ |d| / dmin := by rw [le_div_iff₀ hm]; linarith
  have hs7 : |d| / dmin ≤ ((8 : ℕ) : ℝ) - 1 := by
    rw [div_le_iff₀ hm]; push_cast; linarith
  have key := Construction8.ratio_condition (n := 8) (by norm_num) hs1 hs7
  push_cast at key
  rcases abs_cases d with ⟨hd, _⟩ | ⟨hd, _⟩
  · have e : d * (1 / (8 * dmin)) = |d| / dmin / 8 := by rw [hd]; field_simp
    rw [e]; exact key
  · have e : d * (1 / (8 * dmin)) = -(|d| / dmin / 8) := by rw [hd]; field_simp
    rw [e, circDist.symm_neg]; exact key

/-! ## Incommensurate: `r3 = π` -/

/-- Speeds `1, 2, π, 4, 5, 6, 7, 8`. -/
noncomputable def V : Fin 8 → ℝ := ![1, 2, π, 4, 5, 6, 7, 8]

/-- Each runner's nearest difference: `4 − π` for the runners at `π` and `4`, else `1`. -/
noncomputable def M : Fin 8 → ℝ := ![1, 1, 4 - π, 4 - π, 1, 1, 1, 1]

/-- **Every runner is lonely at its own `t = 1/(8·d_min)`**, with `d_min` irrational for two
of them.  No rational approximation of `π` is used — only `3 < π < 3.15`. -/
theorem all_lonely : ∀ i j : Fin 8, j ≠ i →
    (8 : ℝ)⁻¹ ≤ circDist ((V j - V i) * (1 / (8 * M i))) := by
  have h3 := pi_gt_three
  have h315 : π < 3.15 := pi_lt_d2
  norm_num at h315
  intro i j hji
  have hM : 0 < M i := by fin_cases i <;> simp [M] <;> linarith
  apply clear_of_ratio hM <;>
  fin_cases i <;> fin_cases j <;> simp_all [V, M] <;> norm_num <;>
  first
  | (rw [abs_of_nonneg (by linarith)]; linarith)
  | (rw [abs_of_neg (by linarith)]; linarith)
  | linarith

/-- The shared time of the runners at `π` and at `4` is irrational. -/
theorem time_irrational : Irrational (1 / (8 * (4 - π))) := by
  have h := ((irrational_pi.natCast_sub 4).natCast_mul (m := 8) (by norm_num)).inv
  simpa [one_div] using h

/-- The `d_min` of the runner at `π` is attained: its neighbour at `4`. -/
theorem dmin_attained : |V 3 - V 2| = M 2 := by
  have h3 := pi_gt_three
  simp [V, M]; exact pi_le_four

/-! ## Commensurate: `r3 = 3.141593` -/

def q : ℚ := 3141593 / 1000000

noncomputable def Vq : Fin 8 → ℝ := ![1, 2, (q : ℝ), 4, 5, 6, 7, 8]
noncomputable def Mq : Fin 8 → ℝ := ![1, 1, 4 - (q : ℝ), 4 - (q : ℝ), 1, 1, 1, 1]

theorem all_lonely_q : ∀ i j : Fin 8, j ≠ i →
    (8 : ℝ)⁻¹ ≤ circDist ((Vq j - Vq i) * (1 / (8 * Mq i))) := by
  intro i j hji
  have hM : 0 < Mq i := by fin_cases i <;> simp [Mq, q] <;> norm_num
  apply clear_of_ratio hM <;>
  fin_cases i <;> fin_cases j <;> simp_all [Vq, Mq, q] <;> norm_num [abs_of_nonneg, abs_of_neg]

/-- Its time is the rational `125000/858407`. -/
theorem time_rational : 1 / (8 * (4 - (q : ℝ))) = ((125000 / 858407 : ℚ) : ℝ) := by
  simp [q]; norm_num

end IrrationalDemo

#print axioms IrrationalDemo.all_lonely
#print axioms IrrationalDemo.time_irrational
#print axioms IrrationalDemo.all_lonely_q
#print axioms IrrationalDemo.time_rational

#print axioms IrrationalDemo.dmin_attained
