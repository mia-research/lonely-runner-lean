import LonelyRunner.LRC.Construction8.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.NumberTheory.Real.Irrational

/-!
Part of the cascade artefact (`LRC/Cascade/`).  How the existing `Construction8` statements handle a
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


/-!
# An incommensurate arrangement, every runner, in Lean

Part of the cascade artefact (`LRC/Cascade/`).  Speeds `(1, 1+δ, 3, 4, 5, 6, 7, 8)` with `δ = √2/100`
(`SKETCH_v7` §7d).  `√2` is never approximated as a value: every step uses `√2·√2 = 2` and the
bracket `1.41421 < √2 < 1.41422`.

| runner | settled by | time |
|---|---|---|
| r2, speed `1+δ` | grid tier of the cascade, `D = d_min = δ`, spine `r = 3` (`u = 3/8`) | `3/(8δ) = 75√2/4`, irrational |
| r1, speed `1` | the integer pack, one difference exactly on the threshold | `71/8` |
| r3 … r8 | Theorem 4.8 (`ratio_condition`, unchanged), `d_min = 1` | `1/8` |

r2 is outside Theorem 4.8 (`r2_not_ratio`) and blocked at the first spine point
(`r2_blocked_at_first_spine`), so the step to `r = 3` is doing work.
-/

open Real

namespace IrrationalCascade

/-! ## Two band lemmas -/

/-- A point whose phase lies in `[1/8, 7/8]` above an integer `N` is clear. -/
theorem band {x : ℝ} (N : ℤ) (h1 : (N : ℝ) + 1 / 8 ≤ x) (h2 : x ≤ (N : ℝ) + 7 / 8) :
    (8 : ℝ)⁻¹ ≤ circDist x := by
  have hfl : ⌊x⌋ = N := by rw [Int.floor_eq_iff]; constructor <;> linarith
  unfold circDist
  simp only [Int.fract, hfl, le_min_iff]
  constructor <;> linarith

/-- A point within `1/8` above an integer is in the way. -/
theorem blocked {x : ℝ} (N : ℤ) (h1 : (N : ℝ) ≤ x) (h2 : x < (N : ℝ) + 1 / 8) :
    circDist x < (8 : ℝ)⁻¹ := by
  have hfl : ⌊x⌋ = N := by rw [Int.floor_eq_iff]; constructor <;> linarith
  unfold circDist
  simp only [Int.fract, hfl]
  exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

/-- Theorem 4.8 on one real difference, from `Construction8.ratio_condition` unchanged. -/
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

/-! ## The arrangement -/

theorem sqrt2_facts :
    √2 * √2 = 2 ∧ (141421 / 100000 : ℝ) < √2 ∧ √2 < (141422 / 100000 : ℝ) := by
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hp : 0 ≤ √2 := Real.sqrt_nonneg 2
  refine ⟨hs, ?_, ?_⟩ <;> nlinarith

noncomputable def δ : ℝ := √2 / 100

noncomputable def W : Fin 8 → ℝ := ![1, 1 + δ, 3, 4, 5, 6, 7, 8]

/-! ## r2 — the runner the cascade must step for -/

/-- r2's nearest difference is `δ`, to r1. -/
theorem r2_nearest : |W 0 - W 1| = δ := by
  have hp : 0 < δ := by unfold δ; positivity
  simp [W]; linarith

/-- r2 is outside Theorem 4.8: its largest difference exceeds `7·d_min`. -/
theorem r2_not_ratio : 7 * δ < |W 7 - W 1| := by
  obtain ⟨hs, hlo, hhi⟩ := sqrt2_facts
  simp [W, δ]; rw [abs_of_pos (by nlinarith)]; nlinarith

/-- r2 is blocked at the first spine point `u = 1/8`: the runner at speed 6 is in the way. -/
theorem r2_blocked_at_first_spine :
    circDist ((W 5 - W 1) * (1 / (8 * δ))) < (8 : ℝ)⁻¹ := by
  obtain ⟨hs, hlo, hhi⟩ := sqrt2_facts
  have hp : 0 < √2 := by nlinarith
  have ht : 1 / (8 * δ) = 25 * √2 / 4 := by
    unfold δ
    rw [div_eq_iff (by positivity)]
    linear_combination (-1 / 2 : ℝ) * hs
  rw [ht]
  refine blocked 44 ?_ ?_ <;> simp [W, δ] <;> nlinarith

/-- r2's time, `u = 3/8`, is `t = 3/(8δ) = 75√2/4`. -/
theorem r2_time : 3 / (8 * δ) = 75 * √2 / 4 := by
  obtain ⟨hs, hlo, hhi⟩ := sqrt2_facts
  have hp : 0 < √2 := by nlinarith
  unfold δ
  rw [div_eq_iff (by positivity)]
  linear_combination (-3 / 2 : ℝ) * hs

theorem r2_time_irrational : Irrational (3 / (8 * δ)) := by
  rw [r2_time]
  have h := irrational_sqrt_two.ratCast_mul (q := 75 / 4) (by norm_num)
  convert h using 1
  push_cast; ring

/-- **r2 is lonely at the irrational time `3/(8δ)`.** -/
theorem r2_lonely : ∀ j : Fin 8, j ≠ 1 →
    (8 : ℝ)⁻¹ ≤ circDist ((W j - W 1) * (3 / (8 * δ))) := by
  obtain ⟨hs, hlo, hhi⟩ := sqrt2_facts
  intro j hj
  rw [r2_time]
  fin_cases j
  · refine band (-1) ?_ ?_ <;> simp [W, δ] <;> nlinarith
  · simp at hj
  · refine band 52 ?_ ?_ <;> simp [W, δ] <;> nlinarith
  · refine band 79 ?_ ?_ <;> simp [W, δ] <;> nlinarith
  · refine band 105 ?_ ?_ <;> simp [W, δ] <;> nlinarith
  · refine band 132 ?_ ?_ <;> simp [W, δ] <;> nlinarith
  · refine band 158 ?_ ?_ <;> simp [W, δ] <;> nlinarith
  · refine band 185 ?_ ?_ <;> simp [W, δ] <;> nlinarith

/-! ## r1 — rational time, one difference exactly on the threshold -/

/-- **r1 is lonely at `t = 71/8`**; at difference `7` the distance is exactly `1/8`. -/
theorem r1_lonely : ∀ j : Fin 8, j ≠ 0 →
    (8 : ℝ)⁻¹ ≤ circDist ((W j - W 0) * (71 / 8)) := by
  obtain ⟨hs, hlo, hhi⟩ := sqrt2_facts
  intro j hj
  fin_cases j
  · simp at hj
  · refine band 0 ?_ ?_ <;> simp [W, δ] <;> nlinarith
  · refine band 17 ?_ ?_ <;> norm_num [W]
  · refine band 26 ?_ ?_ <;> norm_num [W]
  · refine band 35 ?_ ?_ <;> norm_num [W]
  · refine band 44 ?_ ?_ <;> norm_num [W]
  · refine band 53 ?_ ?_ <;> norm_num [W]
  · refine band 62 ?_ ?_ <;> norm_num [W]

/-! ## r3 … r8 — Theorem 4.8 -/

theorem others_lonely : ∀ i : Fin 8, 2 ≤ i.val → ∀ j : Fin 8, j ≠ i →
    (8 : ℝ)⁻¹ ≤ circDist ((W j - W i) * (1 / (8 * 1))) := by
  obtain ⟨hs, hlo, hhi⟩ := sqrt2_facts
  have hδ0 : 0 < δ := by unfold δ; positivity
  have hδ1 : δ < 1 / 10 := by unfold δ; nlinarith
  intro i hi j hj
  apply clear_of_ratio one_pos <;>
  fin_cases i <;> fin_cases j <;> simp_all [W] <;> norm_num <;>
  (rw [abs_of_neg (by linarith)]; linarith)

end IrrationalCascade
