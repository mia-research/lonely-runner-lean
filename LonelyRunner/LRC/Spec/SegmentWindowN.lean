import LonelyRunner.LRC.Spec.OneFreeN

/-!
# The window along a one-mover segment

2026-10-02 (running log E296).  `OneFreeN.lonely_of_one_free_eight` shows that along a move of one runner every arrangement
off the lattice (`(v i − v k)·P` not whole) is lonely, at `t₇ + m·P` with `m` a step count.  This file exposes the
bound on `m`: it is `1/(4a) + 1`, `a = ‖(v i − v k)·P‖`.  Hence a window `[c, T]` holds on every part of a segment where
`a` stays above a positive `a₀`, with `T = t₇ + P(1/(4a₀) + 1)`, `t₇` fixed by the six other readings alone.

The bound is sharp in kind: `T → ∞` as `a → 0`, so the window is not uniform at a lattice point, and a segment has
finitely many of them.  Nothing here says anything at a lattice point.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.SegmentWindow

open Arrangement LRC.OneFree

theorem circDist_pos_of_not_int {α : ℝ} (hα : ∀ z : ℤ, α ≠ z) : 0 < circDist α := by
  obtain ⟨z, hz⟩ := exists_near_int α
  rcases (circDist.nonneg α).lt_or_eq with h | h
  · exact h
  · exfalso; apply hα z
    have : |α - z| = 0 := by rw [hz]; exact h.symm
    linarith [abs_eq_zero.mp this]

/-- `exists_far_multiple`, with the step count bounded. -/
theorem exists_far_multiple_bounded {α : ℝ} (hα : ∀ z : ℤ, α ≠ z) :
    ∃ m : ℕ, (m : ℝ) ≤ 1 / (4 * circDist α) + 1 ∧ (1 : ℝ) / 4 ≤ circDist (m * α) := by
  obtain ⟨z, hz⟩ := exists_near_int α
  set a := circDist α with ha
  have ha0 : 0 < a := circDist_pos_of_not_int hα
  have hahalf : a ≤ 1 / 2 := circDist.le_half α
  set r := α - z with hr
  have hm : ∀ m : ℕ, circDist (m * α) = circDist (m * r) := by
    intro m
    have e : (m : ℝ) * α = m * r + ((m * z : ℤ) : ℝ) := by rw [hr]; push_cast; ring
    rw [e, LRC.PinchOpen.circDist_add_int_po]
  rcases le_or_gt ((1 : ℝ) / 4) a with h4 | h4
  · refine ⟨1, ?_, ?_⟩
    · have : 0 ≤ 1 / (4 * a) := by positivity
      norm_num; linarith
    · rw [hm, Nat.cast_one, one_mul, circDist_eq_abs (by rw [hz]; exact hahalf), hz]; exact h4
  · set m : ℕ := ⌈1 / (4 * a)⌉₊ with hmdef
    have hc1 : 1 / (4 * a) ≤ (m : ℝ) := Nat.le_ceil _
    have hc2 : (m : ℝ) < 1 / (4 * a) + 1 := Nat.ceil_lt_add_one (by positivity)
    have hma1 : (1 : ℝ) / 4 ≤ m * a := by
      have := mul_le_mul_of_nonneg_right hc1 ha0.le
      have e : 1 / (4 * a) * a = 1 / 4 := by field_simp
      linarith
    have hma2 : (m : ℝ) * a < 1 / 2 := by
      have := mul_lt_mul_of_pos_right hc2 ha0
      have e : (1 / (4 * a) + 1) * a = 1 / 4 + a := by field_simp
      rw [e] at this; linarith
    have habs : |(m : ℝ) * r| = m * a := by
      rw [abs_mul, Nat.abs_cast, hz]
    refine ⟨m, hc2.le, ?_⟩
    rw [hm, circDist_eq_abs (by rw [habs]; linarith), habs]; exact hma1

/-- `exists_clear_step`, with the step count bounded. -/
theorem exists_clear_step_bounded (θ : ℝ) {α : ℝ} (hα : ∀ z : ℤ, α ≠ z) :
    ∃ m : ℕ, (m : ℝ) ≤ 1 / (4 * circDist α) + 1 ∧ (8 : ℝ)⁻¹ ≤ circDist (θ + m * α) := by
  have ha0 := circDist_pos_of_not_int hα
  rcases le_or_gt (8 : ℝ)⁻¹ (circDist θ) with h | h
  · refine ⟨0, ?_, by simpa using h⟩
    have : 0 ≤ 1 / (4 * circDist α) := by positivity
    rw [Nat.cast_zero]; linarith
  · obtain ⟨m, hmb, hm⟩ := exists_far_multiple_bounded hα
    refine ⟨m, hmb, ?_⟩
    have := circDist_sub_le θ (m * α)
    linarith

/-- **The one-mover window.**  Six readings of common period `P` (every reading other than the mover's is a whole
multiple of `1/P` from the subject) fix an instant `t₇ > 0` at which order seven clears them.  For every reading `x` of the
mover with `(x)·P` not whole, the arrangement with the mover at `x` is lonely at an instant `t ≤ t₇ + P(1/(4a) + 1)`,
`a = ‖x·P‖`.  `t₇` does not depend on `x`. -/
theorem lonely_window_of_one_free {v : Fin 8 → ℝ} {k i : Fin 8} (hki : k ≠ i)
    (hpos : ∀ j : Fin 8, j ≠ k → 0 < v j - v k) {P : ℝ} (hP : 0 < P)
    (hper : ∀ j : Fin 8, j ≠ i → ∃ z : ℤ, (v j - v k) * P = z) :
    ∃ t7 : ℝ, 0 < t7 ∧ ∀ x : ℝ, 0 < x → (∀ z : ℤ, x * P ≠ z) →
      ∃ t : ℝ, 0 < t ∧ t ≤ t7 + P * (1 / (4 * circDist (x * P)) + 1) ∧
        LonelyAt (Function.update v i (v k + x)) k t := by
  classical
  set S : Finset (Fin 8) := (Finset.univ.erase k).erase i with hS
  set ds : Finset ℝ := S.image (fun j => v j - v k) with hds
  have hSmem : ∀ j, j ∈ S ↔ j ≠ i ∧ j ≠ k := by
    intro j; simp [hS]
  have hcardS : S.card = 6 := by
    rw [hS, Finset.card_erase_of_mem (by simp [Ne.symm hki]), Finset.card_erase_of_mem (Finset.mem_univ k)]
    simp
  have hcard : ds.card ≤ 7 - 1 := by
    have := Finset.card_image_le (s := S) (f := fun j => v j - v k)
    rw [hcardS] at this; simpa using this
  have hdpos : ∀ d ∈ ds, 0 < d := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
    exact hpos j ((hSmem j).mp hj).2
  obtain ⟨t7, ht7, hl7⟩ := LRC.OrderSevenN.existenceAtN_seven ds hdpos hcard
  refine ⟨t7, ht7, fun x hx hfree => ?_⟩
  obtain ⟨m, hmb, hm⟩ := exists_clear_step_bounded (x * t7) hfree
  refine ⟨t7 + m * P, by positivity, ?_, fun j hjk => ?_⟩
  · have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have : (m : ℝ) * P ≤ P * (1 / (4 * circDist (x * P)) + 1) := by
      rw [mul_comm P]; exact mul_le_mul_of_nonneg_right hmb hP.le
    linarith
  · rw [sep_eq]
    by_cases hji : j = i
    · subst hji
      simp only [Function.update_self, Function.update_of_ne hki]
      rw [show v k + x - v k = x by ring]
      have e : x * (t7 + m * P) = x * t7 + m * (x * P) := by ring
      rw [e]; exact hm
    · simp only [Function.update_of_ne hji, Function.update_of_ne hki]
      obtain ⟨z, hz⟩ := hper j hji
      have e : (v j - v k) * (t7 + m * P) = (v j - v k) * t7 + ((m * z : ℤ) : ℝ) := by
        push_cast; rw [← hz]; ring
      rw [e, LRC.PinchOpen.circDist_add_int_po]
      have hmem : v j - v k ∈ ds := Finset.mem_image.mpr ⟨j, (hSmem j).mpr ⟨hji, hjk⟩, rfl⟩
      have h7 := hl7 _ hmem
      have : ((7 : ℕ) : ℝ)⁻¹ ≥ (8 : ℝ)⁻¹ := by norm_num
      linarith

end LRC.SegmentWindow
