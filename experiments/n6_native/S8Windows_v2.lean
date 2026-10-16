import LonelyRunner.LRC.Spec.OrderSixSecSevenNativeN

/-!
# BHK §8 by slow-block windows, any laps; lap boxes (n6_native, E83)

Versioned successor of `S8Windows_v1.lean` (kept): the window statements with the laps of the block as parameters,
so the later windows (laps `(1,2,3)`, `(0,1,1)`, `(0,0,1)`, …) are instances, and the five-runner lap box.

* `block3_window_laps`: runners 1–3 on laps `m₁, m₂, m₃` all clear on `[L, U]`; runners 4, 5 by `lonely_of_window`
  (`window_two`'s length and residue conditions).
* `block4_fold_laps`: runners 1–4 clear on `[L, U]`; runner 5 folded alone when `v₅ (U − L) ≥ 1/3`.
* `box5`: the lap box for five runners (`lap_box_lonely`, re-proved here for `Fin 5` with the latest entry).
-/

namespace N6Native
open LRC.S7Native

/-- A runner whose reading lies in `[m + 1/6, m + 5/6]` at both ends of `[L, U]` is clear across it. -/
theorem clear_on_lap {v m L U t : ℝ} (hv : 0 < v) (hL : m + 1 / 6 ≤ v * L) (hU : v * U ≤ m + 5 / 6)
    (ht1 : L ≤ t) (ht2 : t ≤ U) (p : ℤ) (hp : (p : ℝ) = m) : (6 : ℝ)⁻¹ ≤ circDist (v * t) := by
  apply clear_of_band (p := p) <;> rw [hp] <;> nlinarith

/-- **Three-runner block on given laps, runners 4 and 5 by the window lemma.** -/
theorem block3_window_laps {v₁ v₂ v₃ v₄ v₅ L U : ℝ} {p₁ p₂ p₃ : ℤ}
    (h1 : 0 < v₁) (h2 : 0 < v₂) (h3 : 0 < v₃) (h4 : 0 < v₄) (h45 : v₄ ≤ v₅)
    (a1 : (p₁ : ℝ) + 1 / 6 ≤ v₁ * L) (b1 : v₁ * U ≤ (p₁ : ℝ) + 5 / 6)
    (a2 : (p₂ : ℝ) + 1 / 6 ≤ v₂ * L) (b2 : v₂ * U ≤ (p₂ : ℝ) + 5 / 6)
    (a3 : (p₃ : ℝ) + 1 / 6 ≤ v₃ * L) (b3 : v₃ * U ≤ (p₃ : ℝ) + 5 / 6)
    (hbase : 1 / (3 * v₄) + 1 / (3 * v₅) ≤ U - L)
    (hres : ∀ m : ℤ, 3 * (m : ℝ) * v₄ < v₄ + v₅ → ((m : ℝ) + 1 / 3) / v₅ ≤ U - L) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v₁ * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₂ * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₃ * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v₄ * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₅ * t) := by
  refine lonely_of_window (J₀ := L) (ℓ := U - L) h4 h45 (fun t ht1 ht2 => ?_) hbase hres
  have ht2' : t ≤ U := by linarith
  exact ⟨clear_on_lap h1 a1 b1 ht1 ht2' p₁ rfl, clear_on_lap h2 a2 b2 ht1 ht2' p₂ rfl,
    clear_on_lap h3 a3 b3 ht1 ht2' p₃ rfl⟩

/-- **Four-runner block on given laps, runner 5 folded alone.** -/
theorem block4_fold_laps {v₁ v₂ v₃ v₄ v₅ L U : ℝ} {p₁ p₂ p₃ p₄ : ℤ}
    (h1 : 0 < v₁) (h2 : 0 < v₂) (h3 : 0 < v₃) (h4 : 0 < v₄) (h5 : 0 < v₅)
    (a1 : (p₁ : ℝ) + 1 / 6 ≤ v₁ * L) (b1 : v₁ * U ≤ (p₁ : ℝ) + 5 / 6)
    (a2 : (p₂ : ℝ) + 1 / 6 ≤ v₂ * L) (b2 : v₂ * U ≤ (p₂ : ℝ) + 5 / 6)
    (a3 : (p₃ : ℝ) + 1 / 6 ≤ v₃ * L) (b3 : v₃ * U ≤ (p₃ : ℝ) + 5 / 6)
    (a4 : (p₄ : ℝ) + 1 / 6 ≤ v₄ * L) (b4 : v₄ * U ≤ (p₄ : ℝ) + 5 / 6)
    (hfold : 1 / 3 ≤ v₅ * (U - L)) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v₁ * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₂ * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₃ * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v₄ * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₅ * t) := by
  have hℓ : 1 / (3 * v₅) ≤ U - L := by rw [div_le_iff₀ (by positivity)]; linarith
  -- fold one runner through [L, L + (U − L)] (the argument of `S8Windows_v1.fold_one`)
  set y := v₅ * L with hy
  set f := Int.fract y with hf
  have hf0 : 0 ≤ f := Int.fract_nonneg y
  have hf1 : f < 1 := Int.fract_lt_one y
  have hyf : y = (⌊y⌋ : ℝ) + f := by rw [hf]; exact (Int.floor_add_fract y).symm
  obtain ⟨t, ht1, ht2, c5⟩ : ∃ t : ℝ, L ≤ t ∧ t ≤ U ∧ (6 : ℝ)⁻¹ ≤ circDist (v₅ * t) := by
    by_cases hmid : 1 / 6 ≤ f ∧ f ≤ 5 / 6
    · refine ⟨L, le_rfl, by nlinarith, ?_⟩
      apply clear_of_band (p := ⌊y⌋) <;> [linarith [hmid.1]; linarith [hmid.2]]
    · push Not at hmid
      by_cases hlow : f < 1 / 6
      · refine ⟨L + (1 / 6 - f) / v₅, by have : 0 ≤ (1 / 6 - f) / v₅ := div_nonneg (by linarith) h5.le; linarith, ?_, ?_⟩
        · have : (1 / 6 - f) / v₅ ≤ U - L := by rw [div_le_iff₀ h5]; nlinarith
          linarith
        · apply clear_of_band (p := ⌊y⌋)
          · rw [mul_add, mul_div_cancel₀ _ h5.ne', ← hy]; linarith
          · rw [mul_add, mul_div_cancel₀ _ h5.ne', ← hy]; linarith
      · push Not at hlow
        have hhi : 5 / 6 < f := hmid hlow
        refine ⟨L + (7 / 6 - f) / v₅, by have : 0 ≤ (7 / 6 - f) / v₅ := div_nonneg (by linarith) h5.le; linarith, ?_, ?_⟩
        · have : (7 / 6 - f) / v₅ ≤ U - L := by rw [div_le_iff₀ h5]; nlinarith
          linarith
        · apply clear_of_band (p := ⌊y⌋ + 1)
          · push_cast; rw [mul_add, mul_div_cancel₀ _ h5.ne', ← hy]; linarith
          · push_cast; rw [mul_add, mul_div_cancel₀ _ h5.ne', ← hy]; linarith
  exact ⟨t, clear_on_lap h1 a1 b1 ht1 ht2 p₁ rfl, clear_on_lap h2 a2 b2 ht1 ht2 p₂ rfl,
    clear_on_lap h3 a3 b3 ht1 ht2 p₃ rfl, clear_on_lap h4 a4 b4 ht1 ht2 p₄ rfl, c5⟩

/-- **The lap box for five runners.** Laps `k i ≥ 0`; if every ordered pair has `(6 k_i + 1) d_j ≤ (6 k_j + 5) d_i`,
the latest band entry is lonely. -/
theorem box5 (d : Fin 5 → ℝ) (k : Fin 5 → ℕ) (hd : ∀ i, 0 < d i)
    (h : ∀ i j, (6 * (k i : ℝ) + 1) * d j ≤ (6 * (k j : ℝ) + 5) * d i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, (6 : ℝ)⁻¹ ≤ circDist (d i * t) := by
  set l : Fin 5 → ℝ := fun i => (6 * (k i : ℝ) + 1) / (6 * d i) with hl
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ l Finset.univ_nonempty
  refine ⟨l i₀, by simp only [hl]; have := hd i₀; positivity, fun i => ?_⟩
  have hdi := hd i
  have lo : (k i : ℝ) + 1 / 6 ≤ d i * l i₀ := by
    have := hi₀ i (Finset.mem_univ _); simp only [hl] at this ⊢
    rw [div_le_div_iff₀ (by positivity) (by have := hd i₀; positivity)] at this
    rw [mul_div_assoc', le_div_iff₀ (by have := hd i₀; positivity)]; nlinarith
  have hi : d i * l i₀ ≤ (k i : ℝ) + 5 / 6 := by
    have := h i₀ i; simp only [hl]
    rw [mul_div_assoc', div_le_iff₀ (by have := hd i₀; positivity)]; nlinarith
  exact clear_of_band (p := (k i : ℤ)) (by push_cast; linarith) (by push_cast; linarith)

end N6Native

#print axioms N6Native.block3_window_laps
#print axioms N6Native.block4_fold_laps
#print axioms N6Native.box5
