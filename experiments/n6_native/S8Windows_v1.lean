import LonelyRunner.LRC.Spec.OrderSixSecSevenNativeN

/-!
# BHK §8 by slow-block windows (n6_native, E82; candidate 1 of `FORMAL_RETHINK_v1.md`)

Runners with speeds in `[v₁, V]` are clear across `[1/(6 v₁), 5/(6 V)]` (all on lap 0). Two closures:

* `s8_block3_window`: runners 1–3 make the block (`v₃ ≤ 5 v₁`); runners 4, 5 are closed by `window_two_uniform`
  when the block's window has length at least `2/(3 v₄)`, i.e. `4 v₁ v₃ ≤ v₄ (5 v₁ − v₃)`.
* `s8_block4_fold`: runners 1–4 make the block (`v₄ ≤ 5 v₁`); runner 5 alone sweeps at least a third of a lap across
  the window when `2 v₁ v₄ ≤ v₅ (5 v₁ − v₄)`, so it meets the band (`fold_one`).

These are first-window statements; E82 records which §8 sets they close.
-/

namespace N6Native
open LRC.S7Native

/-- A block of speeds in `[v₁, V]`, `V ≤ 5 v₁`: each is clear on `[1/(6 v₁), 5/(6 V)]`. -/
theorem block_clear {v₁ V v t : ℝ} (h1 : 0 < v₁) (hlo : v₁ ≤ v) (hhi : v ≤ V)
    (ht1 : 1 / (6 * v₁) ≤ t) (ht2 : t ≤ 5 / (6 * V)) : (6 : ℝ)⁻¹ ≤ circDist (v * t) := by
  have hv : 0 < v := lt_of_lt_of_le h1 hlo
  have hV : 0 < V := lt_of_lt_of_le hv hhi
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  apply clear_of_band (p := 0)
  · rw [Int.cast_zero, zero_add]
    rw [div_le_iff₀ (by positivity)] at ht1
    nlinarith
  · rw [Int.cast_zero, zero_add]
    rw [le_div_iff₀ (by positivity)] at ht2
    nlinarith

/-- **One runner folded through a window.** A runner whose reading sweeps at least a third of a lap across
`[J₀, J₀ + ℓ]` meets the band there. -/
theorem fold_one {b J₀ ℓ : ℝ} (hb : 0 < b) (hℓ : 1 / (3 * b) ≤ ℓ) :
    ∃ t : ℝ, J₀ ≤ t ∧ t ≤ J₀ + ℓ ∧ (6 : ℝ)⁻¹ ≤ circDist (b * t) := by
  set y := b * J₀ with hy
  set f := Int.fract y with hf
  have hf0 : 0 ≤ f := Int.fract_nonneg y
  have hf1 : f < 1 := Int.fract_lt_one y
  have hyf : y = (⌊y⌋ : ℝ) + f := by rw [hf]; exact (Int.floor_add_fract y).symm
  have hℓ' : 1 / 3 ≤ b * ℓ := by rw [div_le_iff₀ (by positivity)] at hℓ; linarith
  by_cases hmid : 1 / 6 ≤ f ∧ f ≤ 5 / 6
  · refine ⟨J₀, le_rfl, by nlinarith [hℓ'], ?_⟩
    apply clear_of_band (p := ⌊y⌋) <;> [linarith [hmid.1]; linarith [hmid.2]]
  · push Not at hmid
    by_cases hlow : f < 1 / 6
    · refine ⟨J₀ + (1 / 6 - f) / b, by have : 0 ≤ (1 / 6 - f) / b := div_nonneg (by linarith) hb.le; linarith, ?_, ?_⟩
      · have : (1 / 6 - f) / b ≤ ℓ := by rw [div_le_iff₀ hb]; nlinarith
        linarith
      · apply clear_of_band (p := ⌊y⌋)
        · rw [mul_add, mul_div_cancel₀ _ hb.ne', ← hy]; linarith
        · rw [mul_add, mul_div_cancel₀ _ hb.ne', ← hy]; linarith
    · push Not at hlow
      have hhi : 5 / 6 < f := hmid hlow
      refine ⟨J₀ + (7 / 6 - f) / b, by have : 0 ≤ (7 / 6 - f) / b := div_nonneg (by linarith) hb.le; linarith, ?_, ?_⟩
      · have : (7 / 6 - f) / b ≤ ℓ := by rw [div_le_iff₀ hb]; nlinarith
        linarith
      · apply clear_of_band (p := ⌊y⌋ + 1)
        · push_cast; rw [mul_add, mul_div_cancel₀ _ hb.ne', ← hy]; linarith
        · push_cast; rw [mul_add, mul_div_cancel₀ _ hb.ne', ← hy]; linarith

/-- **Three-runner block, two folded by the window lemma.** -/
theorem s8_block3_window {v₁ v₂ v₃ v₄ v₅ : ℝ} (h1 : 0 < v₁) (h12 : v₁ ≤ v₂) (h23 : v₂ ≤ v₃)
    (h45 : v₄ ≤ v₅) (h34 : v₃ ≤ v₄) (hw : 4 * v₁ * v₃ ≤ v₄ * (5 * v₁ - v₃)) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v₁ * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₂ * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₃ * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v₄ * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₅ * t) := by
  have hv3 : 0 < v₃ := by linarith
  have hv4 : 0 < v₄ := by linarith
  have h5 : v₃ < 5 * v₁ := by nlinarith
  set ℓ := 5 / (6 * v₃) - 1 / (6 * v₁) with hℓ
  have hlen : 2 / (3 * v₄) ≤ ℓ := by
    rw [hℓ, div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  obtain ⟨t, ht1, ht2, c4, c5⟩ := window_two_uniform (J₀ := 1 / (6 * v₁)) hv4 h45 hlen
  have ht2' : t ≤ 5 / (6 * v₃) := by rw [hℓ] at ht2; linarith
  exact ⟨t, block_clear h1 le_rfl (by linarith) ht1 ht2', block_clear h1 h12 h23 ht1 ht2',
    block_clear h1 (by linarith) le_rfl ht1 ht2', c4, c5⟩

/-- **Four-runner block, runner 5 folded alone.** -/
theorem s8_block4_fold {v₁ v₂ v₃ v₄ v₅ : ℝ} (h1 : 0 < v₁) (h12 : v₁ ≤ v₂) (h23 : v₂ ≤ v₃) (h34 : v₃ ≤ v₄)
    (h45 : v₄ ≤ v₅) (hw : 2 * v₁ * v₄ ≤ v₅ * (5 * v₁ - v₄)) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v₁ * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₂ * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₃ * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v₄ * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v₅ * t) := by
  have hv4 : 0 < v₄ := by linarith
  have hv5 : 0 < v₅ := by linarith
  set ℓ := 5 / (6 * v₄) - 1 / (6 * v₁) with hℓ
  have hlen : 1 / (3 * v₅) ≤ ℓ := by
    rw [hℓ, div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  obtain ⟨t, ht1, ht2, c5⟩ := fold_one (J₀ := 1 / (6 * v₁)) hv5 hlen
  have ht2' : t ≤ 5 / (6 * v₄) := by rw [hℓ] at ht2; linarith
  exact ⟨t, block_clear h1 le_rfl (by linarith) ht1 ht2', block_clear h1 h12 (by linarith) ht1 ht2',
    block_clear h1 (by linarith) h34 ht1 ht2', block_clear h1 (by linarith) le_rfl ht1 ht2', c5⟩

end N6Native

#print axioms N6Native.s8_block3_window
#print axioms N6Native.s8_block4_fold
