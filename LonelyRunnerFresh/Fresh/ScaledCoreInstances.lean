import Mathlib
import Fresh.ScaledCoreScale
import Fresh.ScaledCoreRealA
import Fresh.ScaledCoreRealB

/-!
# Scaled cores with one real extra reading: the survivors of the N = 44 search covered by this

Written 2026-10-29.  New file.  Each theorem combines `Fresh.ScaledCoreScale.scale` with a generated `real_core_<core>` (the core together with ANY real positive reading is lonely at `1/8`, certified by the kernel-checked chain `coreOK`; **[PROVISIONAL: covering]**).
`x` is any positive real, so every whole-number last reading of the survivor sets `(2,10,12,14,16,26,x)`, `(2,12,14,16,18,30,x)`, `(3,15,18,21,24,33,x)` and `(3,15,18,21,24,39,x)` is covered, and so are all of their non-integer analogues.  Grade [L].
-/

namespace Fresh.ScaledCoreInstances

open Fresh Fresh.ScaledCoreChain

theorem times2_1_5_6_7_8_13 {x : ℝ} (hx : 0 < x) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ coreSet [1, 5, 6, 7, 8, 13], (1 / 8 : ℝ) ≤ distInt ((2 * s) * t)) ∧ (1 / 8 : ℝ) ≤ distInt (x * t) :=
  Fresh.ScaledCoreScale.scale (fun y hy => Fresh.ScaledCoreRealA.real_core_1_5_6_7_8_13 hy) (by norm_num) hx

theorem times3_1_5_6_7_8_13 {x : ℝ} (hx : 0 < x) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ coreSet [1, 5, 6, 7, 8, 13], (1 / 8 : ℝ) ≤ distInt ((3 * s) * t)) ∧ (1 / 8 : ℝ) ≤ distInt (x * t) :=
  Fresh.ScaledCoreScale.scale (fun y hy => Fresh.ScaledCoreRealA.real_core_1_5_6_7_8_13 hy) (by norm_num) hx

theorem times2_1_6_7_8_9_15 {x : ℝ} (hx : 0 < x) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ coreSet [1, 6, 7, 8, 9, 15], (1 / 8 : ℝ) ≤ distInt ((2 * s) * t)) ∧ (1 / 8 : ℝ) ≤ distInt (x * t) :=
  Fresh.ScaledCoreScale.scale (fun y hy => Fresh.ScaledCoreRealB.real_core_1_6_7_8_9_15 hy) (by norm_num) hx

theorem times3_1_5_6_7_8_11 {x : ℝ} (hx : 0 < x) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ coreSet [1, 5, 6, 7, 8, 11], (1 / 8 : ℝ) ≤ distInt ((3 * s) * t)) ∧ (1 / 8 : ℝ) ≤ distInt (x * t) :=
  Fresh.ScaledCoreScale.scale (fun y hy => Fresh.ScaledCoreRealA.real_core_1_5_6_7_8_11 hy) (by norm_num) hx

/-- The survivor family `(2, 10, 12, 14, 16, 26, x)` stated on the readings themselves. -/
theorem survivor_2_10_12_14_16_26 {x : ℝ} (hx : 0 < x) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ ({2, 10, 12, 14, 16, 26} : Finset ℝ), (1 / 8 : ℝ) ≤ distInt (s * t)) ∧ (1 / 8 : ℝ) ≤ distInt (x * t) := by
  obtain ⟨t, ht, hS, hx'⟩ := times2_1_5_6_7_8_13 hx
  refine ⟨t, ht, fun s hs => ?_, hx'⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · have := hS 1 (by simp [coreSet]); norm_num at this ⊢; exact this
  · have := hS 5 (by simp [coreSet]); norm_num at this ⊢; exact this
  · have := hS 6 (by simp [coreSet]); norm_num at this ⊢; exact this
  · have := hS 7 (by simp [coreSet]); norm_num at this ⊢; exact this
  · have := hS 8 (by simp [coreSet]); norm_num at this ⊢; exact this
  · have := hS 13 (by simp [coreSet]); norm_num at this ⊢; exact this

#print axioms survivor_2_10_12_14_16_26

end Fresh.ScaledCoreInstances
