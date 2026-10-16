import LonelyRunner.LRC.Spec.OrderSixSixRestN

/-!
# §5 natively: the pair window at the explicit lap `j₀`, and the pair-window fold (n6_native, E105)

§5: `D = v₃ − v₂ ∣ v₁`, `3v₁ < v₃`. Runners 2 and 3 on one lap `j` are clear together on
`P_j = [(j+1/6)/v₂, (j+5/6)/v₃]`. `j₀` is the first lap with runner 1 past `1/6` at the start of `P_j`
(`v₂ ≤ v₁(6j₀+1) < v₂ + 6v₁`); then runner 1 is clear across all of `P_{j₀}` (`3v₁ < v₃` alone), and runners 4, 5 are
folded by `window_two_uniform` when `P_{j₀}` is at least `2/(3v₄)` (`s5_uniform_j0`). `s5_pair_fold`: any sub-window
of `P_j` where runners 1 and 4 are in bands and which runner 5 sweeps for a third of a lap.
-/

namespace LRC.S6Native
open LRC.S7Native LRC.S8Native

/-- The first lap `j₀` with runner 1 past `1/6` at the start of `P_j`. -/
theorem exists_j0 {v1 v2 : ℕ} (h1 : 0 < v1) : ∃ j0 : ℕ, v2 ≤ v1 * (6 * j0 + 1) ∧ v1 * (6 * j0 + 1) < v2 + 6 * v1 := by
  have hex : ∃ j : ℕ, v2 ≤ v1 * (6 * j + 1) := ⟨v2, by nlinarith⟩
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h]; omega
  · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push Not at hmin
    have e : 6 * Nat.find hex + 1 = (6 * (Nat.find hex - 1) + 1) + 6 := by omega
    rw [e, mul_add]; omega

/-- **§5, the uniform pair window at `j₀`.** -/
theorem s5_uniform_j0 {v1 v2 v3 v4 v5 j0 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 ≤ v5)
    (hsmall : 3 * v1 < v3) (hj0a : v2 ≤ v1 * (6 * j0 + 1)) (hj0b : v1 * (6 * j0 + 1) < v2 + 6 * v1)
    (hw : 2 / (3 * (v4 : ℝ)) ≤ ((j0 : ℝ) + 5 / 6) / v3 - ((j0 : ℝ) + 1 / 6) / v2) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have h1R : (0 : ℝ) < v1 := by exact_mod_cast h0
  have h2 : 0 < v2 := by omega
  have h2R : (0 : ℝ) < v2 := by exact_mod_cast h2
  have h3R : (0 : ℝ) < v3 := by exact_mod_cast (show 0 < v3 by omega)
  have h4R : (0 : ℝ) < v4 := by exact_mod_cast (show 0 < v4 by omega)
  refine s5_pair_window (j := (j0 : ℤ)) (m := 0) (by positivity) h1R h2R (by exact_mod_cast h23.le) h4R
    (by exact_mod_cast h45) (by push_cast; exact le_refl _) (by push_cast; exact le_refl _) ?_ ?_ (by push_cast; linarith)
  · push_cast
    rw [div_le_div_iff₀ h1R h2R]
    have : (v2 : ℝ) ≤ v1 * (6 * j0 + 1) := by exact_mod_cast hj0a
    nlinarith
  · push_cast
    rw [div_le_div_iff₀ h3R h1R]
    have hb : (v1 : ℝ) * (6 * j0 + 1) < v2 + 6 * v1 := by exact_mod_cast hj0b
    have hs : 3 * (v1 : ℝ) < v3 := by exact_mod_cast hsmall
    have h23R : (v2 : ℝ) < v3 := by exact_mod_cast h23
    nlinarith

/-- **§5, the pair-window fold.** On a sub-window `[a, b]` of `P_j` where runner 1 (lap `n₁`) and runner 4 (lap `m`)
read in their bands at both ends, runner 5 is folded if `b − a ≥ 1/(3v₅)`. -/
theorem s5_pair_fold {v1 v2 v3 v4 v5 a b : ℝ} {j n1 m : ℤ} (hj : 0 ≤ j) (h1 : 0 < v1) (h2 : 0 < v2) (h23 : v2 ≤ v3)
    (h4 : 0 < v4) (h5 : 0 < v5)
    (ha2 : ((j : ℝ) + 1 / 6) / v2 ≤ a) (hb3 : b ≤ ((j : ℝ) + 5 / 6) / v3)
    (ha1 : (n1 : ℝ) + 1 / 6 ≤ v1 * a) (hb1 : v1 * b ≤ n1 + 5 / 6)
    (ha4 : (m : ℝ) + 1 / 6 ≤ v4 * a) (hb4 : v4 * b ≤ m + 5 / 6)
    (hlen : 1 / (3 * v5) ≤ b - a) :
    ∃ t : ℝ, (6 : ℝ)⁻¹ ≤ circDist (v1 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v2 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v3 * t) ∧
      (6 : ℝ)⁻¹ ≤ circDist (v4 * t) ∧ (6 : ℝ)⁻¹ ≤ circDist (v5 * t) := by
  have h3 : 0 < v3 := lt_of_lt_of_le h2 h23
  have hjR : (0 : ℝ) ≤ j := by exact_mod_cast hj
  obtain ⟨t, ht1, ht2, c5⟩ := fold_one (J₀ := a) (ℓ := b - a) h5 hlen
  have htb : t ≤ b := by linarith
  rw [div_le_iff₀ h2] at ha2; rw [le_div_iff₀ h3] at hb3
  have ht0 : 0 ≤ t := by nlinarith
  refine ⟨t, ?_, ?_, ?_, ?_, c5⟩
  · apply clear_of_band (p := n1) <;> nlinarith
  · apply clear_of_band (p := j) <;> nlinarith
  · apply clear_of_band (p := j) <;> nlinarith
  · apply clear_of_band (p := m) <;> nlinarith

end LRC.S6Native

#print axioms LRC.S6Native.exists_j0
#print axioms LRC.S6Native.s5_uniform_j0
#print axioms LRC.S6Native.s5_pair_fold
