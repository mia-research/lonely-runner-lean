import LonelyRunner.LRC.Spec.OrderSixWholeN
import LonelyRunner.LRC.Spec.MirrorCentreN

/-!
# Order eight: the fast pair, a separation-of-scale rule

2026-09-25.  R8 carries a single fast runner on top of order seven.  This file carries a fast
**pair** on top of order six.

* **Two runners in a window** (`pair_window`).  For `0 < a ≤ b`, every closed window of length
  `3/(4a)` holds an instant at which both `a` and `b` are clear at `1/8`.  In `a`'s coordinate the
  window has length `3/4`, and it contains a quarter-length stretch inside one clear band
  (`exists_quarter_band`).  Across that stretch `b` moves at least a quarter lap, and any quarter lap
  meets a clear band (`exists_band_point`).
* **The fast pair** (`lonely_eight_of_fast_pair`).  Let the core `C` (at most five, nonempty) have
  every element at most `m`, and let the pair satisfy `9m ≤ a ≤ b`.  Order six gives `τ` with every
  core reading at least `1/6`, and 1-Lipschitz `circDist` keeps each core runner clear at `1/8` on
  `[τ − δ, τ + δ]`, `δ = 1/(24m)`.  The window has length `1/(12m) ≥ 3/(4a)`, so the pair is clear at
  some instant inside it.  The instant is named: the window's start, the band point of `a`, and
  `b`'s band point, in that order.

Verified before formalising on 163 constructed `EightResidual` members without a large common factor
(`experiments/nN/fast_pair_window_v1.out`).  Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.FastPairEight

open LRC.MirrorCentre

/-- **Any quarter stretch meets a clear band.** -/
theorem exists_band_point (v : ℝ) :
    ∃ w : ℝ, v ≤ w ∧ w ≤ v + 1 / 4 ∧ ∃ m : ℤ, (m : ℝ) + 1 / 8 ≤ w ∧ w ≤ (m : ℝ) + 1 - 1 / 8 := by
  have hv := Int.floor_add_fract v
  have hf0 := Int.fract_nonneg v
  have hf1 := Int.fract_lt_one v
  by_cases h1 : Int.fract v < 1 / 8
  · exact ⟨(⌊v⌋ : ℝ) + 1 / 8, by linarith, by linarith, ⌊v⌋, le_refl _, by linarith⟩
  by_cases h2 : Int.fract v ≤ 7 / 8
  · exact ⟨v, le_refl _, by linarith, ⌊v⌋, by linarith, by linarith⟩
  · push_neg at h1 h2
    refine ⟨((⌊v⌋ + 1 : ℤ) : ℝ) + 1 / 8, ?_, ?_, ⌊v⌋ + 1, le_refl _, ?_⟩ <;> push_cast <;> linarith

/-- **A quarter-length clear stretch starts within half a lap.** -/
theorem exists_quarter_band (u : ℝ) :
    ∃ s : ℝ, u ≤ s ∧ s ≤ u + 1 / 2 ∧
      ∃ m : ℤ, (m : ℝ) + 1 / 8 ≤ s ∧ s + 1 / 4 ≤ (m : ℝ) + 1 - 1 / 8 := by
  have hv := Int.floor_add_fract u
  have hf0 := Int.fract_nonneg u
  have hf1 := Int.fract_lt_one u
  by_cases h1 : Int.fract u < 1 / 8
  · exact ⟨(⌊u⌋ : ℝ) + 1 / 8, by linarith, by linarith, ⌊u⌋, le_refl _, by linarith⟩
  by_cases h2 : Int.fract u ≤ 5 / 8
  · exact ⟨u, le_refl _, by linarith, ⌊u⌋, by linarith, by linarith⟩
  · push_neg at h1 h2
    refine ⟨((⌊u⌋ + 1 : ℤ) : ℝ) + 1 / 8, ?_, ?_, ⌊u⌋ + 1, le_refl _, ?_⟩ <;> push_cast <;> linarith

/-- **Two runners in a window.**  For `0 < a ≤ b`, the closed window `[x, x + 3/(4a)]` holds an
instant at which both are clear at `1/8`. -/
theorem pair_window {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x : ℝ) :
    ∃ t : ℝ, x ≤ t ∧ t ≤ x + 3 / (4 * a) ∧
      (8 : ℝ)⁻¹ ≤ circDist (a * t) ∧ (8 : ℝ)⁻¹ ≤ circDist (b * t) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h8 : (8 : ℝ)⁻¹ = 1 / 8 := by norm_num
  obtain ⟨s, hs1, hs2, m, hm1, hm2⟩ := exists_quarter_band (a * x)
  obtain ⟨w, hw1, hw2, m', hm1', hm2'⟩ := exists_band_point (b * (s / a))
  refine ⟨w / b, ?_, ?_, ?_, ?_⟩
  · -- x ≤ s/a ≤ w/b
    rw [le_div_iff₀ hb]
    have : x * a ≤ s := by linarith
    have hsa : x ≤ s / a := by rw [le_div_iff₀ ha]; linarith
    calc x * b ≤ (s / a) * b := mul_le_mul_of_nonneg_right hsa hb.le
      _ = b * (s / a) := by ring
      _ ≤ w := hw1
  · -- w/b ≤ s/a + 1/(4b) ≤ x + 1/(2a) + 1/(4a)
    have h1 : w / b ≤ s / a + 1 / (4 * b) := by
      rw [div_le_iff₀ hb]
      have : (s / a + 1 / (4 * b)) * b = b * (s / a) + 1 / 4 := by field_simp
      linarith
    have h2 : s / a ≤ x + 1 / (2 * a) := by
      rw [div_le_iff₀ ha]
      have : (x + 1 / (2 * a)) * a = a * x + 1 / 2 := by field_simp
      linarith
    have h3 : 1 / (4 * b) ≤ 1 / (4 * a) := one_div_le_one_div_of_le (by positivity) (by linarith)
    have h4 : x + 1 / (2 * a) + 1 / (4 * a) = x + 3 / (4 * a) := by field_simp; ring
    linarith
  · -- a·(w/b) lies in [s, s + 1/4], inside the band of m
    rw [h8]
    have hlo : s ≤ a * (w / b) := by
      have : a * (w / b) = (a / b) * w := by ring
      rw [this]
      have hw' : b * (s / a) ≤ w := hw1
      calc s = (a / b) * (b * (s / a)) := by field_simp
        _ ≤ (a / b) * w := mul_le_mul_of_nonneg_left hw' (by positivity)
    have hhi : a * (w / b) ≤ s + 1 / 4 := by
      have hab' : a / b ≤ 1 := (div_le_one hb).mpr hab
      have : a * (w / b) = (a / b) * w := by ring
      rw [this]
      calc (a / b) * w ≤ (a / b) * (b * (s / a) + 1 / 4) :=
            mul_le_mul_of_nonneg_left hw2 (by positivity)
        _ = s + (a / b) * (1 / 4) := by field_simp
        _ ≤ s + 1 / 4 := by nlinarith
    exact circDist_ge_of_window (m := m) (by linarith) (by linarith) (by norm_num)
  · rw [h8, show b * (w / b) = w by field_simp]
    exact circDist_ge_of_window (m := m') hm1' hm2' (by norm_num)

/-- `circDist x ≤ x` for `x ≥ 0`. -/
theorem circDist_le_self {x : ℝ} (hx : 0 ≤ x) : circDist x ≤ x := by
  unfold circDist
  have hfl : (0 : ℝ) ≤ ⌊x⌋ := by exact_mod_cast Int.floor_nonneg.mpr hx
  have := Int.floor_add_fract x
  exact le_trans (min_le_left _ _) (by linarith)

/-- **The fast pair.**  A nonempty core of at most five, every element at most `m`, lonely at `1/6`
by order six; a pair with `9m ≤ a ≤ b`.  Then all of them are clear at `1/8` at one instant. -/
theorem lonely_eight_of_fast_pair {C : Finset ℕ} (hpos : ∀ c ∈ C, 0 < c) (hcard : C.card ≤ 5)
    (hne : C.Nonempty) {m a b : ℕ} (hm : ∀ c ∈ C, c ≤ m) (hab : a ≤ b) (ha : 9 * m ≤ a) :
    ∃ t : ℝ, 0 < t ∧ (∀ c ∈ C, (8 : ℝ)⁻¹ ≤ circDist ((c : ℝ) * t)) ∧
      (8 : ℝ)⁻¹ ≤ circDist ((a : ℝ) * t) ∧ (8 : ℝ)⁻¹ ≤ circDist ((b : ℝ) * t) := by
  obtain ⟨τ, hτ, hl⟩ := LRC.OrderSixN.lonely_six_nat C hpos hcard
  obtain ⟨c0, hc0⟩ := hne
  have hc0pos : 0 < c0 := hpos c0 hc0
  have hmpos : 0 < m := lt_of_lt_of_le hc0pos (hm c0 hc0)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have haR : (9 : ℝ) * m ≤ a := by exact_mod_cast ha
  have haR0 : (0 : ℝ) < a := by linarith
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  set δ : ℝ := 1 / (24 * m) with hδ
  -- τ ≥ 1/(6m) > δ
  have hτm : 1 / (6 * m) ≤ τ := by
    have h1 : (6 : ℝ)⁻¹ ≤ (c0 : ℝ) * τ :=
      le_trans (hl c0 hc0) (circDist_le_self (by positivity))
    have h2 : (c0 : ℝ) ≤ m := by exact_mod_cast hm c0 hc0
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hδτ : δ < τ := by
    have : δ < 1 / (6 * m) := by
      rw [hδ]; exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith
  obtain ⟨t, ht1, ht2, hta, htb⟩ := pair_window haR0 habR (τ - δ)
  have hwin : 3 / (4 * (a : ℝ)) ≤ 2 * δ := by
    rw [hδ, div_le_iff₀ (by positivity)]
    have : 2 * (1 / (24 * (m : ℝ))) * (4 * a) = a / (3 * m) := by field_simp; ring
    rw [this, le_div_iff₀ (by positivity)]
    linarith
  refine ⟨t, by linarith, fun c hc => ?_, hta, htb⟩
  have hcR : (0 : ℝ) < c := by exact_mod_cast hpos c hc
  have hcm : (c : ℝ) ≤ m := by exact_mod_cast hm c hc
  have hdist : |(c : ℝ) * t - (c : ℝ) * τ| ≤ 1 / 24 := by
    rw [← mul_sub, abs_mul, abs_of_pos hcR]
    have hts : |t - τ| ≤ δ := by rw [abs_le]; constructor <;> linarith
    calc (c : ℝ) * |t - τ| ≤ m * δ := mul_le_mul hcm hts (abs_nonneg _) hmR.le
      _ = 1 / 24 := by rw [hδ]; field_simp
  have hlip := circDist_lipschitz.dist_le_mul ((c : ℝ) * t) ((c : ℝ) * τ)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
  have h6 := hl c hc
  have := (abs_sub_le_iff.mp hlip).2
  norm_num at h6 ⊢
  linarith

end LRC.FastPairEight
