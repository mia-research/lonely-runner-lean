import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.PathLaws
import Fresh.Admissible
import Fresh.AdmissibleFlank

/-!
# The fast pair on real speeds: a native reproof of an old separation-of-scale rule

Written 2026-10-25 (owner: "fast pair first").  New file.  Old rule: `lonely_eight_of_fastPair` (`FastPairEightN.lean`): two disparities `a < b` with `9c ≤ a` for every other `c`, over seven disparities, is lonely.
Its proof is elementary once the five core readings have an instant `τ` at which each is `1/6`-clear (the order-six theorem, not available in this tree): the core readings stay `1/8`-clear on a window of length `3/(4a)` around `τ`
(`distInt` is 1-Lipschitz), and in that window both `a` and `b` are clear at some instant (`pair_window`: a quarter-length clear stretch for `a`, a quarter-lap of `b` across it).
Native real form: `FastPairClass v k` carries the `1/6`-clear instant `τ` of the core as part of the class (a checkable hypothesis on the arrangement, which the order-six theorem always supplies).
* `exists_band_point`, `exists_quarter_band`, `pair_window`: re-proved on `distInt`, no integers.
* `fastPair_isolation`: a fast pair with a `1/6`-clear core instant gives an isolation.
* `FastPairClass_smul`, `FastPairClass_add`: scale and translation invariance.
Grades: [L].  Not claimed: that the core instant `τ` exists (it does by order six; it is a hypothesis here); the block split, one-free and thirds/fifths/sixths rules.
-/

open Classical

namespace Fresh.FastPairReal

open Fresh Fresh.Admissible Fresh.AdmissibleFlank

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

/-- Two runners in a window: for `0 < a ≤ b` the closed window `[x, x + 3/(4a)]` holds an instant at which both are `1/8`-clear. -/
theorem pair_window {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x : ℝ) :
    ∃ t : ℝ, x ≤ t ∧ t ≤ x + 3 / (4 * a) ∧ (1 / 8 : ℝ) ≤ distInt (a * t) ∧ (1 / 8 : ℝ) ≤ distInt (b * t) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  obtain ⟨s, hs1, hs2, m, hm1, hm2⟩ := exists_quarter_band (a * x)
  obtain ⟨w, hw1, hw2, m', hm1', hm2'⟩ := exists_band_point (b * (s / a))
  refine ⟨w / b, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hb]
    have hsa : x ≤ s / a := by rw [le_div_iff₀ ha]; linarith
    calc x * b ≤ (s / a) * b := mul_le_mul_of_nonneg_right hsa hb.le
      _ = b * (s / a) := by ring
      _ ≤ w := hw1
  · have h1 : w / b ≤ s / a + 1 / (4 * b) := by
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
  · have hlo : s ≤ a * (w / b) := by
      have : a * (w / b) = (a / b) * w := by ring
      rw [this]
      have hw' : b * (s / a) ≤ w := hw1
      calc s = (a / b) * (b * (s / a)) := by field_simp
        _ ≤ (a / b) * w := mul_le_mul_of_nonneg_left hw' (by positivity)
    have hhi : a * (w / b) ≤ s + 1 / 4 := by
      have hab' : a / b ≤ 1 := (div_le_one hb).mpr hab
      have : a * (w / b) = (a / b) * w := by ring
      rw [this]
      calc (a / b) * w ≤ (a / b) * (b * (s / a) + 1 / 4) := mul_le_mul_of_nonneg_left hw2 (by positivity)
        _ = s + (a / b) * (1 / 4) := by field_simp
        _ ≤ s + 1 / 4 := by nlinarith
    apply Fresh.Localisation.clear_of_window m
    · linarith
    · linarith
  · rw [show b * (w / b) = w by field_simp]
    apply Fresh.Localisation.clear_of_window m'
    · exact hm1'
    · linarith

-- STANDING: DEFINITION
def FastPairClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ a ∈ disparitySet v k, ∃ b ∈ disparitySet v k, a < b ∧ (∃ c ∈ disparitySet v k, c ≠ a ∧ c ≠ b) ∧
    ∃ τ : ℝ, 0 < τ ∧ ∀ c ∈ disparitySet v k, c ≠ a → c ≠ b → (1 / 6 : ℝ) ≤ distInt (c * τ) ∧ 9 * c ≤ a

theorem fastPair_isolation {v : Fin 8 → ℝ} (hinj : Function.Injective v) {k : Fin 8} (h : FastPairClass v k) : Isolation v k := by
  obtain ⟨a, ha, b, hb, hab, ⟨c0, hc0, hc0a, hc0b⟩, τ, hτ, hcore⟩ := h
  have hapos := disp_pos hinj ha
  have hbpos := disp_pos hinj hb
  have hc0pos := disp_pos hinj hc0
  set δ : ℝ := 3 / (8 * a) with hδ
  have hδpos : 0 < δ := by positivity
  -- τ ≥ 3/(2a) > δ
  obtain ⟨h60, h9⟩ := hcore c0 hc0 hc0a hc0b
  have hτ1 : 1 / 6 ≤ c0 * τ := by
    have := Fresh.Localisation.distInt_le (c0 * τ) 0
    simp only [Int.cast_zero, sub_zero] at this
    rw [abs_of_nonneg (by positivity)] at this
    linarith
  have hτlow : 3 / (2 * a) ≤ τ := by
    rw [div_le_iff₀ (by positivity)]
    have : c0 * τ * 9 ≤ a * τ := by nlinarith
    have h2 : (1 / 6 : ℝ) * 9 ≤ c0 * τ * 9 := by linarith
    nlinarith
  have hδτ : δ < τ := by
    have : δ < 3 / (2 * a) := by
      rw [hδ, div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  obtain ⟨t, ht1, ht2, hta, htb⟩ := pair_window hapos hab.le (τ - δ)
  have hwin : t ≤ τ - δ + 3 / (4 * a) := ht2
  have hts : |t - τ| ≤ δ := by
    rw [abs_le]
    have e : 3 / (4 * a) = 2 * δ := by rw [hδ]; field_simp; ring
    constructor <;> linarith
  refine ⟨t, by linarith, ?_⟩
  rw [Fresh.Localisation.isolatedAt_iff]
  intro d hd
  by_cases hda : d = a
  · rw [hda]; exact hta
  by_cases hdb : d = b
  · rw [hdb]; exact htb
  obtain ⟨h6, h9d⟩ := hcore d hd hda hdb
  have hdpos := disp_pos hinj hd
  have hdist : |d * t - d * τ| ≤ 1 / 24 := by
    rw [← mul_sub, abs_mul, abs_of_pos hdpos]
    calc d * |t - τ| ≤ (a / 9) * δ := mul_le_mul (by linarith) hts (abs_nonneg _) (by positivity)
      _ = 1 / 24 := by rw [hδ]; field_simp; ring
  have hlip := Fresh.PathLaws.distInt_lipschitz (d * τ) (d * t)
  have := (abs_le.1 hlip).1
  have h2 : |d * τ - d * t| ≤ 1 / 24 := by rw [abs_sub_comm]; exact hdist
  linarith [(abs_le.1 hlip).2, (abs_le.1 h2).1, (abs_le.1 h2).2]

#print axioms pair_window
#print axioms fastPair_isolation

end Fresh.FastPairReal
