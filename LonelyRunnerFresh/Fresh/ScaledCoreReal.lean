import Mathlib
import Fresh.Localisation

/-!
# A core window serves a real extra reading

Written 2026-10-29.  New file; imports only `Fresh.Localisation` (no order-seven module).
`served`: a set `S` of whole-number readings is `1/8`-clear on a window `[lo, hi]` (bands `N_s + 1/8 <= s lo`, `s hi <= N_s + 7/8`), and
a real reading `y` has `k + 1/8 <= y (hi + n)` and `y (lo + n) <= k + 7/8` for some whole numbers `n, k`.  Then `S` and `y` have a common `1/8`-clear instant `t` in `[lo + n, hi + n]`.
The shift by `n` keeps `S` clear because each `s` is a whole number, so `s n` is a whole number.
`small_y_shift`: every real `y` with `0 < y` and `y (lo + 1) <= 3/4` (so every `y <= 3/8` when `lo <= 1`) is served by the window `[lo, hi]` for a suitable `n` and `k = 0` (the periodic shift).
**[PROVISIONAL: covering]** for the use of these in a core's certificate: the claim named is that every real `y` in `[3/8, y0]` lies in one of the listed served intervals.  Grade [L] for the two lemmas.
-/

namespace Fresh.ScaledCoreReal

open Fresh

theorem served {S : Finset ℝ} {lo hi y : ℝ} (d : ℝ) (hlo : 0 < lo) (hle : lo ≤ hi) (hy : 0 < y)
    (hd0 : 0 ≤ d) (hint : ∀ s ∈ S, ∃ m : ℤ, s * d = m)
    (hb : ∀ s ∈ S, ∃ N : ℤ, (N : ℝ) + 1 / 8 ≤ s * lo ∧ s * hi ≤ (N : ℝ) + 7 / 8)
    (hpos : ∀ s ∈ S, 0 < s) (k : ℤ)
    (h1 : (k : ℝ) + 1 / 8 ≤ y * (hi + d)) (h2 : y * (lo + d) ≤ (k : ℝ) + 7 / 8) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ S, (1 / 8 : ℝ) ≤ distInt (s * t)) ∧ (1 / 8 : ℝ) ≤ distInt (y * t) := by
  set c : ℝ := ((k : ℝ) + 1 / 2) / y with hc
  set t : ℝ := max (lo + d) (min (hi + d) c) with ht
  have htlo : lo + d ≤ t := le_max_left _ _
  have hthi : t ≤ hi + d := by
    apply max_le (by linarith)
    exact min_le_left _ _
  have hlo' : 0 < lo + d := by linarith
  refine ⟨t, by linarith, ?_, ?_⟩
  · intro s hs
    obtain ⟨m_1, hm1⟩ := hint s hs
    obtain ⟨N, hN1, hN2⟩ := hb s hs
    have hsp := hpos s hs
    have hw : (1 / 8 : ℝ) ≤ distInt (s * (t - d)) := by
      apply Fresh.Localisation.clear_of_window N
      · have := mul_le_mul_of_nonneg_left (show lo ≤ t - d by linarith) hsp.le; linarith
      · have := mul_le_mul_of_nonneg_left (show t - d ≤ hi by linarith) hsp.le; linarith
    have : s * t = s * (t - d) + (m_1 : ℝ) := by
      rw [← hm1]; ring
    rw [this, Fresh.Localisation.distInt_add_int]
    exact hw
  · apply Fresh.Localisation.clear_of_window k
    · by_cases hcm : c ≤ hi + d
      · by_cases hcl : lo + d ≤ c
        · have : t = c := by
            simp only [ht]; rw [min_eq_right hcm, max_eq_right hcl]
          rw [this, hc]; field_simp; linarith
        · have : t = lo + d := by
            simp only [ht]; rw [min_eq_right hcm, max_eq_left (by linarith)]
          have hcl' : c < lo + d := lt_of_not_ge hcl
          rw [this]
          have : y * c < y * (lo + d) := mul_lt_mul_of_pos_left hcl' hy
          have hyc : y * c = (k : ℝ) + 1 / 2 := by rw [hc]; field_simp
          linarith
      · have : t = hi + d := by
          simp only [ht]; rw [min_eq_left (by linarith), max_eq_right (by linarith)]
        rw [this]; exact h1
    · by_cases hcm : c ≤ hi + d
      · by_cases hcl : lo + d ≤ c
        · have : t = c := by
            simp only [ht]; rw [min_eq_right hcm, max_eq_right hcl]
          rw [this, hc]; field_simp; linarith
        · have : t = lo + d := by
            simp only [ht]; rw [min_eq_right hcm, max_eq_left (by linarith)]
          rw [this]; exact h2
      · have : t = hi + d := by
          simp only [ht]; rw [min_eq_left (by linarith), max_eq_right (by linarith)]
        have hcl' : hi + d < c := lt_of_not_ge hcm
        rw [this]
        have : y * (hi + d) < y * c := mul_lt_mul_of_pos_left hcl' hy
        have hyc : y * c = (k : ℝ) + 1 / 2 := by rw [hc]; field_simp
        linarith

/-- The periodic shift: with step `τ > 0`, window start `lo ≤ τ`, and `y (τ + 1) ... `: a real `y` with `0 < y` and `y * (lo + τ) ≤ 3/4` is served at `k = 0` by the shift `n τ`, `n = ⌈1/(8 y τ)⌉`. -/
theorem small_y_shift {lo hi y τ : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi) (hτ : 0 < τ) (hy : 0 < y) (hy34 : y * (lo + τ) ≤ 3 / 4) :
    ∃ n : ℕ, (0 : ℝ) + 1 / 8 ≤ y * (hi + n * τ) ∧ y * (lo + n * τ) ≤ (0 : ℝ) + 7 / 8 := by
  refine ⟨⌈1 / (8 * y * τ)⌉₊, ?_, ?_⟩
  · have h8 : 1 / (8 * y * τ) ≤ (⌈1 / (8 * y * τ)⌉₊ : ℝ) := Nat.le_ceil _
    have : 1 / 8 ≤ y * ((⌈1 / (8 * y * τ)⌉₊ : ℝ) * τ) := by
      have := mul_le_mul_of_nonneg_left h8 (mul_pos hy hτ).le
      have e : y * τ * (1 / (8 * y * τ)) = 1 / 8 := by field_simp
      nlinarith
    nlinarith [mul_pos hy hlo]
  · have h8 : (⌈1 / (8 * y * τ)⌉₊ : ℝ) < 1 / (8 * y * τ) + 1 := Nat.ceil_lt_add_one (by positivity)
    have : y * τ * (⌈1 / (8 * y * τ)⌉₊ : ℝ) < y * τ * (1 / (8 * y * τ) + 1) := mul_lt_mul_of_pos_left h8 (mul_pos hy hτ)
    have e : y * τ * (1 / (8 * y * τ) + 1) = 1 / 8 + y * τ := by field_simp
    nlinarith

#print axioms served
#print axioms small_y_shift

end Fresh.ScaledCoreReal
