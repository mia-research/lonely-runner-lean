import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.PathLaws
import Fresh.Grid
import Fresh.ClusterTransfer
import Fresh.FastPairReal

/-!
# A compact clump of fast readings behaves as one reading while its phase stays small

Written 2026-10-25.  New file.  Worklist tags: G04 (one low reading, a high group: 1 | 6), G12 (compact translated train), G03 (low cluster, one high outlier), H06.
`clump_gap`: readings `y ∈ [x, (1+ε) x]` (any number, any positions) are jointly `1/8`-clear somewhere in every interval of length `1/(2x)` that starts at a time `α ≤ T`, provided `ε (x T + 2) ≤ 1/8`.
Reason (M-A at the phase level): choose a time at which the slowest reading's phase is in the reduced band `[m + 1/8, m + 5/8]`; the others have phase at most `(1+ε)` times that, a shift of at most `ε (m + 1) ≤ 1/8`.
So the clump costs `ε (x T + 2) ≤ 1/8` and nothing else: the time cap `T` is explicit when the slow side is one reading (`σ = 1/(2s)`) or an AP block (`σ = 1/((r+1) g)`).  Grade [L].
`single_slow_clump`: one slow reading `s` and any clump of at most six readings within ratio `1 + ε` of its slowest member `x`: isolation when `ε (x/(2s) + 2) ≤ 1/8` and `x ≥ 2 s / 3`.
-/

namespace Fresh.ClumpGap

open Fresh Fresh.ClusterTransfer

-- STANDING: DEFINITION
def ClearGapBelow (F : Finset ℝ) (L T : ℝ) : Prop :=
  ∀ α : ℝ, 0 ≤ α → α ≤ T → ∃ t : ℝ, α ≤ t ∧ t ≤ α + L ∧ ∀ f ∈ F, (1 / 8 : ℝ) ≤ distInt (f * t)

theorem reduced_band_point (v : ℝ) :
    ∃ w : ℝ, v ≤ w ∧ w ≤ v + 1 / 2 ∧ ∃ m : ℤ, (m : ℝ) + 1 / 8 ≤ w ∧ w ≤ (m : ℝ) + 5 / 8 ∧ (m : ℝ) ≤ v + 1 := by
  have hv := Int.floor_add_fract v
  have hf0 := Int.fract_nonneg v
  have hf1 := Int.fract_lt_one v
  by_cases h1 : Int.fract v < 1 / 8
  · exact ⟨(⌊v⌋ : ℝ) + 1 / 8, by linarith, by linarith, ⌊v⌋, le_refl _, by linarith, by linarith⟩
  by_cases h2 : Int.fract v ≤ 5 / 8
  · exact ⟨v, le_refl _, by linarith, ⌊v⌋, by linarith, by linarith, by linarith⟩
  · push Not at h1 h2
    refine ⟨((⌊v⌋ + 1 : ℤ) : ℝ) + 1 / 8, ?_, ?_, ⌊v⌋ + 1, le_refl _, ?_, ?_⟩ <;> push_cast <;> linarith

theorem clump_gap {C : Finset ℝ} {x ε T : ℝ} (hx : 0 < x) (hε : 0 ≤ ε) (hT : 0 ≤ T) (hC : ∀ y ∈ C, x ≤ y ∧ y ≤ (1 + ε) * x)
    (hdev : ε * (x * T + 2) ≤ 1 / 8) : ClearGapBelow C (1 / (2 * x)) T := by
  intro α hα0 hα
  obtain ⟨w, hw1, hw2, m, hm1, hm2, hm3⟩ := reduced_band_point (x * α)
  have hxα : 0 ≤ x * α := by positivity
  have hw0 : 0 ≤ w := by linarith
  have hmT : (m : ℝ) ≤ x * T + 1 := by nlinarith [hα, hx, hm3]
  refine ⟨w / x, ?_, ?_, fun y hy => ?_⟩
  · rw [le_div_iff₀ hx]; linarith
  · rw [div_le_iff₀ hx]
    have : (α + 1 / (2 * x)) * x = x * α + 1 / 2 := by field_simp
    linarith
  · obtain ⟨hy1, hy2⟩ := hC y hy
    have e : y * (w / x) = (y / x) * w := by field_simp
    have hyx : 1 ≤ y / x := by rw [le_div_iff₀ hx]; linarith
    have hyx2 : y / x ≤ 1 + ε := by rw [div_le_iff₀ hx]; linarith
    apply Fresh.Localisation.clear_of_window m
    · rw [e]; nlinarith
    · rw [e]
      have h1 : y / x * w ≤ (1 + ε) * w := mul_le_mul_of_nonneg_right hyx2 hw0
      have h2 : ε * w ≤ ε * ((m : ℝ) + 5 / 8) := mul_le_mul_of_nonneg_left hm2 hε
      have h3 : ε * ((m : ℝ) + 5 / 8) ≤ ε * (x * T + 2) := mul_le_mul_of_nonneg_left (by linarith) hε
      nlinarith

theorem single_slow_clump {s x ε : ℝ} {C : Finset ℝ} (hs : 0 < s) (hx : 0 < x) (hε : 0 ≤ ε) (hC : ∀ y ∈ C, x ≤ y ∧ y ≤ (1 + ε) * x)
    (hdev : ε * (x * (1 / (2 * s)) + 2) ≤ 1 / 8) (hxs : 2 * s ≤ 3 * x) :
    ∃ t : ℝ, 0 < t ∧ (1 / 8 : ℝ) ≤ distInt (s * t) ∧ ∀ y ∈ C, (1 / 8 : ℝ) ≤ distInt (y * t) := by
  have hT : 0 ≤ 1 / (2 * s) := by positivity
  have hgap := clump_gap hx hε hT hC hdev
  set σ : ℝ := 1 / (2 * s) with hσ
  have hσs : s * σ = 1 / 2 := by rw [hσ]; field_simp
  have hhalf : (1 / 2 : ℝ) ≤ distInt (1 / 2) := by
    rw [Fresh.Localisation.le_distInt_iff]
    intro z
    rcases le_or_gt z 0 with hz | hz
    · have : (z : ℝ) ≤ 0 := by exact_mod_cast hz
      rw [abs_of_nonneg (by linarith)]; linarith
    · have : (1 : ℝ) ≤ z := by exact_mod_cast hz
      rw [abs_of_nonpos (by linarith)]; linarith
  set δ : ℝ := (1 / 2 - 1 / 8) / s with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδσ : δ < σ := by
    rw [hδ, hσ, div_lt_div_iff₀ hs (by positivity)]; nlinarith
  obtain ⟨t, ht1, ht2, htC⟩ := hgap (σ - δ) (by linarith) (by linarith)
  have hL : 1 / (2 * x) ≤ 2 * δ := by
    rw [hδ, show 2 * ((1 / 2 - 1 / 8) / s) = (3 / 4) / s by ring, div_le_div_iff₀ (by positivity) hs]
    linarith
  have hts : |t - σ| ≤ δ := by rw [abs_le]; constructor <;> linarith
  refine ⟨t, by linarith, ?_, htC⟩
  exact clear_window_gate (γ := 1 / 2) hs (by rw [hσs]; exact hhalf) hts

#print axioms clump_gap
#print axioms single_slow_clump

end Fresh.ClumpGap
