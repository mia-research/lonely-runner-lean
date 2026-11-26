import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.OneMoverA
import Fresh.CascadeLanding
import Fresh.CascadeLandingG
import Fresh.CascadeLanding2

/-!
# Two movers: a sharper width lemma

Written 2026-10-22.  New file.  `two_clear_in2`: for `d1 ≤ d2`, every interval `[l, r]` with `r - l ≥ 1/d1` contains a common clear
instant of the two movers.  (`two_clear_in` in `CascadeLanding2.lean` needs `r - l ≥ 7/(4 d1)`.)  **[PROVISIONAL: counting tool]**.
Proof: let `S` be the first clear instant of the slower mover at or after `l` (`S ≤ l + 1/(4 d1)`), inside the clear window
`[(n+1/8)/d1, (n+7/8)/d1]`.  If at least `1/(4 d2)` of the window remains after `S`, the faster mover has a clear instant there.
Otherwise the next window starts at most `1/(4 d1)` later, and the faster mover has a clear instant within `1/(4 d2)` of its start.
-/

open Classical

namespace Fresh.OneMover

open Fresh

theorem firstPt_le {d A : ℝ} (hd : 0 < d) : firstPt d A ≤ A + 1 / (4 * d) := by
  unfold firstPt
  split_ifs with hc
  · have : 0 < 1 / (4 * d) := by positivity
    linarith
  · exact opening_close hd hc

theorem two_clear_in2 {d1 d2 l r : ℝ} (h1 : 0 < d1) (h12 : d1 ≤ d2) (hw : l + 1 / d1 ≤ r) :
    ∃ t, l ≤ t ∧ t ≤ r ∧ Clear2 d1 d2 t := by
  have h2 : 0 < d2 := lt_of_lt_of_le h1 h12
  have hq1 : 0 < 1 / (4 * d1) := by positivity
  have hq2 : 0 < 1 / (4 * d2) := by positivity
  have hq21 : 1 / (4 * d2) ≤ 1 / (4 * d1) := by
    apply one_div_le_one_div_of_le (by positivity); nlinarith
  have hfull : 1 / (4 * d1) ≤ 3 / (4 * d1) := by
    apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hsum : 1 / (4 * d1) + 1 / (4 * d1) + 1 / (4 * d1) + 1 / (4 * d1) = 1 / d1 := by field_simp; ring
  -- S: the first clear instant of the slower mover at or after l
  have hhold1 : Holds d1 l (l + 1 / (4 * d1)) := by
    by_cases hc : (1 / 8 : ℝ) ≤ distInt (d1 * l)
    · exact Or.inl hc
    · right; have := opening_close h1 hc; linarith
  obtain ⟨hSc, hSl, hSr, _⟩ := holds_clear h1 (by linarith) hhold1
  set S : ℝ := firstPt d1 l with hS
  -- the window of mover 1 containing S
  set n : ℤ := ⌊d1 * S - 1 / 8⌋ with hn
  have hn1 : (n : ℝ) ≤ d1 * S - 1 / 8 := Int.floor_le _
  have hn2 : d1 * S - 1 / 8 < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have hn3 : d1 * S ≤ (n : ℝ) + 7 / 8 := by
    by_contra hcon
    push Not at hcon
    have hlt : |d1 * S - ((n + 1 : ℤ) : ℝ)| < 1 / 8 := by
      push_cast; rw [abs_lt]; constructor <;> linarith
    have := Fresh.Cascade.distInt_le (d1 * S) (n + 1)
    linarith
  set E : ℝ := ((n : ℝ) + 7 / 8) / d1 with hE
  have hSE : S ≤ E := by rw [hE, le_div_iff₀ h1]; linarith
  have hwin : ∀ s, S ≤ s → s ≤ E → (1 / 8 : ℝ) ≤ distInt (d1 * s) := by
    intro s hs1 hs2
    apply Fresh.Localisation.clear_of_window n
    · have := mul_le_mul_of_nonneg_left hs1 h1.le; linarith
    · have : d1 * s ≤ d1 * E := mul_le_mul_of_nonneg_left hs2 h1.le
      have e : d1 * E = (n : ℝ) + 7 / 8 := by rw [hE]; field_simp
      linarith
  by_cases hR : 1 / (4 * d2) ≤ E - S
  · -- the faster mover has a clear instant inside the rest of the window
    have hh : Holds d2 S E := by
      by_cases hc : (1 / 8 : ℝ) ≤ distInt (d2 * S)
      · exact Or.inl hc
      · right; have := opening_close h2 hc; linarith
    obtain ⟨hc2, hl2, hr2, _⟩ := holds_clear h2 hSE hh
    have hb := firstPt_le (A := S) h2
    exact ⟨firstPt d2 S, by linarith, by linarith, hwin _ hl2 hr2, hc2⟩
  · push Not at hR
    -- the next window of mover 1 starts at S' = E + 1/(4 d1)
    set S' : ℝ := ((n : ℝ) + 1 + 1 / 8) / d1 with hS'
    have hS'E : S' = E + 1 / (4 * d1) := by rw [hS', hE]; field_simp; ring
    have hS'pos : S' ≤ S' + 3 / (4 * d1) := le_add_of_nonneg_right (by positivity)
    have hh : Holds d2 S' (S' + 3 / (4 * d1)) := by
      by_cases hc : (1 / 8 : ℝ) ≤ distInt (d2 * S')
      · exact Or.inl hc
      · right; have := opening_close h2 hc; linarith
    obtain ⟨hc2, hl2, hr2, _⟩ := holds_clear h2 hS'pos hh
    have hwin2 : (1 / 8 : ℝ) ≤ distInt (d1 * firstPt d2 S') := by
      apply Fresh.Localisation.clear_of_window (n + 1)
      · have : d1 * S' = (n : ℝ) + 1 + 1 / 8 := by rw [hS']; field_simp
        have := mul_le_mul_of_nonneg_left hl2 h1.le
        push_cast; linarith
      · have : d1 * (S' + 3 / (4 * d1)) = (n : ℝ) + 1 + 7 / 8 := by rw [hS']; field_simp; ring
        have := mul_le_mul_of_nonneg_left hr2 h1.le
        push_cast; linarith
    refine ⟨firstPt d2 S', by linarith, ?_, hwin2, hc2⟩
    -- firstPt d2 S' ≤ S' + 1/(4 d2) (it is the first clear instant of d2 from S')
    have hfp := firstPt_le (A := S') h2
    linarith

#print axioms two_clear_in2

end Fresh.OneMover
