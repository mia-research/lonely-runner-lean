import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.ClusterTransfer
import Fresh.FastGaps
import Fresh.PairGapHalf
import Fresh.ClusterWindowFree

/-!
# Frozen cores with one or two further readings

Written 2026-10-26.  New file.  Worklist tags: G03, G05, H06, A07 (one or two readings against a frozen core), the S1 and S2 structure of E553 to E573 reached from the whole-number side (E639).
`window_of_bands`: if every `s ∈ S` has an integer `N` with `N + 1/8 ≤ s lo` and `s hi ≤ N + 7/8`, then every `s ∈ S` is `1/8`-clear on all of `[lo, hi]`.
`core_single`: with such a window and `1/(4x) ≤ hi - lo`, the core together with one reading `x` has a common clear instant (`single_gap`, `cluster_transfer_window`); `core_pair`: for two readings `a ≤ b` with `1/(2a) ≤ hi - lo` (`pair_gap_half`).
So a core is certified once, by its window `(lo, hi)` and the bands `N_s`, and every further reading at or above `1/(4 (hi - lo))` (every pair with smaller member at or above `1/(2 (hi - lo))`) is covered at once.
**[PROVISIONAL: covering]** as in `ClusterWindow`.  Grade [L].
-/

open Classical

namespace Fresh.CoreFamilies

open Fresh Fresh.ClusterTransfer Fresh.FastGaps Fresh.PairGapHalf Fresh.ClusterWindow

theorem window_of_bands {S : Finset ℝ} {lo hi : ℝ} (hpos : ∀ s ∈ S, 0 < s)
    (hb : ∀ s ∈ S, ∃ N : ℤ, (N : ℝ) + 1 / 8 ≤ s * lo ∧ s * hi ≤ (N : ℝ) + 7 / 8) :
    ∀ t : ℝ, lo ≤ t → t ≤ hi → ∀ s ∈ S, (1 / 8 : ℝ) ≤ distInt (s * t) := by
  intro t h1 h2 s hs
  obtain ⟨N, hN1, hN2⟩ := hb s hs
  have hsp := hpos s hs
  apply Fresh.Localisation.clear_of_window N
  · have := mul_le_mul_of_nonneg_left h1 hsp.le; linarith
  · have := mul_le_mul_of_nonneg_left h2 hsp.le; linarith

theorem core_single {S : Finset ℝ} {lo hi x : ℝ} (hlo : 0 < lo) (hpos : ∀ s ∈ S, 0 < s)
    (hb : ∀ s ∈ S, ∃ N : ℤ, (N : ℝ) + 1 / 8 ≤ s * lo ∧ s * hi ≤ (N : ℝ) + 7 / 8) (hx : 0 < x) (hgap : 1 / (4 * x) ≤ hi - lo) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ S, (1 / 8 : ℝ) ≤ distInt (s * t)) ∧ (1 / 8 : ℝ) ≤ distInt (x * t) := by
  obtain ⟨t, ht, hS, hF⟩ := cluster_transfer_window hlo (window_of_bands hpos hb) hgap (single_gap hx)
  exact ⟨t, ht, hS, hF x (Finset.mem_singleton_self x)⟩

theorem core_pair {S : Finset ℝ} {lo hi a b : ℝ} (hlo : 0 < lo) (hpos : ∀ s ∈ S, 0 < s)
    (hb : ∀ s ∈ S, ∃ N : ℤ, (N : ℝ) + 1 / 8 ≤ s * lo ∧ s * hi ≤ (N : ℝ) + 7 / 8) (ha : 0 < a) (hab : a ≤ b) (hgap : 1 / (2 * a) ≤ hi - lo) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ S, (1 / 8 : ℝ) ≤ distInt (s * t)) ∧ (1 / 8 : ℝ) ≤ distInt (a * t) ∧ (1 / 8 : ℝ) ≤ distInt (b * t) := by
  obtain ⟨t, ht, hS, hF⟩ := cluster_transfer_window hlo (window_of_bands hpos hb) hgap (pair_gap_half ha hab)
  exact ⟨t, ht, hS, hF a (by simp), hF b (by simp)⟩

/-- Example: the core `{1, 5, 6, 7, 8, 13}` (E639 item 3, widest window `[49/104, 23/48]` of width `5/624`): every further reading `x ≥ 156/5` is covered. -/
theorem core_1_5_6_7_8_13 {x : ℝ} (hx : 156 / 5 ≤ x) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ ({1, 5, 6, 7, 8, 13} : Finset ℝ), (1 / 8 : ℝ) ≤ distInt (s * t)) ∧ (1 / 8 : ℝ) ≤ distInt (x * t) := by
  have hxpos : 0 < x := by linarith
  refine core_single (lo := 49 / 104) (hi := 23 / 48) (by norm_num) ?_ ?_ hxpos ?_
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by norm_num, by norm_num⟩
    · exact ⟨2, by norm_num, by norm_num⟩
    · exact ⟨2, by norm_num, by norm_num⟩
    · exact ⟨3, by norm_num, by norm_num⟩
    · exact ⟨3, by norm_num, by norm_num⟩
    · exact ⟨6, by norm_num, by norm_num⟩
  · rw [show (23 : ℝ) / 48 - 49 / 104 = 5 / 624 by norm_num, div_le_iff₀ (by positivity)]
    nlinarith

#print axioms core_single
#print axioms core_pair
#print axioms core_1_5_6_7_8_13

end Fresh.CoreFamilies
