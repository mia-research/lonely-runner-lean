import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.PathLaws
import Fresh.Grid
import Fresh.FastPairReal
import Fresh.ClusterTransfer
import Fresh.FastGaps
import Fresh.PairGapHalf

/-!
# The chain with full clear windows: rung ratio 7/3 instead of 3

Written 2026-10-25.  New file.  Worklist tags: G02 (ladders and irregular spread), G05 (pair terminal), G09 and G11 (nested scales), H01 to H03 (each rung a window inside the previous one).
`window_start`: a reading `x` is clear on a closed interval of length `w ≤ 3/(4x)` starting within `1/(4x) + w` of any `α` (the blocked zone has width `1/(4x)`, the window needs `w`).
`ChainOK2 LT L`: for every rung `x` with rest `R`: `gap2 LT R ≤ 3/(4x)`, where `gap2 LT [] = LT` and `gap2 LT (x :: R) = 1/(4x) + 2 gap2 LT R`.
`chain_gap2`: every interval of length `gap2 LT L` contains an instant clearing every rung and the terminal cluster `T` (with `ClearGap T LT`).
Steady state at constant ratio `q`: `c = q / (4 (q - 2))`, the condition `c / q ≤ 3/4` gives `q ≥ 7/3` (the quarter-band chain of `ChainNested` needed `3`).  Terminal pair: `LT = 1/(2a)` (`PairGapHalf`).  Mechanism M-A (window, nested).  Grade [L].
-/

open Classical

namespace Fresh.ChainNested2

open Fresh Fresh.ClusterTransfer Fresh.FastGaps Fresh.PairGapHalf

theorem window_start {x w α : ℝ} (hx : 0 < x) (hw0 : 0 ≤ w) (hw : w ≤ 3 / (4 * x)) :
    ∃ β : ℝ, α ≤ β ∧ β ≤ α + 1 / (4 * x) + w ∧ ∀ s : ℝ, β ≤ s → s ≤ β + w → (1 / 8 : ℝ) ≤ distInt (x * s) := by
  have hxw : x * w ≤ 3 / 4 := by
    have := mul_le_mul_of_nonneg_left hw hx.le
    have e : x * (3 / (4 * x)) = 3 / 4 := by field_simp
    linarith
  have hxw0 : 0 ≤ x * w := by positivity
  set u : ℝ := x * α with hu
  set N : ℤ := ⌊u⌋ with hN
  have hN0 : (N : ℝ) ≤ u := Int.floor_le u
  have hN1 : u < (N : ℝ) + 1 := Int.lt_floor_add_one u
  have key : ∀ (M : ℤ) (β : ℝ), (M : ℝ) + 1 / 8 ≤ x * β → x * β + x * w ≤ (M : ℝ) + 7 / 8 →
      ∀ s : ℝ, β ≤ s → s ≤ β + w → (1 / 8 : ℝ) ≤ distInt (x * s) := by
    intro M β h1 h2 s hs1 hs2
    apply Fresh.Localisation.clear_of_window M
    · have := mul_le_mul_of_nonneg_left hs1 hx.le; linarith
    · have := mul_le_mul_of_nonneg_left hs2 hx.le
      have e : x * (β + w) = x * β + x * w := by ring
      linarith
  by_cases hA : (N : ℝ) + 1 / 8 ≤ u ∧ u + x * w ≤ (N : ℝ) + 7 / 8
  · have hpos : 0 < 1 / (4 * x) := by positivity
    exact ⟨α, le_refl _, by linarith, key N α (by rw [← hu]; exact hA.1) (by rw [← hu]; exact hA.2)⟩
  · rcases lt_or_ge u ((N : ℝ) + 1 / 8) with hB | hB
    · set β : ℝ := ((N : ℝ) + 1 / 8) / x with hβ
      have hxβ : x * β = (N : ℝ) + 1 / 8 := by rw [hβ]; field_simp
      refine ⟨β, ?_, ?_, key N β (by rw [hxβ]) (by rw [hxβ]; linarith)⟩
      · rw [hβ, le_div_iff₀ hx]; linarith
      · rw [hβ, div_le_iff₀ hx]
        have : (α + 1 / (4 * x) + w) * x = u + 1 / 4 + x * w := by rw [hu]; field_simp
        linarith
    · set β : ℝ := ((N : ℝ) + 9 / 8) / x with hβ
      have hxβ : x * β = (N : ℝ) + 1 + 1 / 8 := by rw [hβ]; field_simp; ring
      have hu2 : (N : ℝ) + 7 / 8 < u + x * w := by
        by_contra hh
        exact hA ⟨hB, by linarith⟩
      refine ⟨β, ?_, ?_, key (N + 1) β (by rw [hxβ]; push_cast; linarith) (by rw [hxβ]; push_cast; linarith)⟩
      · rw [hβ, le_div_iff₀ hx]; linarith
      · rw [hβ, div_le_iff₀ hx]
        have : (α + 1 / (4 * x) + w) * x = u + 1 / 4 + x * w := by rw [hu]; field_simp
        linarith

noncomputable def gap2 (LT : ℝ) : List ℝ → ℝ
  | [] => LT
  | x :: rest => 1 / (4 * x) + 2 * gap2 LT rest

-- STANDING: DEFINITION
def ChainOK2 (LT : ℝ) : List ℝ → Prop
  | [] => True
  | x :: rest => 0 < x ∧ gap2 LT rest ≤ 3 / (4 * x) ∧ ChainOK2 LT rest

theorem gap2_nonneg {LT : ℝ} (h : 0 ≤ LT) : ∀ L : List ℝ, ChainOK2 LT L → 0 ≤ gap2 LT L
  | [], _ => by simpa [gap2] using h
  | x :: rest, hok => by
    have := gap2_nonneg h rest hok.2.2
    have hx := hok.1
    simp only [gap2]; positivity

theorem chain_gap2 {T : Finset ℝ} {LT : ℝ} (hLT : 0 ≤ LT) (hT : ClearGap T LT) : ∀ (L : List ℝ), ChainOK2 LT L → ∀ α : ℝ,
    ∃ t : ℝ, α ≤ t ∧ t ≤ α + gap2 LT L ∧ (∀ f ∈ L, (1 / 8 : ℝ) ≤ distInt (f * t)) ∧ ∀ f ∈ T, (1 / 8 : ℝ) ≤ distInt (f * t)
  | [], _, α => by
    obtain ⟨t, h1, h2, h3⟩ := hT α
    exact ⟨t, h1, by simpa [gap2] using h2, by simp, h3⟩
  | x :: rest, h, α => by
    obtain ⟨hx, hnext, hrest⟩ := h
    have hg0 := gap2_nonneg hLT rest hrest
    obtain ⟨β, hβ1, hβ2, hβw⟩ := window_start (α := α) hx hg0 hnext
    obtain ⟨u, hu1, hu2, hu3, hu4⟩ := chain_gap2 hLT hT rest hrest β
    refine ⟨u, by linarith, ?_, ?_, hu4⟩
    · simp only [gap2]; linarith
    · intro f hf
      rcases List.mem_cons.1 hf with rfl | hf'
      · exact hβw u hu1 (by linarith)
      · exact hu3 f hf'

theorem cluster_chain2 {S T : Finset ℝ} {LT γ M σ : ℝ} {L : List ℝ} (hLT : 0 ≤ LT) (hγ : 1 / 8 < γ) (hSne : S.Nonempty)
    (hSpos : ∀ s ∈ S, 0 < s) (hM : ∀ s ∈ S, s ≤ M) (hσ0 : 0 < σ) (hσ : ∀ s ∈ S, γ ≤ distInt (s * σ)) (hT : ClearGap T LT)
    (hL : ChainOK2 LT L) (hgap : gap2 LT L * M ≤ 2 * (γ - 1 / 8)) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ S, (1 / 8 : ℝ) ≤ distInt (s * t)) ∧ (∀ f ∈ L, (1 / 8 : ℝ) ≤ distInt (f * t)) ∧
      ∀ f ∈ T, (1 / 8 : ℝ) ≤ distInt (f * t) := by
  have hgp : ClearGap (T ∪ L.toFinset) (gap2 LT L) := by
    intro a
    obtain ⟨u, h1, h2, h3, h4⟩ := chain_gap2 hLT hT L hL a
    refine ⟨u, h1, h2, fun f hf => ?_⟩
    rcases Finset.mem_union.1 hf with hf | hf
    · exact h4 f hf
    · exact h3 f (List.mem_toFinset.1 hf)
  obtain ⟨t, ht, hS, hF⟩ := cluster_transfer_gap hγ hSne hSpos hM hσ0 hσ hgap hgp
  exact ⟨t, ht, hS, fun f hf => hF f (Finset.mem_union_right _ (List.mem_toFinset.2 hf)),
    fun f hf => hF f (Finset.mem_union_left _ hf)⟩

#print axioms window_start
#print axioms chain_gap2
#print axioms cluster_chain2

end Fresh.ChainNested2
