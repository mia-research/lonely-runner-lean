import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.PathLaws
import Fresh.Grid
import Fresh.FastPairReal
import Fresh.ClusterTransfer

/-!
# The pair gap is at most one half of a period of the slower reading

Written 2026-10-25.  New file.  Worklist tags: G05 (two high readings), G09 and G11 (a pair as the terminal cluster of a chain), H06.
`pair_gap_half`: for `0 < a ≤ b` every interval of length `1/(2a)` contains an instant at which both are `1/8`-clear.  `FastPairReal.pair_window` gave `3/(4a)`; the exact interval arithmetic
(`experiments/n8/pair_gap_exact_v1.py`) puts the supremum over the grid at just under `1/2` (`97/200` at `b/a = 25/24`), so `1/2` is the right constant.
Proof (constructive, by the phase `f` of `a` at the start): `f ∈ [1/8, 5/8]` the first quarter of the phase is `a`-clear; `f < 1/8` or `f > 7/8` the next `a`-band starts inside the interval;
`f ∈ (5/8, 7/8]` the interval holds the whole `a`-blocked zone, and either the larger side piece has length at least `1/(4b)` (`b ≥ 2a`) or the two zone endpoints, both `a`-clear and
`b/(4a) < 1/2` apart, cannot both be `b`-blocked.  Mechanism M-A (twice).  Consequence: `fast_pair_far_half` needs `a ≥ M / (4 (γ - 1/8))` (at gate `1/6`: `6 M`, was `9 M`).  Grade [L].
-/

namespace Fresh.PairGapHalf

open Fresh Fresh.FastPairReal Fresh.ClusterTransfer

theorem b_point_in {b p ℓ : ℝ} (hb : 0 < b) (hℓ : 1 / (4 * b) ≤ ℓ) :
    ∃ t : ℝ, p ≤ t ∧ t ≤ p + ℓ ∧ (1 / 8 : ℝ) ≤ distInt (b * t) := by
  obtain ⟨w, hw1, hw2, m, hm1, hm2⟩ := exists_band_point (b * p)
  refine ⟨w / b, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hb]; linarith
  · rw [div_le_iff₀ hb]
    have : 1 / (4 * b) * b = 1 / 4 := by field_simp
    nlinarith
  · rw [show b * (w / b) = w by field_simp]
    exact Fresh.Localisation.clear_of_window m hm1 (by linarith)

theorem not_both_blocked {b c1 c2 : ℝ} (h1 : 1 / 4 ≤ b * (c2 - c1)) (h2 : b * (c2 - c1) < 1 / 2) :
    (1 / 8 : ℝ) ≤ distInt (b * c1) ∨ (1 / 8 : ℝ) ≤ distInt (b * c2) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  have e1 : |b * c1 - (round (b * c1) : ℝ)| < 1 / 8 := hc1
  have e2 : |b * c2 - (round (b * c2) : ℝ)| < 1 / 8 := hc2
  rw [abs_lt] at e1 e2
  have hpos : (0 : ℝ) < ((round (b * c2) - round (b * c1) : ℤ) : ℝ) := by push_cast; linarith [mul_sub b c2 c1]
  have hlt : ((round (b * c2) - round (b * c1) : ℤ) : ℝ) < 1 := by push_cast; linarith [mul_sub b c2 c1]
  have h1' : (0 : ℤ) < round (b * c2) - round (b * c1) := by exact_mod_cast hpos
  have h2' : round (b * c2) - round (b * c1) < (1 : ℤ) := by exact_mod_cast hlt
  omega

theorem bpt_phase {ρ p ℓ : ℝ} (hρ : 0 < ρ) (hℓ : 1 / (4 * ρ) ≤ ℓ) :
    ∃ v : ℝ, p ≤ v ∧ v ≤ p + ℓ ∧ (1 / 8 : ℝ) ≤ distInt (ρ * v) := by
  obtain ⟨t, h1, h2, h3⟩ := b_point_in (p := p) hρ hℓ
  exact ⟨t, h1, h2, h3⟩

/-- The statement with `a = 1`: phases of the slower reading. -/
theorem pair_phase {ρ : ℝ} (hρ : 1 ≤ ρ) (u : ℝ) :
    ∃ v : ℝ, u ≤ v ∧ v ≤ u + 1 / 2 ∧ (1 / 8 : ℝ) ≤ distInt v ∧ (1 / 8 : ℝ) ≤ distInt (ρ * v) := by
  have hρ0 : 0 < ρ := by linarith
  have hq : 1 / (4 * ρ) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set N : ℤ := ⌊u⌋ with hN
  have hN0 : (N : ℝ) ≤ u := Int.floor_le u
  have hN1 : u < (N : ℝ) + 1 := Int.lt_floor_add_one u
  rcases lt_or_ge u ((N : ℝ) + 1 / 8) with hB | hB
  · obtain ⟨v, h1, h2, h3⟩ := bpt_phase (p := (N : ℝ) + 1 / 8) hρ0 (le_refl (1 / (4 * ρ)))
    exact ⟨v, by linarith, by linarith, Fresh.Localisation.clear_of_window N (by linarith) (by linarith), h3⟩
  rcases le_or_gt u ((N : ℝ) + 5 / 8) with hA | hC
  · obtain ⟨v, h1, h2, h3⟩ := bpt_phase (p := u) hρ0 (le_refl (1 / (4 * ρ)))
    exact ⟨v, h1, by linarith, Fresh.Localisation.clear_of_window N (by linarith) (by linarith), h3⟩
  rcases le_or_gt u ((N : ℝ) + 7 / 8) with hD | hD
  · by_cases hb2 : 2 ≤ ρ
    · by_cases hP1 : 1 / (4 * ρ) ≤ (N : ℝ) + 7 / 8 - u
      · obtain ⟨v, h1, h2, h3⟩ := bpt_phase (p := u) hρ0 hP1
        exact ⟨v, h1, by linarith, Fresh.Localisation.clear_of_window N (by linarith) (by linarith), h3⟩
      · push Not at hP1
        have h2b : 1 / (2 * ρ) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        have hP2 : 1 / (4 * ρ) ≤ u + 1 / 2 - ((N : ℝ) + 9 / 8) := by
          have : 1 / (2 * ρ) = 1 / (4 * ρ) + 1 / (4 * ρ) := by field_simp; ring
          linarith
        obtain ⟨v, h1, h2, h3⟩ := bpt_phase (p := (N : ℝ) + 9 / 8) hρ0 hP2
        exact ⟨v, by linarith, by linarith,
          Fresh.Localisation.clear_of_window (N + 1) (by push_cast; linarith) (by push_cast; linarith), h3⟩
    · push Not at hb2
      have hlo : 1 / 4 ≤ ρ * (((N : ℝ) + 9 / 8) - ((N : ℝ) + 7 / 8)) := by nlinarith
      have hhi : ρ * (((N : ℝ) + 9 / 8) - ((N : ℝ) + 7 / 8)) < 1 / 2 := by nlinarith
      have hc1 : (1 / 8 : ℝ) ≤ distInt ((N : ℝ) + 7 / 8) :=
        Fresh.Localisation.clear_of_window N (by linarith) (by linarith)
      have hc2 : (1 / 8 : ℝ) ≤ distInt ((N : ℝ) + 9 / 8) :=
        Fresh.Localisation.clear_of_window (N + 1) (by push_cast; linarith) (by push_cast; linarith)
      rcases not_both_blocked hlo hhi with h | h
      · exact ⟨(N : ℝ) + 7 / 8, by linarith, by linarith, hc1, h⟩
      · exact ⟨(N : ℝ) + 9 / 8, by linarith, by linarith, hc2, h⟩
  · obtain ⟨v, h1, h2, h3⟩ := bpt_phase (p := (N : ℝ) + 9 / 8) hρ0 (le_refl (1 / (4 * ρ)))
    exact ⟨v, by linarith, by linarith,
      Fresh.Localisation.clear_of_window (N + 1) (by push_cast; linarith) (by push_cast; linarith), h3⟩

theorem pair_gap_half {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : ClearGap {a, b} (1 / (2 * a)) := by
  intro x
  have hρ : 1 ≤ b / a := by rw [le_div_iff₀ ha]; linarith
  obtain ⟨v, h1, h2, h3, h4⟩ := pair_phase hρ (a * x)
  refine ⟨v / a, ?_, ?_, fun f hf => ?_⟩
  · rw [le_div_iff₀ ha]; linarith
  · rw [div_le_iff₀ ha]
    have : (x + 1 / (2 * a)) * a = a * x + 1 / 2 := by field_simp
    linarith
  · rw [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · rw [show f * (v / f) = v by field_simp]; exact h3
    · have : f * (v / a) = f / a * v := by field_simp
      rw [this]; exact h4

theorem fast_pair_far_half {S : Finset ℝ} {γ M σ a b : ℝ} (hγ : 1 / 8 < γ) (hSne : S.Nonempty) (hSpos : ∀ s ∈ S, 0 < s)
    (hM : ∀ s ∈ S, s ≤ M) (hσ0 : 0 < σ) (hσ : ∀ s ∈ S, γ ≤ distInt (s * σ)) (hab : a ≤ b) (hapos : 0 < a)
    (ha : M ≤ 4 * (γ - 1 / 8) * a) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ S, (1 / 8 : ℝ) ≤ distInt (s * t)) ∧ (1 / 8 : ℝ) ≤ distInt (a * t) ∧ (1 / 8 : ℝ) ≤ distInt (b * t) := by
  have hL : 1 / (2 * a) * M ≤ 2 * (γ - 1 / 8) := by
    rw [show 1 / (2 * a) * M = M / (2 * a) by ring, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨t, ht, hS, hF⟩ := cluster_transfer_gap hγ hSne hSpos hM hσ0 hσ hL (pair_gap_half hapos hab)
  exact ⟨t, ht, hS, hF a (by simp), hF b (by simp)⟩

#print axioms pair_gap_half
#print axioms fast_pair_far_half

end Fresh.PairGapHalf
