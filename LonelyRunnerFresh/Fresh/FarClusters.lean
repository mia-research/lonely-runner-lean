import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.PathLaws
import Fresh.Grid
import Fresh.Cascade
import Fresh.ClusterTransfer

/-!
# Two clusters separated by a factor of 28: a slow set against a near-periodic fast block

Written 2026-10-25.  New file.  Worklist tags: G02 to G09 (two-group compositions `k | 7-k` of the subject's disparities), G11 prep, H06 (the slow group against the fast
group's landing), A04 (deformation: the block is within `η` of a grid).  Mechanisms: M-A (window about a clear instant), M-B (return and step), M-D (the split `a + b`).
`far_clusters`: the slow set `S` (arbitrary positive reals) has a `1/7`-clear instant `σ`; the fast block `f i` is within `η` of the natural multiples `n i · g` of a unit `g ≥ 28 M`
(`M` a bound for `S`), whose quotient `n i` has a `1/7`-clear instant `σF`; the deformation allowance is `η (σ + 1/(56 M)) ≤ 1/56`.  Then one instant clears both.
No order-six or order-seven theorem is used here; `σ` and `σF` are hypotheses.  Grade [L].
-/

open Classical

namespace Fresh.FarClusters

open Fresh Fresh.ClusterTransfer

theorem far_clusters {S : Finset ℝ} {ι : Type*} [Fintype ι] {f : ι → ℝ} {n : ι → ℕ} {g M σ σF η : ℝ} (hSne : S.Nonempty)
    (hSpos : ∀ s ∈ S, 0 < s) (hM : ∀ s ∈ S, s ≤ M) (hσ0 : 0 < σ) (hσ : ∀ s ∈ S, (1 / 7 : ℝ) ≤ distInt (s * σ))
    (hg : 28 * M ≤ g) (hdev : ∀ i, |f i - (n i : ℝ) * g| ≤ η) (hη : 0 ≤ η) (hquot : ∀ i, (1 / 7 : ℝ) ≤ distInt ((n i : ℝ) * σF))
    (hallow : η * (σ + 1 / (56 * M)) ≤ 1 / 56) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ S, (1 / 8 : ℝ) ≤ distInt (s * t)) ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (f i * t) := by
  obtain ⟨s0, hs0⟩ := hSne
  have hs0pos := hSpos s0 hs0
  have hMpos : 0 < M := lt_of_lt_of_le hs0pos (hM s0 hs0)
  have hgpos : 0 < g := by linarith
  set δ : ℝ := 1 / (56 * M) with hδ
  have hδpos : 0 < δ := by positivity
  have hσM : 1 / 7 ≤ M * σ := by
    have h1 := hσ s0 hs0
    have h2 := distInt_le_abs (s0 * σ)
    rw [abs_of_pos (by positivity)] at h2
    nlinarith [hM s0 hs0]
  have hδσ : δ < σ := by
    rw [hδ, div_lt_iff₀ (by positivity)]
    nlinarith
  have hper : 1 / g ≤ 2 * δ := by
    rw [hδ, div_le_iff₀ hgpos]
    have : 2 * (1 / (56 * M)) * g = g / (28 * M) := by field_simp; ring
    rw [this, le_div_iff₀ (by positivity)]
    linarith
  set a : ℝ := σ - δ with ha
  set j : ℤ := ⌈a * g - σF⌉ with hj
  set t : ℝ := (σF + j) / g with ht
  have hj1 : a * g - σF ≤ j := Int.le_ceil _
  have hj2 : (j : ℝ) < a * g - σF + 1 := Int.ceil_lt_add_one _
  have ht1 : a ≤ t := by rw [ht, le_div_iff₀ hgpos]; linarith
  have ht2 : t < a + 1 / g := by
    rw [ht, div_lt_iff₀ hgpos]
    have : (a + 1 / g) * g = a * g + 1 := by field_simp
    linarith
  have htσ : t ≤ σ + δ := by linarith
  have htpos : 0 < t := by linarith
  refine ⟨t, htpos, fun s hs => ?_, fun i => ?_⟩
  · have hts : |t - σ| ≤ δ := by rw [abs_le]; constructor <;> linarith
    have hsp := hSpos s hs
    apply clear_window_gate hsp (hσ s hs)
    refine le_trans hts ?_
    rw [show (1 / 7 : ℝ) - 1 / 8 = 1 / 56 by norm_num, hδ]
    rw [show (1 / 56 : ℝ) / s = 1 / (56 * s) by field_simp]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith [hM s hs])
  · have hlip := Fresh.PathLaws.distInt_lipschitz (f i * t) ((n i : ℝ) * (σF + j))
    have e1 : f i * t - (n i : ℝ) * (σF + j) = (f i - (n i : ℝ) * g) * t := by rw [ht]; field_simp
    have h1 : |f i * t - (n i : ℝ) * (σF + j)| ≤ 1 / 56 := by
      rw [e1, abs_mul, abs_of_pos htpos]
      calc |f i - (n i : ℝ) * g| * t ≤ η * t := mul_le_mul_of_nonneg_right (hdev i) htpos.le
        _ ≤ η * (σ + δ) := mul_le_mul_of_nonneg_left htσ hη
        _ ≤ 1 / 56 := hallow
    have e2 : (n i : ℝ) * (σF + j) = (n i : ℝ) * σF + (((n i : ℤ) * j : ℤ) : ℝ) := by push_cast; ring
    have hy : distInt ((n i : ℝ) * (σF + j)) = distInt ((n i : ℝ) * σF) := by rw [e2, distInt_add_int]
    rw [hy] at hlip
    have h7 := hquot i
    have := (abs_le.1 hlip).1
    have h2 := (abs_le.1 h1).1
    have h3 := (abs_le.1 h1).2
    linarith [(abs_le.1 hlip).2]

theorem far_clusters_gate {S : Finset ℝ} {ι : Type*} [Fintype ι] {f : ι → ℝ} {n : ι → ℕ} {g M σ σF η γ γ' : ℝ} (hSne : S.Nonempty)
    (hSpos : ∀ s ∈ S, 0 < s) (hM : ∀ s ∈ S, s ≤ M) (hσ0 : 0 < σ) (hγ : 1 / 8 < γ) (hγ' : 1 / 8 ≤ γ') (hσ : ∀ s ∈ S, γ ≤ distInt (s * σ))
    (hg : M ≤ 2 * (γ - 1 / 8) * g) (hdev : ∀ i, |f i - (n i : ℝ) * g| ≤ η) (hη : 0 ≤ η) (hquot : ∀ i, γ' ≤ distInt ((n i : ℝ) * σF))
    (hallow : η * (σ + (γ - 1 / 8) / M) ≤ γ' - 1 / 8) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ S, (1 / 8 : ℝ) ≤ distInt (s * t)) ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (f i * t) := by
  obtain ⟨s0, hs0⟩ := hSne
  have hs0pos := hSpos s0 hs0
  have hMpos : 0 < M := lt_of_lt_of_le hs0pos (hM s0 hs0)
  have hgpos : 0 < g := by
    by_contra hh
    push_neg at hh
    nlinarith
  set δ : ℝ := (γ - 1 / 8) / M with hδ
  have hδpos : 0 < δ := div_pos (by linarith) hMpos
  have hσM : γ ≤ M * σ := by
    have h1 := hσ s0 hs0
    have h2 := distInt_le_abs (s0 * σ)
    rw [abs_of_pos (by positivity)] at h2
    nlinarith [hM s0 hs0]
  have hδσ : δ < σ := by
    rw [hδ, div_lt_iff₀ hMpos]
    nlinarith
  have hper : 1 / g ≤ 2 * δ := by
    rw [hδ, div_le_iff₀ hgpos]
    have : 2 * ((γ - 1 / 8) / M) * g = (2 * (γ - 1 / 8) * g) / M := by ring
    rw [this, le_div_iff₀ hMpos]
    linarith
  set a : ℝ := σ - δ with ha
  set j : ℤ := ⌈a * g - σF⌉ with hj
  set t : ℝ := (σF + j) / g with ht
  have hj1 : a * g - σF ≤ j := Int.le_ceil _
  have hj2 : (j : ℝ) < a * g - σF + 1 := Int.ceil_lt_add_one _
  have ht1 : a ≤ t := by rw [ht, le_div_iff₀ hgpos]; linarith
  have ht2 : t < a + 1 / g := by
    rw [ht, div_lt_iff₀ hgpos]
    have : (a + 1 / g) * g = a * g + 1 := by field_simp
    linarith
  have htσ : t ≤ σ + δ := by linarith
  have htpos : 0 < t := by linarith
  refine ⟨t, htpos, fun s hs => ?_, fun i => ?_⟩
  · have hts : |t - σ| ≤ δ := by rw [abs_le]; constructor <;> linarith
    have hsp := hSpos s hs
    apply clear_window_gate hsp (hσ s hs)
    refine le_trans hts ?_
    rw [hδ]
    exact div_le_div_of_nonneg_left (by linarith) hsp (hM s hs)
  · have hlip := Fresh.PathLaws.distInt_lipschitz (f i * t) ((n i : ℝ) * (σF + j))
    have e1 : f i * t - (n i : ℝ) * (σF + j) = (f i - (n i : ℝ) * g) * t := by rw [ht]; field_simp
    have h1 : |f i * t - (n i : ℝ) * (σF + j)| ≤ γ' - 1 / 8 := by
      rw [e1, abs_mul, abs_of_pos htpos]
      calc |f i - (n i : ℝ) * g| * t ≤ η * t := mul_le_mul_of_nonneg_right (hdev i) htpos.le
        _ ≤ η * (σ + δ) := mul_le_mul_of_nonneg_left htσ hη
        _ ≤ γ' - 1 / 8 := hallow
    have e2 : (n i : ℝ) * (σF + j) = (n i : ℝ) * σF + (((n i : ℤ) * j : ℤ) : ℝ) := by push_cast; ring
    have hy : distInt ((n i : ℝ) * (σF + j)) = distInt ((n i : ℝ) * σF) := by rw [e2, distInt_add_int]
    rw [hy] at hlip
    have h7 := hquot i
    have := (abs_le.1 hlip).1
    have h2 := (abs_le.1 h1).1
    have h3 := (abs_le.1 h1).2
    linarith [(abs_le.1 hlip).2]


#print axioms far_clusters
#print axioms far_clusters_gate

end Fresh.FarClusters
