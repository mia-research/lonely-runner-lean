import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.PathLaws
import Fresh.Grid
import Fresh.Cascade

/-!
# Cluster transfer: a clear instant of a slow cluster, a recurrence of a fast cluster, and one slow reading against a near-periodic block

Written 2026-10-25.  New file.  Worklist tags (`ARRANGEMENT_WORKLIST_v1.md`): G02, G05, G06, G11 (cluster placement and transfer), H06 (a slow group
displaces the fast group's landing), A04 (deformation between consecutive grid speeds).  Mechanism tags used in the docstrings (recurring themes, E634):
* **M-A window**: a gate-`γ`-clear instant of a reading `d` carries a `1/8`-clear window of half-width `(γ - 1/8)/d` (`distInt` is 1-Lipschitz).
* **M-B return and step**: a cluster whose readings are whole multiples of a unit `g` has its clear set invariant under the shift `1/g`; a reading of rate
  `ρ = s/g` below `g` moves its phase by `ρ` per return, and a step of fractional size cannot stay blocked.
* **M-D split**: seven disparities split as `a + b` with `a, b ≤ 6`, so each side has a lower-order clear instant.
`cluster_transfer_gap`: slow set `S` clear at gate `γ` at `σ`; fast set `F` clear somewhere in every interval of length `L`; `L · max S ≤ 2 (γ - 1/8)`.
`clearGap_of_period`: a block of natural multiples of `g` has gap `1/g`.  `exists_clear_step_quant`: the step lemma with the number of returns bounded by `1/(4 min(ρ, 1 - ρ)) + 1`.
`slow_one_vs_block`: one slow reading `s < g` against a block within `η` of natural multiples of `g`, with the deformation allowance `η (σ + K) / g ≤ 1/56`.
All grades [L]; no order-six or order-seven result is used.
-/

open Classical

namespace Fresh.ClusterTransfer

open Fresh

/-- **M-A.** A gate-`γ`-clear instant carries a `1/8`-clear window of half-width `(γ - 1/8)/d`. -/
theorem clear_window_gate {γ d σ t : ℝ} (hd : 0 < d) (h : γ ≤ distInt (d * σ)) (ht : |t - σ| ≤ (γ - 1 / 8) / d) :
    (1 / 8 : ℝ) ≤ distInt (d * t) := by
  have hlip := Fresh.PathLaws.distInt_lipschitz (d * t) (d * σ)
  have h1 : |d * t - d * σ| ≤ γ - 1 / 8 := by
    rw [← mul_sub, abs_mul, abs_of_pos hd]
    calc d * |t - σ| ≤ d * ((γ - 1 / 8) / d) := mul_le_mul_of_nonneg_left ht hd.le
      _ = γ - 1 / 8 := by field_simp
  have := (abs_le.1 hlip).1
  have h2 := (abs_le.1 h1).2
  linarith

-- STANDING: DEFINITION
def ClearGap (F : Finset ℝ) (L : ℝ) : Prop :=
  ∀ a : ℝ, ∃ t : ℝ, a ≤ t ∧ t ≤ a + L ∧ ∀ f ∈ F, (1 / 8 : ℝ) ≤ distInt (f * t)

theorem cluster_transfer_gap {S F : Finset ℝ} {γ M σ L : ℝ} (hγ : 1 / 8 < γ) (hSne : S.Nonempty) (hSpos : ∀ s ∈ S, 0 < s)
    (hM : ∀ s ∈ S, s ≤ M) (hσ0 : 0 < σ) (hσ : ∀ s ∈ S, γ ≤ distInt (s * σ)) (hL : L * M ≤ 2 * (γ - 1 / 8))
    (hgap : ClearGap F L) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ S, (1 / 8 : ℝ) ≤ distInt (s * t)) ∧ ∀ f ∈ F, (1 / 8 : ℝ) ≤ distInt (f * t) := by
  obtain ⟨s0, hs0⟩ := hSne
  have hs0pos := hSpos s0 hs0
  have hMpos : 0 < M := lt_of_lt_of_le hs0pos (hM s0 hs0)
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
  have hLδ : L ≤ 2 * δ := by
    rw [hδ]
    rw [show 2 * ((γ - 1 / 8) / M) = (2 * (γ - 1 / 8)) / M by ring, le_div_iff₀ hMpos]
    exact hL
  obtain ⟨t, ht1, ht2, htF⟩ := hgap (σ - δ)
  have hts : |t - σ| ≤ δ := by rw [abs_le]; constructor <;> linarith
  refine ⟨t, by linarith, fun s hs => ?_, htF⟩
  have hsp := hSpos s hs
  apply clear_window_gate hsp (hσ s hs)
  refine le_trans hts ?_
  rw [hδ]
  exact div_le_div_of_nonneg_left (by linarith) hsp (hM s hs)

theorem clearGap_of_period {F : Finset ℝ} {g σ : ℝ} (hg : 0 < g) (hmul : ∀ f ∈ F, ∃ n : ℕ, f = (n : ℝ) * g)
    (hσ : ∀ f ∈ F, (1 / 8 : ℝ) ≤ distInt (f * σ)) : ClearGap F (1 / g) := by
  intro a
  set j : ℤ := ⌈(a - σ) * g⌉ with hj
  have hj1 : (a - σ) * g ≤ j := Int.le_ceil _
  have hj2 : (j : ℝ) < (a - σ) * g + 1 := Int.ceil_lt_add_one _
  refine ⟨σ + j / g, ?_, ?_, fun f hf => ?_⟩
  · have : (a - σ) ≤ j / g := by rw [le_div_iff₀ hg]; exact hj1
    linarith
  · have : (j : ℝ) / g < (a - σ) + 1 / g := by
      rw [div_lt_iff₀ hg]
      have : ((a - σ) + 1 / g) * g = (a - σ) * g + 1 := by field_simp
      linarith
    linarith
  · obtain ⟨n, hn⟩ := hmul f hf
    have e : f * (σ + j / g) = f * σ + (((n : ℤ) * j : ℤ) : ℝ) := by
      rw [hn]; push_cast; field_simp
    rw [e, distInt_add_int]
    exact hσ f hf

/-- **M-B, quantitative step.**  For `0 < ρ ≤ 1/2`, some `k ≤ 1/(4ρ) + 1` has `c + kρ` at least `1/8` from an integer. -/
theorem exists_clear_step_half {c ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1 / 2) :
    ∃ k : ℕ, (k : ℝ) ≤ 1 / (4 * ρ) + 1 ∧ (1 / 8 : ℝ) ≤ distInt (c + (k : ℝ) * ρ) := by
  by_cases hc : (1 / 8 : ℝ) ≤ distInt c
  · exact ⟨0, by simp; positivity, by simpa using hc⟩
  push_neg at hc
  set e : ℝ := c - round c with he
  have heabs : |e| = distInt c := rfl
  have he1 : e < 1 / 8 := by rw [← heabs] at hc; exact lt_of_le_of_lt (le_abs_self e) hc
  have he2 : -(1 / 8) < e := by rw [← heabs] at hc; exact lt_of_le_of_lt (neg_le_abs e) hc |> fun h => by linarith [abs_nonneg e, neg_abs_le e]
  set k : ℕ := ⌈(1 / 8 - e) / ρ⌉₊ with hk
  have hk1 : (1 / 8 - e) / ρ ≤ (k : ℝ) := Nat.le_ceil _
  have hk2 : (k : ℝ) < (1 / 8 - e) / ρ + 1 := Nat.ceil_lt_add_one (div_nonneg (by linarith) h0.le)
  have hk1' : 1 / 8 - e ≤ k * ρ := by rwa [div_le_iff₀ h0] at hk1
  have hk2' : (k : ℝ) * ρ < (1 / 8 - e) + ρ := by
    have := mul_lt_mul_of_pos_right hk2 h0
    rw [add_mul, div_mul_cancel₀ _ h0.ne', one_mul] at this
    exact this
  refine ⟨k, ?_, ?_⟩
  · have h3 : (1 / 8 - e) / ρ ≤ 1 / (4 * ρ) := by
      rw [div_le_div_iff₀ h0 (by positivity)]; nlinarith
    linarith
  · apply Fresh.Localisation.clear_of_window (round c)
    · have : c = (round c : ℝ) + e := by rw [he]; ring
      linarith
    · have : c = (round c : ℝ) + e := by rw [he]; ring
      linarith

theorem exists_clear_step_quant {c ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) :
    ∃ k : ℕ, (k : ℝ) ≤ 1 / (4 * min ρ (1 - ρ)) + 1 ∧ (1 / 8 : ℝ) ≤ distInt (c + (k : ℝ) * ρ) := by
  by_cases hρ : ρ ≤ 1 / 2
  · rw [min_eq_left (by linarith)]
    exact exists_clear_step_half h0 hρ
  · push_neg at hρ
    rw [min_eq_right (by linarith)]
    obtain ⟨k, hk, hc⟩ := exists_clear_step_half (c := -c) (ρ := 1 - ρ) (by linarith) (by linarith)
    refine ⟨k, hk, ?_⟩
    have e : c + (k : ℝ) * ρ = -(-c + (k : ℝ) * (1 - ρ)) + (k : ℤ) := by push_cast; ring
    rw [e, distInt_add_int, Fresh.Cascade.distInt_neg]
    exact hc

theorem slow_one_vs_block {ι : Type*} [Fintype ι] {f : ι → ℝ} {n : ι → ℕ} {g s σ η : ℝ} (hg : 0 < g) (hs0 : 0 < s) (hsg : s < g)
    (hσ0 : 0 < σ) (hdev : ∀ i, |f i - (n i : ℝ) * g| ≤ η) (hquot : ∀ i, 1 / 7 ≤ distInt ((n i : ℝ) * σ)) (hη : 0 ≤ η)
    (hallow : η * (σ + (1 / (4 * min (s / g) (1 - s / g)) + 1)) / g ≤ 1 / 56) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, (1 / 8 : ℝ) ≤ distInt (f i * t)) ∧ (1 / 8 : ℝ) ≤ distInt (s * t) := by
  have hρ0 : 0 < s / g := div_pos hs0 hg
  have hρ1 : s / g < 1 := (div_lt_one hg).2 hsg
  obtain ⟨k, hk, hclear⟩ := exists_clear_step_quant (c := s * σ / g) hρ0 hρ1
  refine ⟨(σ + k) / g, by positivity, fun i => ?_, ?_⟩
  · have hlip := Fresh.PathLaws.distInt_lipschitz (f i * ((σ + k) / g)) ((n i : ℝ) * (σ + k))
    have e1 : f i * ((σ + k) / g) - (n i : ℝ) * (σ + k) = (f i - (n i : ℝ) * g) * ((σ + k) / g) := by field_simp
    have h1 : |f i * ((σ + k) / g) - (n i : ℝ) * (σ + k)| ≤ 1 / 56 := by
      rw [e1, abs_mul, abs_of_pos (by positivity : 0 < (σ + k) / g)]
      calc |f i - (n i : ℝ) * g| * ((σ + k) / g) ≤ η * ((σ + k) / g) :=
            mul_le_mul_of_nonneg_right (hdev i) (by positivity)
        _ ≤ η * ((σ + (1 / (4 * min (s / g) (1 - s / g)) + 1)) / g) := by
            apply mul_le_mul_of_nonneg_left _ hη
            apply div_le_div_of_nonneg_right _ hg.le
            linarith
        _ = η * (σ + (1 / (4 * min (s / g) (1 - s / g)) + 1)) / g := by ring
        _ ≤ 1 / 56 := hallow
    have e2 : (n i : ℝ) * (σ + k) = (n i : ℝ) * σ + (((n i : ℤ) * k : ℤ) : ℝ) := by push_cast; ring
    have h7 := hquot i
    have hy : distInt ((n i : ℝ) * (σ + k)) = distInt ((n i : ℝ) * σ) := by rw [e2, distInt_add_int]
    rw [hy] at hlip
    have := (abs_le.1 hlip).1
    have h2 := (abs_le.1 h1).1
    have h3 := (abs_le.1 h1).2
    linarith [(abs_le.1 hlip).2]
  · have e : s * ((σ + k) / g) = s * σ / g + (k : ℝ) * (s / g) := by field_simp
    rw [e]; exact hclear

#print axioms clear_window_gate
#print axioms cluster_transfer_gap
#print axioms clearGap_of_period
#print axioms exists_clear_step_quant
#print axioms slow_one_vs_block

end Fresh.ClusterTransfer
