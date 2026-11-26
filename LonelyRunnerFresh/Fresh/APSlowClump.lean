import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.PathLaws
import Fresh.Grid
import Fresh.Admissible
import Fresh.AdmissibleFlank
import Fresh.ClusterTransfer
import Fresh.ClumpGap
import Fresh.APBlockSlow
import Fresh.APBlockFar

/-!
# A slow near-AP block under a compact fast clump

Written 2026-10-25.  New file.  Worklist tags: A01, A04 (the slow block is an AP `g, …, r g` within `η` of the AP), G12 (compact translated train above it), G04 and G03 (a low group and a high group), H06.
`cluster_transfer_gap_below`: `cluster_transfer_gap` with a fast part that has a bounded gap only for start times up to a cap `T` (`ClearGapBelow`); the cap is the slow cluster's gate instant plus nothing.
`ap_slow_clump`: slow `d i` with `|d i - (i+1) g| ≤ η` (`i < r`, `r ≤ 6`), gate instant `σ = 1/((r+1) g)` explicit, effective gate `γ = 1/(r+1) - η σ > 1/8`; a fast clump `C ⊂ [x, (1+ε) x]` with
`M/(2x) ≤ 2 (γ - 1/8)` (`M = r g + η`) and `ε (x σ + 2) ≤ 1/8` is jointly clear with the slow block at one instant.  No order theorem is used.  **[PROVISIONAL: covering]**: the clump's blocked zones (one zone of width at most
`1/(4x)` per period, shifted by at most the phase slack `ε (m + 1)`) do not cover the slow block's clear window; the claim rests on the slack `1/(2x) ≤ 2 δ` and the time cap.  Grade [L].
-/

open Classical

namespace Fresh.APSlowClump

open Fresh Fresh.ClusterTransfer Fresh.ClumpGap Fresh.APBlockSlow

theorem cluster_transfer_gap_below {S F : Finset ℝ} {γ M σ L : ℝ} (hγ : 1 / 8 < γ) (hSne : S.Nonempty) (hSpos : ∀ s ∈ S, 0 < s)
    (hM : ∀ s ∈ S, s ≤ M) (hσ0 : 0 < σ) (hσ : ∀ s ∈ S, γ ≤ distInt (s * σ)) (hL : L * M ≤ 2 * (γ - 1 / 8))
    (hgap : ClearGapBelow F L σ) :
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
  obtain ⟨t, ht1, ht2, htF⟩ := hgap (σ - δ) (by linarith) (by linarith)
  have hts : |t - σ| ≤ δ := by rw [abs_le]; constructor <;> linarith
  refine ⟨t, by linarith, fun s hs => ?_, htF⟩
  have hsp := hSpos s hs
  apply clear_window_gate hsp (hσ s hs)
  refine le_trans hts ?_
  rw [hδ]
  exact div_le_div_of_nonneg_left (by linarith) hsp (hM s hs)

theorem ap_slow_clump {r : ℕ} (hr : r ≤ 6) (hr1 : 1 ≤ r) {d : Fin r → ℝ} {g η ε x : ℝ} {C : Finset ℝ} (hg : 0 < g) (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hx : 0 < x) (hdev : ∀ i : Fin r, |d i - (((i : ℕ) + 1 : ℕ) : ℝ) * g| ≤ η) (hC : ∀ y ∈ C, x ≤ y ∧ y ≤ (1 + ε) * x)
    (hgate : η * (1 / (((r : ℝ) + 1) * g)) < 1 / ((r : ℝ) + 1) - 1 / 8)
    (hsep : (r * g + η) / (2 * x) ≤ 2 * (1 / ((r : ℝ) + 1) - η * (1 / (((r : ℝ) + 1) * g)) - 1 / 8))
    (hclump : ε * (x * (1 / (((r : ℝ) + 1) * g)) + 2) ≤ 1 / 8) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, (1 / 8 : ℝ) ≤ distInt (d i * t)) ∧ ∀ y ∈ C, (1 / 8 : ℝ) ≤ distInt (y * t) := by
  have hrpos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  set σ : ℝ := 1 / (((r : ℝ) + 1) * g) with hσ
  have hσ0 : 0 < σ := by positivity
  set γ : ℝ := 1 / ((r : ℝ) + 1) - η * σ with hγ
  have hγ8 : 1 / 8 < γ := by linarith
  have hr7 : (r : ℝ) ≤ 6 := by exact_mod_cast hr
  -- the slow set as a Finset
  set S : Finset ℝ := Finset.univ.image d with hS
  have hSne : S.Nonempty := by
    haveI : Nonempty (Fin r) := ⟨⟨0, hr1⟩⟩
    exact ⟨d ⟨0, hr1⟩, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩⟩
  have hdpos : ∀ i, 0 < d i := by
    intro i
    have hi : (1 : ℝ) ≤ ((i : ℕ) + 1 : ℕ) := by exact_mod_cast Nat.succ_pos _
    have hgate' : η * σ < 1 / ((r : ℝ) + 1) - 1 / 8 := hgate
    have h1 := hdev i
    have hdi : (((i : ℕ) + 1 : ℕ) : ℝ) * g - η ≤ d i := by
      have := (abs_le.1 h1).1; linarith
    -- η < g: from the gate condition
    have hηg : η < g := by
      have hgσ : g * σ = 1 / ((r : ℝ) + 1) := by rw [hσ]; field_simp
      have : η * σ < g * σ := by rw [hgσ]; linarith
      exact lt_of_mul_lt_mul_right this hσ0.le
    nlinarith
  have hSpos : ∀ s ∈ S, 0 < s := by
    intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hs
    exact hdpos i
  have hM : ∀ s ∈ S, s ≤ (r : ℝ) * g + η := by
    intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hs
    have h1 := (abs_le.1 (hdev i)).2
    have hi : (((i : ℕ) + 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast i.2
    nlinarith
  have hgate_all : ∀ s ∈ S, γ ≤ distInt (s * σ) := by
    intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hs
    have hq := Fresh.APBlockFar.ap_quot_gate_full (by omega) i
    have hlip := Fresh.PathLaws.distInt_lipschitz (d i * σ) ((((i : ℕ) + 1 : ℕ) : ℝ) * g * σ)
    have e1 : (((i : ℕ) + 1 : ℕ) : ℝ) * g * σ = (((i : ℕ) + 1 : ℕ) : ℝ) * (1 / ((r : ℝ) + 1)) := by rw [hσ]; field_simp
    have e2 : d i * σ - (((i : ℕ) + 1 : ℕ) : ℝ) * g * σ = (d i - (((i : ℕ) + 1 : ℕ) : ℝ) * g) * σ := by ring
    have h3 : |d i * σ - (((i : ℕ) + 1 : ℕ) : ℝ) * g * σ| ≤ η * σ := by
      rw [e2, abs_mul, abs_of_pos hσ0]
      exact mul_le_mul_of_nonneg_right (hdev i) hσ0.le
    have hd : distInt ((((i : ℕ) + 1 : ℕ) : ℝ) * g * σ) = distInt ((((i : ℕ) + 1 : ℕ) : ℝ) * (1 / ((r : ℝ) + 1))) := by rw [e1]
    rw [hd] at hlip
    have h4 := (abs_le.1 hlip).1
    have h5 := (abs_le.1 h3).2
    have h6 := (abs_le.1 h3).1
    linarith [(abs_le.1 hlip).2]
  have hLM : 1 / (2 * x) * ((r : ℝ) * g + η) ≤ 2 * (γ - 1 / 8) := by
    rw [show 1 / (2 * x) * ((r : ℝ) * g + η) = ((r : ℝ) * g + η) / (2 * x) by ring]
    linarith
  have hgap := clump_gap hx hε hσ0.le hC hclump
  obtain ⟨t, ht, hSt, hCt⟩ := cluster_transfer_gap_below hγ8 hSne hSpos hM hσ0 hgate_all hLM hgap
  exact ⟨t, ht, fun i => hSt (d i) (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩), hCt⟩

#print axioms cluster_transfer_gap_below
#print axioms ap_slow_clump

end Fresh.APSlowClump
