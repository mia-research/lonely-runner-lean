import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.PathLaws
import Fresh.Grid
import Fresh.Admissible
import Fresh.AdmissibleFlank
import Fresh.ClusterTransfer
import Fresh.FarClusters
import Fresh.APBlockSlow

/-!
# A slow cluster under a near-AP fast block, with the thresholds by cluster size

Written 2026-10-25.  New file.  Worklist tags: A01 (the block is an AP `g, 2g, …, r g`), A04 (deviation at most `η` from the AP), G02 to G09 (two-group compositions `(7-r) | r`), H06.
`ap_block_far`: a slow set `S` (arbitrary positive reals, bounded by `M`) clear at gate `γ` at `σ`; an AP block `f i ≈ (i+1) g` within `η`, `r ≤ 6` readings, with `M ≤ 2 (γ - 1/8) g`; the deviation allowance
`η (σ + (γ - 1/8)/M) ≤ 1/(r+1) - 1/8`.  The block's quotient instant `1/(r+1)` is explicit: no order theorem is used for the block.
At the slow cluster's natural gate `1/(m+1)` (`m = |S|`, from the lower-order existence results) the separation `g/M` needed is `4/3, 12/5, 4, 20/3, 12, 28` for `m = 1, …, 6`.  Mechanisms: M-A (twice), M-B.  Grade [L].
-/

open Classical

namespace Fresh.APBlockFar

open Fresh Fresh.Admissible Fresh.AdmissibleFlank Fresh.ClusterTransfer Fresh.FarClusters Fresh.APBlockSlow

theorem ap_quot_gate_full {r : ℕ} (hr : r ≤ 7) (i : Fin r) :
    (1 / ((r : ℝ) + 1)) ≤ distInt ((((i : ℕ) + 1 : ℕ) : ℝ) * (1 / ((r : ℝ) + 1))) := by
  have hi : (i : ℕ) + 1 ≤ r := i.2
  have hiR : ((i : ℕ) : ℝ) + 1 ≤ r := by exact_mod_cast hi
  have hrpos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  apply gate_of_band (0 : ℤ) _ _ (by positivity)
  · push_cast
    rw [show ((i : ℕ) + 1 : ℝ) * (1 / ((r : ℝ) + 1)) = ((i : ℕ) + 1) / ((r : ℝ) + 1) by ring]
    rw [le_div_iff₀ hrpos]
    have : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
    have e : 1 / ((r : ℝ) + 1) * ((r : ℝ) + 1) = 1 := by field_simp
    linarith
  · push_cast
    rw [show ((i : ℕ) + 1 : ℝ) * (1 / ((r : ℝ) + 1)) = ((i : ℕ) + 1) / ((r : ℝ) + 1) by ring]
    rw [div_le_iff₀ hrpos]
    have e : 1 / ((r : ℝ) + 1) * ((r : ℝ) + 1) = 1 := by field_simp
    nlinarith

theorem ap_block_far {S : Finset ℝ} {r : ℕ} (hr : r ≤ 6) {f : Fin r → ℝ} {g M σ η γ : ℝ} (hSne : S.Nonempty) (hSpos : ∀ s ∈ S, 0 < s)
    (hM : ∀ s ∈ S, s ≤ M) (hσ0 : 0 < σ) (hγ : 1 / 8 < γ) (hσ : ∀ s ∈ S, γ ≤ distInt (s * σ)) (hg : M ≤ 2 * (γ - 1 / 8) * g)
    (hdev : ∀ i : Fin r, |f i - (((i : ℕ) + 1 : ℕ) : ℝ) * g| ≤ η) (hη : 0 ≤ η)
    (hallow : η * (σ + (γ - 1 / 8) / M) ≤ 1 / ((r : ℝ) + 1) - 1 / 8) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ S, (1 / 8 : ℝ) ≤ distInt (s * t)) ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (f i * t) := by
  have hr1 : (1 / 8 : ℝ) ≤ 1 / ((r : ℝ) + 1) := by
    have : (r : ℝ) + 1 ≤ 8 := by exact_mod_cast (by omega : r + 1 ≤ 8)
    exact one_div_le_one_div_of_le (by positivity) this
  exact far_clusters_gate (f := f) (n := fun i : Fin r => ((i : ℕ) + 1 : ℕ)) (σF := 1 / ((r : ℝ) + 1))
    (γ' := 1 / ((r : ℝ) + 1)) hSne hSpos hM hσ0 hγ hr1 hσ hg hdev hη (fun i => ap_quot_gate_full (by omega) i) hallow

-- STANDING: DEFINITION
def APBlockFarClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (S : Finset ℝ) (r : ℕ) (f : Fin r → ℝ) (g M σ η γ : ℝ), S.Nonempty ∧ (∀ s ∈ S, 0 < s) ∧ (∀ s ∈ S, s ≤ M) ∧ r ≤ 6 ∧ 0 < σ ∧ 1 / 8 < γ ∧
    (∀ s ∈ S, γ ≤ distInt (s * σ)) ∧ M ≤ 2 * (γ - 1 / 8) * g ∧ (∀ i : Fin r, |f i - (((i : ℕ) + 1 : ℕ) : ℝ) * g| ≤ η) ∧ 0 ≤ η ∧
    η * (σ + (γ - 1 / 8) / M) ≤ 1 / ((r : ℝ) + 1) - 1 / 8 ∧ ∀ d : ℝ, d ∈ disparitySet v k ↔ d ∈ S ∨ ∃ i, d = f i

theorem apBlockFar_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : APBlockFarClass v k) : Isolation v k := by
  obtain ⟨S, r, f, g, M, σ, η, γ, hSne, hSpos, hM, hr, hσ0, hγ, hσ, hg, hdev, hη, hallow, hmem⟩ := h
  obtain ⟨t, ht, hS, hF⟩ := ap_block_far hr hSne hSpos hM hσ0 hγ hσ hg hdev hη hallow
  refine ⟨t, ht, ?_⟩
  rw [Fresh.Localisation.isolatedAt_iff]
  intro d hd
  rcases (hmem d).1 hd with hs | ⟨i, rfl⟩
  · exact hS d hs
  · exact hF i

#print axioms ap_block_far
#print axioms apBlockFar_isolation

end Fresh.APBlockFar
