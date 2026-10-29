import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.ClusterTransfer
import Fresh.ChainNested2
import Fresh.EightResidualOpenFree

/-!
# The slow cluster's exact clear window, and the residual it removes

Written 2026-10-25.  New file.  Worklist tags: G02 to G11, H06, A07.  `cluster_transfer_window`: if every element of `S` is `1/8`-clear on a closed interval `[lo, hi]` with `lo > 0` and the fast part has a bounded gap
`L ≤ hi - lo` (`ClearGap T L`, or a chain, `ChainNested2`), one instant clears everything.  This replaces the gate-and-Lipschitz window of `cluster_transfer_gap` by the exact interval, which is computable from the readings
(for whole numbers: the intersection of the `S`-bands over one period); it needs no order theorem and loses nothing to the Lipschitz estimate.
`WindowChainSet ds`: a partition `ds = S ∪ L ∪ T`, an exact window `[lo, hi]` of `S`, a chain `L` under `ChainOK2` and a terminal `T` with `ClearGap T LT`, and `gap2 LT L ≤ hi - lo`; `windowChainSet_lonely`.
`ResidualRest3` is `ResidualRest2` with `WindowChainSet` also excluded (`-- STANDING: OWED`); `residualRest2_of_rest3`.  Integer/commensurable statement.  **[PROVISIONAL: covering]**: the fast part's blocked zones do not cover the window, from `gap2 ≤ hi - lo`.  Grade [L] modulo `ResidualRest3`.
-/

open Classical

namespace Fresh.ClusterWindow

open Fresh Fresh.ClusterTransfer Fresh.ChainNested2 Fresh.EightResidualOpen Fresh.ResidualDischarge Fresh.EightResidualNative LRC.OrderEightN LRC.ParityDescent

theorem cluster_transfer_window {S T : Finset ℝ} {lo hi L : ℝ} (hlo : 0 < lo) (hS : ∀ t : ℝ, lo ≤ t → t ≤ hi → ∀ s ∈ S, (1 / 8 : ℝ) ≤ distInt (s * t))
    (hL : L ≤ hi - lo) (hgap : ClearGap T L) :
    ∃ t : ℝ, 0 < t ∧ (∀ s ∈ S, (1 / 8 : ℝ) ≤ distInt (s * t)) ∧ ∀ f ∈ T, (1 / 8 : ℝ) ≤ distInt (f * t) := by
  obtain ⟨t, ht1, ht2, htT⟩ := hgap lo
  exact ⟨t, by linarith, hS t ht1 (by linarith), htT⟩

-- STANDING: DEFINITION
def WindowChainSet (ds : Finset ℝ) : Prop :=
  ∃ (S T : Finset ℝ) (L : List ℝ) (LT lo hi : ℝ), 0 < lo ∧ 0 ≤ LT ∧ (∀ t : ℝ, lo ≤ t → t ≤ hi → ∀ s ∈ S, (1 / 8 : ℝ) ≤ distInt (s * t)) ∧
    ClearGap T LT ∧ ChainOK2 LT L ∧ gap2 LT L ≤ hi - lo ∧ ∀ d : ℝ, d ∈ ds ↔ d ∈ S ∨ d ∈ L ∨ d ∈ T

theorem windowChainSet_lonely {ds : Finset ℝ} (h : WindowChainSet ds) : ∃ t : ℝ, 0 < t ∧ ∀ d ∈ ds, (1 / 8 : ℝ) ≤ distInt (d * t) := by
  obtain ⟨S, T, L, LT, lo, hi, hlo, hLT, hS, hT, hL, hgap, hmem⟩ := h
  have hgp : ClearGap (T ∪ L.toFinset) (gap2 LT L) := by
    intro a
    obtain ⟨u, h1, h2, h3, h4⟩ := chain_gap2 hLT hT L hL a
    refine ⟨u, h1, h2, fun f hf => ?_⟩
    rcases Finset.mem_union.1 hf with hf | hf
    · exact h4 f hf
    · exact h3 f (List.mem_toFinset.1 hf)
  obtain ⟨t, ht, hSt, hFt⟩ := cluster_transfer_window hlo hS hgap hgp
  refine ⟨t, ht, fun d hd => ?_⟩
  rcases (hmem d).1 hd with h | h | h
  · exact hSt d h
  · exact hFt d (Finset.mem_union_right _ (List.mem_toFinset.2 h))
  · exact hFt d (Finset.mem_union_left _ h)

-- STANDING: OWED
def ResidualRest3 : Prop :=
  ∀ R : Finset ℕ, (∀ d ∈ R, 0 < d) → EightResidual R →
    ¬ SettledCounts8' (R.filter (fun d => 8 ∣ d)).card (R.filter (fun d => ¬ 2 ∣ d)).card
        (R.filter (fun d => d % 4 = 2)).card (R.filter (fun d => d % 8 = 4)).card →
    ¬ OottCase8 R → ¬ ChainSet (R.image (fun d : ℕ => (d : ℝ))) → ¬ FixedRSet (R.image (fun d : ℕ => (d : ℝ))) →
    ¬ WindowChainSet (R.image (fun d : ℕ => (d : ℝ))) →
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ R, (1 / 8 : ℝ) ≤ distInt ((d : ℝ) * t)

theorem residualRest2_of_rest3 (h : ResidualRest3) : ResidualRest2 := by
  intro R hpos hR hs ho hc hf
  by_cases hw : WindowChainSet (R.image (fun d : ℕ => (d : ℝ)))
  · obtain ⟨t, ht, hl⟩ := windowChainSet_lonely hw
    exact ⟨t, ht, fun d hd => hl (d : ℝ) (Finset.mem_image.2 ⟨d, hd, rfl⟩)⟩
  · exact h R hpos hR hs ho hc hf hw

theorem isolation_of_rest3 (h : ResidualRest3) {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) (k : Fin 8) : Isolation v k :=
  isolation_of_rest2 (residualRest2_of_rest3 h) hv k

#print axioms windowChainSet_lonely
#print axioms isolation_of_rest3

end Fresh.ClusterWindow
