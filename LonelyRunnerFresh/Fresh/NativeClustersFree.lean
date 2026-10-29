import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Admissible
import Fresh.AdmissibleFlank
import Fresh.ClusterTransfer
import Fresh.FastGaps
import Fresh.PairGapHalf
import Fresh.ChainNested2
import Fresh.NativeOrdersFree

/-!
# Cluster classes with the native lower-order gates

Written 2026-10-25.  New file.  Worklist tags: G02 to G11 (cluster placement), G03 and G05 (one or two fast readings over a low cluster), H06, H01 to H03 (chained windows).
A slow cluster `S` of `m` disparities (`1 ≤ m ≤ 6`) has an instant clearing all of it at gate `1/(m+1)` (`NativeOrders`: orders two to seven, ported).  With the cluster window of half-width
`(1/(m+1) - 1/8)/M` (M-A) and a fast part with a bounded gap (a chain of rungs, `ChainNested2`, ending in a single reading or an arbitrary pair, `FastGaps`, `PairGapHalf`) one instant clears everything.
`slow_gate`: the gate instant for every slow set of size `1..6`.  `cluster_chain_isolation`: the class `ClusterChainClass`.  Threshold on the first fast reading `h` (single fast part, `LT = 1/(4h)`):
`h ≥ (m+1) M / (7-m)`; pair fast part (`LT = 1/(2a)`): `a ≥ 2 (m+1) M / (7-m)` (`m = 5`: `6 M`).  Mechanisms: M-A nested.  Grade [L].
-/

open Classical

namespace Fresh.NativeClusters

open Fresh Fresh.Admissible Fresh.AdmissibleFlank Fresh.ClusterTransfer Fresh.ChainNested2 Fresh.NativeOrdersFree

theorem slow_gate {S : Finset ℝ} (hpos : ∀ s ∈ S, 0 < s) (hne : S.Nonempty) (hcard : S.card ≤ 6) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ s ∈ S, (1 : ℝ) / ((S.card : ℝ) + 1) ≤ distInt (s * σ) := by
  have h1 : 1 ≤ S.card := Finset.card_pos.2 hne
  interval_cases hc : S.card
  · obtain ⟨σ, hσ, h⟩ := clear_two hpos hc.le
    exact ⟨σ, hσ, fun s hs => by have := h s hs; norm_num at this ⊢; linarith⟩
  · obtain ⟨σ, hσ, h⟩ := clear_three hpos hc.le
    exact ⟨σ, hσ, fun s hs => by have := h s hs; norm_num at this ⊢; linarith⟩
  · obtain ⟨σ, hσ, h⟩ := clear_four hpos hc.le
    exact ⟨σ, hσ, fun s hs => by have := h s hs; norm_num at this ⊢; linarith⟩
  · obtain ⟨σ, hσ, h⟩ := clear_five hpos hc.le
    exact ⟨σ, hσ, fun s hs => by have := h s hs; norm_num at this ⊢; linarith⟩
  · obtain ⟨σ, hσ, h⟩ := clear_six hpos hc.le
    exact ⟨σ, hσ, fun s hs => by have := h s hs; norm_num at this ⊢; linarith⟩
  · obtain ⟨σ, hσ, h⟩ := clear_seven hpos hc.le
    exact ⟨σ, hσ, fun s hs => by have := h s hs; norm_num at this ⊢; linarith⟩

-- STANDING: DEFINITION
def ClusterChainClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (S T : Finset ℝ) (L : List ℝ) (LT M : ℝ), S.Nonempty ∧ (∀ s ∈ S, 0 < s) ∧ S.card ≤ 6 ∧ (∀ s ∈ S, s ≤ M) ∧ 0 ≤ LT ∧
    ClearGap T LT ∧ ChainOK2 LT L ∧ gap2 LT L * M ≤ 2 * (1 / ((S.card : ℝ) + 1) - 1 / 8) ∧
    ∀ d : ℝ, d ∈ disparitySet v k ↔ d ∈ S ∨ d ∈ L ∨ d ∈ T

theorem cluster_chain_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ClusterChainClass v k) : Isolation v k := by
  obtain ⟨S, T, L, LT, M, hSne, hSpos, hScard, hM, hLT, hT, hL, hgap, hmem⟩ := h
  obtain ⟨σ, hσ0, hσ⟩ := slow_gate hSpos hSne hScard
  have hγ : (1 : ℝ) / 8 < 1 / ((S.card : ℝ) + 1) := by
    have : (S.card : ℝ) + 1 ≤ 7 := by exact_mod_cast (by omega : S.card + 1 ≤ 7)
    have hc1 : (1 : ℝ) ≤ S.card := by exact_mod_cast Finset.card_pos.2 hSne
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  obtain ⟨t, ht, hS, hLs, hTs⟩ := cluster_chain2 hLT hγ hSne hSpos hM hσ0 hσ hT hL hgap
  refine ⟨t, ht, ?_⟩
  rw [Fresh.Localisation.isolatedAt_iff]
  intro d hd
  rcases (hmem d).1 hd with h | h | h
  · exact hS d h
  · exact hLs d h
  · exact hTs d h

#print axioms slow_gate
#print axioms cluster_chain_isolation

end Fresh.NativeClusters
