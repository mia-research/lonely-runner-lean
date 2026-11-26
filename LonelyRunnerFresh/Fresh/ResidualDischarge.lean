import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.ClusterTransfer
import Fresh.ChainNested2
import Fresh.NativeClusters
import Fresh.NativeOrders
import Fresh.EightResidualNative

/-!
# Discharging part of the whole-number residual with the real types

Written 2026-10-25.  New file.  `ChainSet ds` (set-level form of `NativeClusters.ClusterChainClass`: a slow cluster at its native gate, singleton rungs, a terminal single or pair) and `FixedRSet ds` (a fixed instant
`a/(b d_min)` clears every element, `b ≤ 12`, `a ≤ 8b`) are classes of finite sets of positive reals; each gives a common `1/8`-clear instant (`chainSet_lonely`, `fixedRSet_lonely`).
`ResidualRest` is `ResidualLonely8` restricted to the `EightResidual` sets that are in neither class (`-- STANDING: OWED`); `residualLonely8_of_rest`: `ResidualRest → ResidualLonely8`.  So the owed whole-number residual
is reduced by the real types of E634 to E636 to the sets they do not reach.  Integer/commensurable statement (the sets are whole numbers); the classes themselves are about reals.  **[PROVISIONAL: covering]** as in `NativeClusters`.  Grade [L] modulo `ResidualRest`.
-/

open Classical

namespace Fresh.ResidualDischarge

open Fresh Fresh.ClusterTransfer Fresh.ChainNested2 Fresh.NativeOrders Fresh.NativeClusters Fresh.EightResidualNative LRC.OrderEightN

-- STANDING: DEFINITION
def ChainSet (ds : Finset ℝ) : Prop :=
  ∃ (S T : Finset ℝ) (L : List ℝ) (LT M : ℝ), S.Nonempty ∧ (∀ s ∈ S, 0 < s) ∧ S.card ≤ 6 ∧ (∀ s ∈ S, s ≤ M) ∧ 0 ≤ LT ∧
    ClearGap T LT ∧ ChainOK2 LT L ∧ gap2 LT L * M ≤ 2 * (1 / ((S.card : ℝ) + 1) - 1 / 8) ∧
    ∀ d : ℝ, d ∈ ds ↔ d ∈ S ∨ d ∈ L ∨ d ∈ T

theorem chainSet_lonely {ds : Finset ℝ} (h : ChainSet ds) : ∃ t : ℝ, 0 < t ∧ ∀ d ∈ ds, (1 / 8 : ℝ) ≤ distInt (d * t) := by
  obtain ⟨S, T, L, LT, M, hSne, hSpos, hScard, hM, hLT, hT, hL, hgap, hmem⟩ := h
  obtain ⟨σ, hσ0, hσ⟩ := slow_gate hSpos hSne hScard
  have hγ : (1 : ℝ) / 8 < 1 / ((S.card : ℝ) + 1) := by
    have : (S.card : ℝ) + 1 ≤ 7 := by exact_mod_cast (by omega : S.card + 1 ≤ 7)
    have hc1 : (1 : ℝ) ≤ S.card := by exact_mod_cast Finset.card_pos.2 hSne
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  obtain ⟨t, ht, hS, hLs, hTs⟩ := cluster_chain2 hLT hγ hSne hSpos hM hσ0 hσ hT hL hgap
  refine ⟨t, ht, fun d hd => ?_⟩
  rcases (hmem d).1 hd with h | h | h
  · exact hS d h
  · exact hLs d h
  · exact hTs d h

-- STANDING: DEFINITION
def FixedRSet (ds : Finset ℝ) : Prop :=
  ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ b ≤ 12 ∧ a ≤ 8 * b ∧ ∃ m : ℝ, IsLeast (ds : Set ℝ) m ∧ 0 < m ∧
    ∀ d ∈ ds, (1 / 8 : ℝ) ≤ distInt (d * ((a : ℝ) / ((b : ℝ) * m)))

theorem fixedRSet_lonely {ds : Finset ℝ} (h : FixedRSet ds) : ∃ t : ℝ, 0 < t ∧ ∀ d ∈ ds, (1 / 8 : ℝ) ≤ distInt (d * t) := by
  obtain ⟨a, b, ha, hb, _, _, m, _, hm0, hcl⟩ := h
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  exact ⟨(a : ℝ) / ((b : ℝ) * m), by positivity, hcl⟩

-- STANDING: OWED
def ResidualRest : Prop :=
  ∀ R : Finset ℕ, (∀ d ∈ R, 0 < d) → EightResidual R → ¬ ChainSet (R.image (fun d : ℕ => (d : ℝ))) →
    ¬ FixedRSet (R.image (fun d : ℕ => (d : ℝ))) → ∃ t : ℝ, 0 < t ∧ ∀ d ∈ R, (1 / 8 : ℝ) ≤ distInt ((d : ℝ) * t)

theorem residualLonely8_of_rest (h : ResidualRest) : ResidualLonely8 := by
  intro R hpos hR
  by_cases hc : ChainSet (R.image (fun d : ℕ => (d : ℝ)))
  · obtain ⟨t, ht, hl⟩ := chainSet_lonely hc
    exact ⟨t, ht, fun d hd => hl (d : ℝ) (Finset.mem_image.2 ⟨d, hd, rfl⟩)⟩
  by_cases hf : FixedRSet (R.image (fun d : ℕ => (d : ℝ)))
  · obtain ⟨t, ht, hl⟩ := fixedRSet_lonely hf
    exact ⟨t, ht, fun d hd => hl (d : ℝ) (Finset.mem_image.2 ⟨d, hd, rfl⟩)⟩
  exact h R hpos hR hc hf

#print axioms chainSet_lonely
#print axioms residualLonely8_of_rest

end Fresh.ResidualDischarge
