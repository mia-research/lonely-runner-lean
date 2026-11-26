import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Admissible
import Fresh.AdmissibleFlank
import Fresh.AdmissibleMore
import Fresh.FreeStepSeven
import Fresh.NativeOrders
import Fresh.LadderNested
import Fresh.NativeClusters
import Fresh.APBlockSlow
import Fresh.APBlockFar
import Fresh.ClumpClasses

/-!
# All proved types in one predicate, and the remainder

Written 2026-10-25.  New file.  `TypesProved v k` is the disjunction of every class proved in `Fresh/` that carries an isolation theorem, each tagged by its worklist rows:
* `MoreProved` (E628 to E632): grid, ratio at most 7, unblocked `d_min` instant, near-AP neighbourhood, one mover, first-lap flank, fast pair (`9c ≤ a`), no common multiple of some `q ≤ 8` [A01 to A04, A08, G05];
* `OneFreeClass`, `BlockSplitClass` (E633) [G02 to G08, H06];
* `LadderClass` (E634) [G02];
* `ClusterChainClass` (E634): slow cluster at its native gate, singleton rungs, terminal single or pair [G02 to G11, H01 to H06];
* `APBlockSlowClass`, `APBlockFarClass` (E634) [A01, A04, G04];
* `SlowOneClumpClass`, `APSlowClumpClass` (E635) [G03, G04, G12].
`typesProved_isolation`; `AdmissibleTypes := IsOrderedArrangement ∧ ¬ TypesProved` is the current admissible remainder (`typesProved_or_admissible`: every ordered arrangement is in a proved type or in the remainder).
Each class is a statement about the subject's disparity set only (a union of the classes' own conditions), so the remainder is again a statement about one subject.  Grade [L]; the covering tags of the component classes apply.
-/

open Classical

namespace Fresh.ProvedTypes

open Fresh Fresh.Admissible Fresh.AdmissibleFlank Fresh.AdmissibleMore Fresh.FreeStep

-- STANDING: DEFINITION
def TypesProved (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  MoreProved v k ∨ OneFreeClass v k ∨ BlockSplitClass v k ∨ Fresh.LadderNested.LadderClass v k ∨
    Fresh.NativeClusters.ClusterChainClass v k ∨ Fresh.APBlockSlow.APBlockSlowClass v k ∨ Fresh.APBlockFar.APBlockFarClass v k ∨
    Fresh.ClumpClasses.SlowOneClumpClass v k ∨ Fresh.ClumpClasses.APSlowClumpClass v k

-- STANDING: DEFINITION
def AdmissibleTypes (v : Fin 8 → ℝ) (k : Fin 8) : Prop := IsOrderedArrangement v ∧ ¬ TypesProved v k

theorem typesProved_isolation {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) {k : Fin 8} (h : TypesProved v k) : Isolation v k := by
  rcases h with h | h | h | h | h | h | h | h | h
  · exact moreProved_isolation hv h
  · exact oneFree_isolation Fresh.NativeOrders.sevenClear6_proved hv.2.injective h
  · exact blockSplit_isolation Fresh.NativeOrders.sevenClear6_proved hv.2.injective h
  · exact Fresh.LadderNested.ladder_isolation h
  · exact Fresh.NativeClusters.cluster_chain_isolation h
  · exact Fresh.APBlockSlow.apBlockSlow_isolation h
  · exact Fresh.APBlockFar.apBlockFar_isolation h
  · exact Fresh.ClumpClasses.slowOneClump_isolation h
  · exact Fresh.ClumpClasses.apSlowClump_isolation h

theorem typesProved_or_admissible {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) (k : Fin 8) :
    TypesProved v k ∨ AdmissibleTypes v k := by
  by_cases h : TypesProved v k
  · exact Or.inl h
  · exact Or.inr ⟨hv, h⟩

theorem admissibleTypes_iff {v : Fin 8 → ℝ} {k : Fin 8} : AdmissibleTypes v k ↔ IsOrderedArrangement v ∧ ¬ TypesProved v k := Iff.rfl

theorem admissibleTypes_imp_admissibleMore {v : Fin 8 → ℝ} {k : Fin 8} (h : AdmissibleTypes v k) : AdmissibleMore v k :=
  ⟨h.1, fun hm => h.2 (Or.inl hm)⟩

#print axioms typesProved_isolation
#print axioms typesProved_or_admissible

end Fresh.ProvedTypes
