import Fresh.CatalogueCoalescence
import Fresh.TwoBlockCoalescence

/-! A root for the arrangement types without the free-instant alternative (log E646).
`ShapeAlternatives` is `NewTypes` with its 21st disjunct `CanonicalReturnClass` removed (that disjunct is isolation
itself, E645). The nine two-block alternatives enter through `TwoBlockClass`, their common template. `ShapeTypes` adds
the proved types of my chain (`TypesProvedRUp`); `ShapeUp` closes under positive scale; `ShapeAdmissible` is the
remainder. No claim is made here that `ShapeAdmissible` is empty, finite, or different from the counterexamples;
its definition does not mention isolation.
-/
namespace Fresh.ShapeRoot
open Fresh Fresh.ArrangementTypesOct26 Fresh.ProvedTypesR Fresh.ProvedTypesScale

-- STANDING: DEFINITION
def ShapeAlternatives (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  Fresh.APCoreOpening.APCoreOpeningClass v k ∨
  Fresh.SplitAPBands.SplitAPReadingsClass v k ∨
  Fresh.SplitAPBands.SignedAPReadingsClass v k ∨
  Fresh.SplitAPArrangement.GeneralTwoAPBlockClass v ∨
  Fresh.TrainFlankPair.PairTrainOpeningClass v k ∨
  Fresh.TrainFlank.TwoSlowTrainClass v k ∨
  Fresh.UnequalAPArrangement.UnequalTwoAPBlockClass v ∨
  Fresh.TwoBlockCoalescence.TwoBlockClass v ∨
  Fresh.FourBlockDoubleSingletonArrangement.DoubleCoveredClass v ∨
  Fresh.ThreeBlockReverseMiddlePartitions.ThreeBlockReverseMiddlePartitionsClass v ∨
  Fresh.ThreeGapPacketBand.ThreeGapPacketClass v k ∨
  Fresh.FourAPPairsNativeClass.FourPairNativeClass v k ∨
  Fresh.FourBlockNeighbour.FourBlockInternalClass v k ∨
  Fresh.ThreeBlockPartitionBypassClass.PartitionNativeBypassClass v k ∨
  Fresh.FourPairStepIndependentPhysical.FourPairStepIndependentClass v k ∨
  Fresh.OneMover.TwoMoverSubjectClass v

/-- Every alternative of `NewTypes` other than the canonical one is a shape alternative, and conversely. -/
theorem newTypes_iff_shape_or_canonical {v : Fin 8 → ℝ} {k : Fin 8} :
    NewTypes v k ↔ ShapeAlternatives v k ∨ Fresh.NativeCanonicalReturn.CanonicalReturnClass v k := by
  unfold NewTypes ShapeAlternatives
  constructor
  · rintro (h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · -- four-by-four mixed: three mixed classes and the uniform class, all two-block
      refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))
      apply Fresh.TwoBlockCoalescence.nine_imp_twoBlock
      rcases h with h|h|h|h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
    · refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))
      apply Fresh.TwoBlockCoalescence.nine_imp_twoBlock
      rcases h with h|h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (Fresh.TwoBlockCoalescence.nine_imp_twoBlock (Or.inl h))))))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (Fresh.TwoBlockCoalescence.nine_imp_twoBlock (Or.inr (Or.inl h)))))))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (Fresh.TwoBlockCoalescence.nine_imp_twoBlock (Or.inr (Or.inr (Or.inl h))))))))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))
    · exact Or.inr h
  · rintro (h|h)
    · rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · rcases Fresh.TwoBlockCoalescence.twoBlock_imp_nine h with h|h|h|h|h|h|h|h|h
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h)))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h)))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl h)))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl h))))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr h))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))
    · exact canonicalReturn_into_newTypes k h

theorem shapeAlternatives_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ShapeAlternatives v k) :
    Isolation v k :=
  newTypes_isolation ((newTypes_iff_shape_or_canonical).2 (Or.inl h))

-- STANDING: DEFINITION
def ShapeTypes (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  TypesProvedRUp v k ∨ ShapeAlternatives v k

-- STANDING: DEFINITION
def ShapeUp (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ShapeTypes (fun j => c*v j) k

-- STANDING: DEFINITION
def ShapeAdmissible (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsOrderedArrangement v ∧ ¬ ShapeUp v k

theorem shapeTypes_isolation {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) {k : Fin 8}
    (h : ShapeTypes v k) : Isolation v k := by
  rcases h with h|h
  · exact typesProvedRUp_isolation hv h
  · exact shapeAlternatives_isolation h

theorem shapeUp_isolation {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) {k : Fin 8}
    (h : ShapeUp v k) : Isolation v k := by
  obtain ⟨c,hc,h⟩ := h
  exact (Isolation_smul hc).1 (shapeTypes_isolation (orderedArrangement_smul hc hv) h)

theorem shapeUp_or_admissible {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) (k : Fin 8) :
    ShapeUp v k ∨ ShapeAdmissible v k := by
  by_cases h : ShapeUp v k
  · exact Or.inl h
  · exact Or.inr ⟨hv,h⟩

/-- The old remainder is the new one minus the canonical class (scaled). -/
theorem reduced_imp_shapeAdmissible {v : Fin 8 → ℝ} {k : Fin 8} (h : ReducedAdmissible v k) :
    ShapeAdmissible v k := by
  refine ⟨h.1, fun ⟨c,hc,hs⟩ => h.2 ⟨c,hc,?_⟩⟩
  rcases hs with hs|hs
  · exact Or.inl hs
  · exact Or.inr ((newTypes_iff_shape_or_canonical).2 (Or.inl hs))

theorem shapeAdmissible_smul {c : ℝ} (hc : 0 < c) {v : Fin 8 → ℝ} {k : Fin 8} :
    ShapeAdmissible (fun j => c*v j) k ↔ ShapeAdmissible v k := by
  have key : ShapeUp (fun j => c*v j) k ↔ ShapeUp v k := by
    constructor
    · rintro ⟨b,hb,h⟩
      refine ⟨b*c,by positivity,?_⟩
      have he : (fun j => b*(c*v j)) = (fun j => (b*c)*v j) := by funext j; ring
      rwa [he] at h
    · rintro ⟨b,hb,h⟩
      refine ⟨b/c,by positivity,?_⟩
      have he : (fun j => b/c*(c*v j)) = (fun j => b*v j) := by funext j; field_simp
      rwa [he]
  constructor
  · rintro ⟨hv,hn⟩
    have hv' : IsOrderedArrangement v := by
      have := orderedArrangement_smul (inv_pos.mpr hc) hv
      have he : (fun j => c⁻¹*(c*v j)) = v := by funext j; field_simp
      rwa [he] at this
    exact ⟨hv', fun h => hn (key.2 h)⟩
  · rintro ⟨hv,hn⟩
    exact ⟨orderedArrangement_smul hc hv, fun h => hn (key.1 h)⟩

#print axioms newTypes_iff_shape_or_canonical
#print axioms shapeUp_isolation
#print axioms shapeUp_or_admissible
#print axioms reduced_imp_shapeAdmissible
#print axioms shapeAdmissible_smul
end Fresh.ShapeRoot
