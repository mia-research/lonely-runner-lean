import Fresh.ArrangementTypesOct26
import Fresh.NativePositivePointCanonical

/-! Coalescence of the 2026-10-26 catalogue (log E645).
Since `NativePositivePointCanonical.isolation_iff_canonical` (V82), the 21st alternative of `NewTypes`,
`CanonicalReturnClass`, is equivalent to isolation of the subject. So every alternative of `NewTypes`
coalesces into that one, `NewTypes`, `Types` and `TypesUp` are each equivalent to isolation on ordered
arrangements, and `ReducedAdmissible` is exactly the set of ordered arrangements whose subject is not
isolated. These are restatements of the obligation (map v5 section 5), not reductions of it.
-/
namespace Fresh.CatalogueCoalescence
open Fresh Fresh.ArrangementTypesOct26

theorem ordered_isArrangement {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) : IsArrangement v :=
  ⟨hv.1, hv.2.injective⟩

theorem newTypes_iff_isolation {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) :
    NewTypes v k ↔ Isolation v k :=
  ⟨newTypes_isolation, fun h =>
    canonicalReturn_into_newTypes k ((Fresh.NativePositivePointCanonical.isolation_iff_canonical hv k).1 h)⟩

theorem types_iff_isolation {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) (k : Fin 8) :
    Types v k ↔ Isolation v k :=
  ⟨types_isolation hv, fun h => Or.inr ((newTypes_iff_isolation (ordered_isArrangement hv) k).2 h)⟩

theorem typesUp_iff_isolation {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) (k : Fin 8) :
    TypesUp v k ↔ Isolation v k :=
  ⟨typesUp_isolation hv, fun h => types_imp_up ((types_iff_isolation hv k).2 h)⟩

/-- The remainder of the catalogue is exactly the counterexamples. -/
theorem reducedAdmissible_iff_not_isolation {v : Fin 8 → ℝ} (k : Fin 8) :
    ReducedAdmissible v k ↔ IsOrderedArrangement v ∧ ¬ Isolation v k := by
  constructor
  · rintro ⟨hv, hn⟩
    exact ⟨hv, fun h => hn ((typesUp_iff_isolation hv k).2 h)⟩
  · rintro ⟨hv, hn⟩
    exact ⟨hv, fun h => hn (typesUp_isolation hv h)⟩

#print axioms newTypes_iff_isolation
#print axioms types_iff_isolation
#print axioms typesUp_iff_isolation
#print axioms reducedAdmissible_iff_not_isolation
end Fresh.CatalogueCoalescence
