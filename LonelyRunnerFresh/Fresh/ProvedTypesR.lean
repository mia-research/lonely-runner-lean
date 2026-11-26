import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Admissible
import Fresh.AdmissibleFlank
import Fresh.ProvedTypes
import Fresh.ProvedTypesScale
import Fresh.FixedRClass

/-!
# The proved types with the fixed-instant list, up to scale

Written 2026-10-25.  New file.  `TypesProvedR := TypesProved ∨ FixedRList`; `AdmissibleR` is the remainder (ordered arrangements outside every proved type and clear at none of the listed instants `R = 8a/b`, `b ≤ 12`, `a ≤ 8b`);
`typesProvedR_isolation`, `typesProvedR_or_admissible`; the version up to positive scale (`TypesProvedRUp`, `typesProvedRUp_isolation`, `typesProvedRUp_or_admissible`, `TypesProvedRUp_smul`).
The free-unit class `NearMultiplesClass` is NOT included (it is equivalent to isolation, `NearMultiples.isolation_imp_nearMultiples`).  Grade [L].
-/

namespace Fresh.ProvedTypesR

open Fresh Fresh.Admissible Fresh.AdmissibleFlank Fresh.ProvedTypes Fresh.ProvedTypesScale Fresh.FixedRClass

-- STANDING: DEFINITION
def TypesProvedR (v : Fin 8 → ℝ) (k : Fin 8) : Prop := TypesProved v k ∨ FixedRList v k

-- STANDING: DEFINITION
def AdmissibleR (v : Fin 8 → ℝ) (k : Fin 8) : Prop := IsOrderedArrangement v ∧ ¬ TypesProvedR v k

theorem typesProvedR_isolation {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) {k : Fin 8} (h : TypesProvedR v k) : Isolation v k := by
  rcases h with h | h
  · exact typesProved_isolation hv h
  · exact fixedRList_isolation h

theorem typesProvedR_or_admissible {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) (k : Fin 8) :
    TypesProvedR v k ∨ AdmissibleR v k := by
  by_cases h : TypesProvedR v k
  · exact Or.inl h
  · exact Or.inr ⟨hv, h⟩

-- STANDING: DEFINITION
def TypesProvedRUp (v : Fin 8 → ℝ) (k : Fin 8) : Prop := ∃ c : ℝ, 0 < c ∧ TypesProvedR (fun j => c * v j) k

-- STANDING: DEFINITION
def AdmissibleRUp (v : Fin 8 → ℝ) (k : Fin 8) : Prop := IsOrderedArrangement v ∧ ¬ TypesProvedRUp v k

theorem typesProvedRUp_isolation {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) {k : Fin 8} (h : TypesProvedRUp v k) : Isolation v k := by
  obtain ⟨c, hc, hT⟩ := h
  exact (Isolation_smul hc).1 (typesProvedR_isolation (orderedArrangement_smul hc hv) hT)

theorem typesProvedRUp_or_admissible {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) (k : Fin 8) :
    TypesProvedRUp v k ∨ AdmissibleRUp v k := by
  by_cases h : TypesProvedRUp v k
  · exact Or.inl h
  · exact Or.inr ⟨hv, h⟩

theorem TypesProvedRUp_smul {c : ℝ} (hc : 0 < c) {v : Fin 8 → ℝ} {k : Fin 8} :
    TypesProvedRUp (fun j => c * v j) k ↔ TypesProvedRUp v k := by
  constructor
  · rintro ⟨c', hc', h⟩
    refine ⟨c' * c, by positivity, ?_⟩
    have e : (fun j => c' * (c * v j)) = (fun j => c' * c * v j) := by funext j; ring
    rwa [e] at h
  · rintro ⟨c', hc', h⟩
    refine ⟨c' / c, by positivity, ?_⟩
    have e : (fun j => c' / c * (c * v j)) = (fun j => c' * v j) := by funext j; field_simp
    rwa [e]

#print axioms typesProvedRUp_isolation
#print axioms TypesProvedRUp_smul

end Fresh.ProvedTypesR
