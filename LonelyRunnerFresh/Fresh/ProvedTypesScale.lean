import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Admissible
import Fresh.AdmissibleFlank
import Fresh.ProvedTypes

/-!
# The proved types up to positive scale

Written 2026-10-25.  New file.  `Isolation_smul`: isolation is invariant under `v ↦ c v`, `c > 0`.  `TypesProvedUp v k := ∃ c > 0, TypesProved (c v) k`, which is scale invariant by construction
(`TypesProvedUp_smul`), and `AdmissibleUp` its complement among ordered arrangements; `typesProvedUp_isolation`, `typesProvedUp_or_admissible`.  So the remainder after all proved types is a statement
about the arrangement up to scale, as the programme needs, without a separate invariance proof for each class.  Grade [L].
-/

namespace Fresh.ProvedTypesScale

open Fresh Fresh.Admissible Fresh.AdmissibleFlank Fresh.ProvedTypes

theorem Isolation_smul_of {c : ℝ} (hc : 0 < c) {v : Fin 8 → ℝ} {k : Fin 8} (h : Isolation (fun j => c * v j) k) : Isolation v k := by
  obtain ⟨t, ht, hiso⟩ := h
  rw [Fresh.Localisation.isolatedAt_iff] at hiso
  refine ⟨c * t, by positivity, ?_⟩
  rw [Fresh.Localisation.isolatedAt_iff]
  intro d hd
  have := hiso (c * d) ((mem_disp_smul hc v k _).2 ⟨d, hd, rfl⟩)
  rwa [show c * d * t = d * (c * t) by ring] at this

theorem Isolation_smul {c : ℝ} (hc : 0 < c) {v : Fin 8 → ℝ} {k : Fin 8} : Isolation (fun j => c * v j) k ↔ Isolation v k := by
  constructor
  · exact Isolation_smul_of hc
  · rintro ⟨t, ht, hiso⟩
    rw [Fresh.Localisation.isolatedAt_iff] at hiso
    refine ⟨t / c, by positivity, ?_⟩
    rw [Fresh.Localisation.isolatedAt_iff]
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := (mem_disp_smul hc v k d').1 hd'
    have := hiso d hd
    rwa [show c * d * (t / c) = d * t by field_simp]

-- STANDING: DEFINITION
def TypesProvedUp (v : Fin 8 → ℝ) (k : Fin 8) : Prop := ∃ c : ℝ, 0 < c ∧ TypesProved (fun j => c * v j) k

-- STANDING: DEFINITION
def AdmissibleUp (v : Fin 8 → ℝ) (k : Fin 8) : Prop := IsOrderedArrangement v ∧ ¬ TypesProvedUp v k

theorem orderedArrangement_smul {c : ℝ} (hc : 0 < c) {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) : IsOrderedArrangement (fun j => c * v j) := by
  refine ⟨fun i => mul_pos hc (hv.1 i), ?_⟩
  intro i j hij
  exact mul_lt_mul_of_pos_left (hv.2 hij) hc

theorem typesProvedUp_isolation {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) {k : Fin 8} (h : TypesProvedUp v k) : Isolation v k := by
  obtain ⟨c, hc, hT⟩ := h
  exact (Isolation_smul hc).1 (typesProved_isolation (orderedArrangement_smul hc hv) hT)

theorem typesProvedUp_or_admissible {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) (k : Fin 8) :
    TypesProvedUp v k ∨ AdmissibleUp v k := by
  by_cases h : TypesProvedUp v k
  · exact Or.inl h
  · exact Or.inr ⟨hv, h⟩

theorem TypesProvedUp_smul {c : ℝ} (hc : 0 < c) {v : Fin 8 → ℝ} {k : Fin 8} :
    TypesProvedUp (fun j => c * v j) k ↔ TypesProvedUp v k := by
  constructor
  · rintro ⟨c', hc', h⟩
    refine ⟨c' * c, by positivity, ?_⟩
    have e : (fun j => c' * (c * v j)) = (fun j => c' * c * v j) := by funext j; ring
    rwa [e] at h
  · rintro ⟨c', hc', h⟩
    refine ⟨c' / c, by positivity, ?_⟩
    have e : (fun j => c' / c * (c * v j)) = (fun j => c' * v j) := by funext j; field_simp
    rwa [e]

#print axioms typesProvedUp_isolation
#print axioms TypesProvedUp_smul

end Fresh.ProvedTypesScale
