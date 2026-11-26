import Mathlib
import Fresh.Framework

/-!
# Sets of at most seven whole numbers containing a given six-element core

Written 2026-10-26.  New file.  `exists_insert_of_core`: a set `R` of at most seven naturals containing a six-element set `C` is `insert x C` for some `x` (take any element of `C` if `R = C`).
Used by the generated core covers (`CoreCover.lean`).  Grade [L].
-/

namespace Fresh.CoreCoverLib

theorem exists_insert_of_core {C R : Finset ℕ} (hC : C.card = 6) (hsub : C ⊆ R) (hR : R.card ≤ 7) : ∃ x : ℕ, R = insert x C := by
  by_cases hEq : R = C
  · have hne : C.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, by rw [hEq, Finset.insert_eq_of_mem hx]⟩
  · have hssub : C ⊂ R := lt_of_le_of_ne hsub (fun h => hEq h.symm)
    obtain ⟨x, hxR, hxC⟩ := Finset.exists_of_ssubset hssub
    refine ⟨x, (Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
    · intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact hxR
      · exact hsub hy
    · rw [Finset.card_insert_of_notMem hxC, hC]; omega

#print axioms exists_insert_of_core

end Fresh.CoreCoverLib
