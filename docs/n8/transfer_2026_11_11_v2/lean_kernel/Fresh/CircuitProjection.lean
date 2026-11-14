import Fresh.PhaseFibres

namespace Fresh.FiniteRelations

open scoped BigOperators

/-- The support used for a coordinate circuit. -/
def coordSupport {ι K : Type*} [Fintype ι] [Zero K] [DecidableEq K] (v : ι → K) : Finset ι :=
  Finset.univ.filter fun i => v i ≠ 0

theorem mem_coordSupport {ι K : Type*} [Fintype ι] [Zero K] [DecidableEq K]
    (v : ι → K) (i : ι) : i ∈ coordSupport v ↔ v i ≠ 0 := by simp [coordSupport]

def restrictOutside {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (V : Submodule K (ι → K)) (s : Finset ι) : V →ₗ[K] (↥(sᶜ) → K) where
  toFun v i := (v : ι → K) i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A minimal support direction has a one-dimensional kernel under
restriction to its complement. The projected codimension therefore drops
by the support size minus one. -/
theorem circuit_projection {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    [DecidableEq K] (V : Submodule K (ι → K)) (u : V)
    (hu : (u : ι → K) ≠ 0)
    (hmin : ∀ v : V, (v : ι → K) ≠ 0 →
      (coordSupport (u : ι → K)).card ≤ (coordSupport (v : ι → K)).card) :
    let s := coordSupport (u : ι → K)
    let P := restrictOutside V s
    P.ker = K ∙ u ∧
      Module.finrank K P.range + 1 = Module.finrank K V ∧
      s.card + Module.finrank K V ≤ Fintype.card ι + 1 := by
  classical
  dsimp only
  let s := coordSupport (u : ι → K)
  let P := restrictOutside V s
  have hker : P.ker = K ∙ u := by
    apply le_antisymm
    · intro v hv
      obtain ⟨i,hi⟩ := Function.ne_iff.mp hu
      change (u : ι → K) i ≠ 0 at hi
      let c := (v : ι → K) i / (u : ι → K) i
      let w : V := v-c • u
      have hwi : (w : ι → K) i = 0 := by
        change (v : ι → K) i - c * (u : ι → K) i = 0
        dsimp [c]
        field_simp
        ring
      have hsub : coordSupport (w : ι → K) ⊆ s.erase i := by
        intro j hj
        apply Finset.mem_erase.mpr
        have hwj := (mem_coordSupport _ _).1 hj
        refine ⟨fun h => hwj (h ▸ hwi),?_⟩
        by_contra hn
        have huz : (u : ι → K) j = 0 := by
          by_contra hz
          exact hn ((mem_coordSupport _ _).2 hz)
        have hvz : (v : ι → K) j = 0 := by
          exact congrFun (LinearMap.mem_ker.mp hv) ⟨j,Finset.mem_compl.mpr hn⟩
        exact hwj (by change (v : ι → K) j - c * (u : ι → K) j = 0; rw [huz,hvz]; ring)
      have hz : (w : ι → K) = 0 := by
        by_contra hn
        have hs : i ∈ s := (mem_coordSupport _ _).2 hi
        have h := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hs] at h
        have hm : s.card ≤ (coordSupport (w : ι → K)).card := hmin w hn
        have hp : 0 < s.card := Finset.card_pos.mpr ⟨i,hs⟩
        omega
      have hw : w = 0 := Subtype.ext hz
      exact Submodule.mem_span_singleton.mpr ⟨c,(sub_eq_zero.mp hw).symm⟩
    · apply Submodule.span_le.mpr
      rw [Set.singleton_subset_iff]
      apply LinearMap.mem_ker.mpr
      funext i
      change (u : ι → K) i = 0
      by_contra hu'
      exact (Finset.mem_compl.mp i.property) ((mem_coordSupport _ _).2 hu')
  have hdim := LinearMap.finrank_range_add_finrank_ker P
  rw [hker,finrank_span_singleton (show u ≠ 0 by intro h; apply hu; exact congrArg Subtype.val h)] at hdim
  have hbound : Module.finrank K P.range ≤ Fintype.card ι - s.card := by
    have h := Submodule.finrank_le P.range
    rwa [Module.finrank_fintype_fun_eq_card,Fintype.card_coe,Finset.card_compl] at h
  have hs := Finset.card_le_univ s
  refine ⟨hker,hdim,?_⟩
  change s.card + Module.finrank K V ≤ Fintype.card ι + 1
  omega

/-- A nontrivial phase space always has a direction of smallest support. -/
theorem exists_circuit {ι K : Type*} [Fintype ι] [Field K] [DecidableEq K]
    (V : Submodule K (ι → K)) (h : V ≠ ⊥) :
    ∃ u : V, (u : ι → K) ≠ 0 ∧ ∀ v : V, (v : ι → K) ≠ 0 →
      (coordSupport (u : ι → K)).card ≤ (coordSupport (v : ι → K)).card := by
  classical
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  let P (k : ℕ) := ∃ w : V, (w : ι → K) ≠ 0 ∧ (coordSupport (w : ι → K)).card = k
  have hP : ∃ k, P k := ⟨_,⟨v,hv⟩,hv0,rfl⟩
  obtain ⟨u,hu,hcard⟩ := Nat.find_spec hP
  refine ⟨u,hu,fun w hw => ?_⟩
  rw [hcard]
  exact Nat.find_min' hP ⟨w,hw,rfl⟩

#print axioms circuit_projection
#print axioms exists_circuit

end Fresh.FiniteRelations
