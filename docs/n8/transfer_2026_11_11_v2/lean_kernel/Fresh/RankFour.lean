import Fresh.FiniteKernels

namespace Fresh.FiniteRelations

open scoped BigOperators

/-- The space spanned by the small-frequency rows of the chosen finite expansion. -/
noncomputable def shortSpan {n : ℕ} (modes : Finset (Fin n → ℤ))
    (v : Fin n → ℝ) (D : ℝ) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ {x | ∃ m ∈ modes, |∑ i, (m i : ℝ)*v i| ≤ D ∧
    x = fun i => (m i : ℝ)}

theorem mem_shortSpan {n : ℕ} {modes : Finset (Fin n → ℤ)} {v : Fin n → ℝ} {D : ℝ}
    {m : Fin n → ℤ} (hm : m ∈ modes) (hf : |∑ i, (m i : ℝ)*v i| ≤ D) :
    (fun i => (m i : ℝ)) ∈ shortSpan modes v D :=
  Submodule.subset_span ⟨m,hm,hf,rfl⟩

/-- Select four rows from the actual finite list, rather than arbitrary
linear combinations of its rows. If there are fewer, use a bounded
kernel correction on a basis of the entire short-frequency span. -/
theorem four_short_rows_or_positive_annihilator (n bound : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (modes : Finset (Fin n → ℤ)) (v : Fin n → ℝ) (D : ℝ), 0 ≤ D →
        (∀ m ∈ modes, ∀ i, |m i| ≤ (bound : ℤ)) → (∀ i, C*D < v i) →
        (∃ rows : Fin 4 → Fin n → ℤ, (∀ j, rows j ∈ modes) ∧
          (∀ j, |∑ i, (rows j i : ℝ)*v i| ≤ D) ∧
          LinearIndependent ℝ (fun j i => (rows j i : ℝ))) ∨
        (Module.finrank ℝ (shortSpan modes v D) ≤ 3 ∧
          ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧
            ∀ z ∈ shortSpan modes v D, ∑ i, z i*w i = 0) := by
  classical
  obtain ⟨C,hC,hcorr⟩ := bounded_rows_kernel_types n 3 bound
  refine ⟨C,hC,fun modes v D hD hb hv => ?_⟩
  let S := {m : Fin n → ℤ // m ∈ modes ∧ |∑ i, (m i : ℝ)*v i| ≤ D}
  let f : S → (Fin n → ℝ) := fun m i => (m.val i : ℝ)
  obtain ⟨I,a,ha,hspan,hli⟩ := exists_linearIndependent' ℝ f
  haveI : Finite S := Finite.of_injective (fun m : S => (⟨m.val,m.property.1⟩ : modes))
    (fun a b h => Subtype.ext (congrArg (fun u : modes => u.val) h))
  haveI : Finite I := Finite.of_injective a ha
  letI := Fintype.ofFinite I
  let k := Fintype.card I
  let e : Fin k ≃ I := (Fintype.equivFin I).symm
  have hspan' : Submodule.span ℝ (Set.range (f ∘ a)) = shortSpan modes v D := by
    rw [hspan]
    congr 1
    ext x
    constructor
    · rintro ⟨m,rfl⟩
      exact ⟨m.val,m.property.1,m.property.2,rfl⟩
    · rintro ⟨m,hm,hD',rfl⟩
      exact ⟨⟨m,hm,hD'⟩,rfl⟩
  have hk : Module.finrank ℝ (shortSpan modes v D) = k := by
    rw [← hspan', finrank_span_eq_card hli]
  by_cases h4 : 4 ≤ k
  · let inc : Fin 4 ↪ Fin k := Fin.castLEEmb h4
    let idx : Fin 4 → I := fun j => e (inc j)
    refine Or.inl ⟨fun j => (a (idx j)).val, fun j => (a (idx j)).property.1,
      fun j => (a (idx j)).property.2, ?_⟩
    exact hli.comp idx (e.injective.comp inc.injective)
  · have hk3 : k ≤ 3 := by omega
    refine Or.inr ⟨by omega,?_⟩
    let rows (j : Fin 3) : Fin n → ℤ :=
      if h : j.val < k then (a (e ⟨j.val,h⟩)).val else 0
    have hrb (j : Fin 3) (i : Fin n) : |rows j i| ≤ (bound : ℤ) := by
      unfold rows
      split
      · exact hb _ (a _).property.1 i
      · simp
    have hrd (j : Fin 3) : |∑ i, (rows j i : ℝ)*v i| ≤ D := by
      unfold rows
      split
      · exact (a _).property.2
      · simpa using hD
    obtain ⟨A,hA,w,hw,hclose,_⟩ := hcorr v D hD rows hrb hrd
    rw [hA] at hw
    refine ⟨w,fun i => ?_,?_⟩
    · have hh := (norm_le_pi_norm (v-w) i).trans hclose
      change ‖v i-w i‖ ≤ C*D at hh
      rw [Real.norm_eq_abs] at hh
      linarith only [hv i,(abs_le.mp hh).2]
    · rw [← hspan']
      intro z hz
      let eval : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ i, w i • LinearMap.proj i
      have he (u : Fin n → ℝ) : eval u = ∑ i, u i*w i := by
        simp [eval, mul_comm]
      rw [← he]
      have hle : Submodule.span ℝ (Set.range (f ∘ a)) ≤ eval.ker := by
        apply Submodule.span_le.mpr
        rintro _ ⟨i,rfl⟩
        change (f ∘ a) i ∈ eval.ker
        rw [LinearMap.mem_ker, he]
        let j : Fin 3 := ⟨(e.symm i).val, (e.symm i).isLt.trans_le hk3⟩
        have hj : rows j = (a i).val := by
          unfold rows j
          simp
        have hzero := congrFun (LinearMap.mem_ker.mp hw) j
        rw [evaluate_apply,hj] at hzero
        exact hzero
      exact LinearMap.mem_ker.mp (hle hz)

#print axioms four_short_rows_or_positive_annihilator

end Fresh.FiniteRelations
