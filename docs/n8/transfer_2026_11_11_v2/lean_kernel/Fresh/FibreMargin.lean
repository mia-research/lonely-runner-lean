import Fresh.FourCircleComplete

namespace Fresh.FiniteRelations

open Set

/-- Strict pointwise clearance gives a uniform margin for a fixed fibre
direction space. The margin may shrink as the space varies. -/
theorem uniform_fibre_margin {ι : Type*} [Fintype ι]
    (V : Submodule ℚ (ι → ℚ))
    (hdim : Fintype.card ι ≤ Module.finrank ℚ V+3)
    (hmoves : ∀ i, ∃ u : V, (u : ι → ℚ) i ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ι → ℝ,
      ∃ q : ℕ, (q = 1 ∨ q = 2) ∧ ∃ w : V,
        ∀ i, 1/8 + δ < distInt ((q:ℝ)*x i+((w : ι → ℚ) i : ℝ)) := by
  classical
  have hcont : Continuous distInt := by
    have h := (AddCircle.continuous_mk' (1:ℝ)).norm
    convert h using 1
    funext x
    exact UnitAddCircle.norm_eq.symm
  let I := {p : ℝ × ℕ × V // 0 < p.1 ∧ (p.2.1 = 1 ∨ p.2.1 = 2)}
  let U : I → Set (ι → ℝ) := fun p =>
    ⋂ i, {x | 1/8+p.val.1 < distInt ((p.val.2.1:ℝ)*x i+((p.val.2.2 : ι → ℚ) i:ℝ))}
  have hU (p : I) : IsOpen (U p) := by
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_lt continuous_const
    apply hcont.comp
    fun_prop
  have small (s : Finset ℝ) (hs : ∀ e ∈ s, 0 < e) :
      ∃ δ : ℝ, 0 < δ ∧ ∀ e ∈ s, δ ≤ e := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert a s has ih =>
      obtain ⟨δ,hδ,hle⟩ := ih (fun e he => hs e (Finset.mem_insert_of_mem he))
      refine ⟨min a δ,lt_min (hs a (Finset.mem_insert_self a s)) hδ,fun e he => ?_⟩
      rcases Finset.mem_insert.mp he with rfl | he
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hle e he)
  have hcover : (univ : Set (ι → ℝ)) ⊆ ⋃ p : I, U p := by
    intro x _
    obtain ⟨q,hq,w,hw⟩ := rank_three_fibre_clear V hdim hmoves x
    let f : ι → ℝ := fun i => distInt ((q:ℝ)*x i+((w:ι → ℚ) i:ℝ)) - 1/8
    obtain ⟨e,he,hle⟩ := small (Finset.univ.image f) (by
      intro d hd
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hd
      exact sub_pos.mpr (hw i))
    refine mem_iUnion.mpr ⟨⟨(e/2,q,w),by constructor <;> first | positivity | exact hq⟩,?_⟩
    refine mem_iInter.mpr (fun i => ?_)
    have hh := hle (f i) (Finset.mem_image_of_mem f (Finset.mem_univ i))
    dsimp [f] at hh
    change 1/8+e/2 < distInt ((q:ℝ)*x i+((w:ι → ℚ) i:ℝ))
    linarith
  let K : Set (ι → ℝ) := Icc 0 1
  obtain ⟨s,hs⟩ := (isCompact_Icc (a := (0 : ι → ℝ)) (b := 1)).elim_finite_subcover
    U hU ((subset_univ K).trans hcover)
  obtain ⟨δ,hδ,hle⟩ := small (s.image fun p => p.val.1) (by
    intro e he
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp he
    exact p.property.1)
  refine ⟨δ,hδ,fun x => ?_⟩
  let y : ι → ℝ := fun i => Int.fract (x i)
  have hy : y ∈ K := ⟨fun i => Int.fract_nonneg _,fun i => (Int.fract_lt_one _).le⟩
  obtain ⟨p,hps,hp⟩ := mem_iUnion₂.mp (hs hy)
  obtain ⟨⟨e,q,w⟩,he,hq⟩ := p
  refine ⟨q,hq,w,fun i => ?_⟩
  have hd : δ ≤ e := hle _ (Finset.mem_image_of_mem _ hps)
  have hh : 1/8+e < distInt ((q:ℝ)*y i+((w:ι → ℚ) i:ℝ)) := mem_iInter.mp hp i
  have hx : (q:ℝ)*x i+((w:ι → ℚ) i:ℝ) =
      (q:ℝ)*y i+((w:ι → ℚ) i:ℝ)+(((q:ℤ)*⌊x i⌋:ℤ):ℝ) := by
    change _ = (q:ℝ)*(x i-(⌊x i⌋:ℝ))+((w:ι → ℚ) i:ℝ)+_
    push_cast
    ring
  rw [hx,Fresh.Cascade.distInt_add_int]
  exact (add_le_add_right hd _).trans_lt hh

#print axioms uniform_fibre_margin

end Fresh.FiniteRelations
