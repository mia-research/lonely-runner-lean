import Fresh.Cascade

namespace Fresh.FiniteRelations

open Set Metric MeasureTheory MeasureTheory.Measure
open scoped ENNReal

theorem circle_mul_preserving (p : ℤ) (hp : p ≠ 0) :
    MeasurePreserving (fun x : UnitAddCircle => p • x) volume volume := by
  let f : UnitAddCircle →+ UnitAddCircle :=
    { toFun := fun x => p • x
      map_zero' := smul_zero _
      map_add' := smul_add _ }
  have hcont : Continuous f := continuous_id.const_smul p
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientAddGroup.mk_surjective y
    refine ⟨((x/(p:ℝ) : ℝ) : UnitAddCircle),?_⟩
    change p • ((x/(p:ℝ) : ℝ) : UnitAddCircle) = (x : UnitAddCircle)
    rw [← AddCircle.coe_zsmul,zsmul_eq_mul,mul_div_cancel₀ _ (by exact_mod_cast hp)]
  haveI : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨by simp [AddCircle.measure_univ]⟩
  haveI := Measure.isAddHaarMeasure_map_of_isFiniteMeasure
    (volume : Measure UnitAddCircle) f hcont hsurj
  haveI : IsProbabilityMeasure (Measure.map f (volume : Measure UnitAddCircle)) :=
    ⟨by rw [Measure.map_apply hcont.measurable MeasurableSet.univ, preimage_univ, measure_univ]⟩
  exact ⟨hcont.measurable, isAddHaarMeasure_eq_of_isProbabilityMeasure _ _⟩

/-- Three or fewer nonzero integer slopes clear any shifted phase at
threshold one seventh. This is the small-circuit leaf of the rank proof. -/
theorem small_circle_phase {ι : Type*} [Fintype ι] (hcard : Fintype.card ι ≤ 3)
    (p : ι → ℤ) (hp : ∀ i, p i ≠ 0) (x : ι → ℝ) :
    ∃ t : ℝ, ∀ i, (1/7:ℝ) < distInt ((p i : ℝ)*t+x i) := by
  classical
  let B (i : ι) := (fun z : UnitAddCircle => p i • z) ⁻¹'
    closedBall (-((x i : ℝ) : UnitAddCircle)) (1/7)
  have hb (i : ι) : volume (B i) = ENNReal.ofReal (2/7) := by
    rw [show volume (B i) = volume (closedBall (-((x i : ℝ) : UnitAddCircle)) (1/7)) from
      (circle_mul_preserving (p i) (hp i)).measure_preimage measurableSet_closedBall.nullMeasurableSet,
      AddCircle.volume_closedBall]
    congr 1
    norm_num
  have hlt : volume (⋃ i, B i) < 1 := by
    apply (measure_iUnion_le B).trans_lt
    rw [tsum_fintype]
    simp only [hb,Finset.sum_const,Finset.card_univ, ← ENNReal.ofReal_nsmul]
    have hR : ((Fintype.card ι : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hcard
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ) < 1) |>.2
    simp only [nsmul_eq_mul]
    linarith
  have hne : (⋃ i, B i) ≠ univ := by
    intro h
    rw [h, AddCircle.measure_univ] at hlt
    norm_num at hlt
  obtain ⟨z,hz⟩ : ∃ z, z ∉ ⋃ i, B i := by
    by_contra! h
    exact hne (eq_univ_of_forall h)
  obtain ⟨t,rfl⟩ := QuotientAddGroup.mk_surjective z
  refine ⟨t,fun i => ?_⟩
  have hi : (t : UnitAddCircle) ∉ B i :=
    fun h => hz (mem_iUnion.mpr ⟨i,h⟩)
  change ¬ dist (p i • (t : UnitAddCircle)) (-((x i : ℝ) : UnitAddCircle)) ≤ 1/7 at hi
  rw [dist_eq_norm, sub_neg_eq_add, ← AddCircle.coe_zsmul, ← AddCircle.coe_add,
    UnitAddCircle.norm_eq, zsmul_eq_mul] at hi
  exact lt_of_not_ge hi

#print axioms small_circle_phase

end Fresh.FiniteRelations
