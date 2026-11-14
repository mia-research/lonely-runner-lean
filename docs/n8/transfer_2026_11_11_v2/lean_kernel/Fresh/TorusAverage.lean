import Fresh.TorusPolynomial
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace Fresh.FiniteRelations

open Set MeasureTheory MeasureTheory.Measure
open scoped BigOperators

noncomputable section

def parameterMap {ι κ : Type*} [Fintype κ] (U : κ → ι → ℤ) (z : PhaseTorus κ) :
    PhaseTorus ι := fun i => ∑ j, U j i • z j

@[simp] theorem parameterMap_add {ι κ : Type*} [Fintype κ] (U : κ → ι → ℤ)
    (z w : PhaseTorus κ) : parameterMap U (z+w) = parameterMap U z + parameterMap U w := by
  ext i
  simp [parameterMap,Finset.sum_add_distrib]

theorem continuous_parameterMap {ι κ : Type*} [Fintype κ] (U : κ → ι → ℤ) :
    Continuous (parameterMap U) :=
  continuous_pi fun _ => continuous_finset_sum _ fun j _ => (continuous_apply j).const_smul _

theorem parameterMap_cast {ι κ : Type*} [Fintype κ] (U : κ → ι → ℤ) (t : κ → ℝ) :
    parameterMap U (torusCast t) = torusCast (fun i => ∑ j, (U j i : ℝ) * t j) := by
  ext i
  let Q := QuotientAddGroup.mk' (AddSubgroup.zmultiples (1:ℝ))
  change _ = Q (∑ j, (U j i : ℝ) * t j)
  rw [_root_.map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← zsmul_eq_mul, map_zsmul]
  rfl

theorem torusEval_parameterMap {ι κ : Type*} [Fintype ι] [Fintype κ] (U : κ → ι → ℤ)
    (m : ι → ℤ) (z : PhaseTorus κ) :
    torusEval m (parameterMap U z) = ∑ j, (∑ i, m i * U j i) • z j := by
  unfold torusEval parameterMap
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_smul]

def parameterMeasure (κ : Type*) [Fintype κ] : Measure (PhaseTorus κ) := addHaarMeasure ⊤

instance {κ : Type*} [Fintype κ] : IsProbabilityMeasure (parameterMeasure κ) :=
  ⟨addHaarMeasure_self⟩

instance {κ : Type*} [Fintype κ] : IsAddHaarMeasure (parameterMeasure κ) :=
  inferInstanceAs (IsAddHaarMeasure (addHaarMeasure ⊤))

def phaseAverage {ι κ E : Type*} [Fintype κ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : κ → ι → ℤ) (g : PhaseTorus ι → E) (x : PhaseTorus ι) : E :=
  ∫ z, g (x + parameterMap U z) ∂parameterMeasure κ

theorem phaseAverage_continuous {ι κ E : Type*} [Fintype κ] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (U : κ → ι → ℤ) {g : PhaseTorus ι → E} (hg : Continuous g) :
    Continuous (phaseAverage U g) := by
  rw [← continuousOn_univ]
  apply continuousOn_integral_of_compact_support isCompact_univ
  · exact (hg.comp (continuous_fst.add ((continuous_parameterMap U).comp continuous_snd))).continuousOn
  · simp

theorem phaseAverage_nonneg {ι κ : Type*} [Fintype κ] (U : κ → ι → ℤ)
    {g : PhaseTorus ι → ℝ} (hg : ∀ y, 0 ≤ g y) (x : PhaseTorus ι) :
    0 ≤ phaseAverage U g x := integral_nonneg fun _ => hg _

theorem phaseAverage_pos {ι κ : Type*} [Fintype κ] (U : κ → ι → ℤ)
    {g : PhaseTorus ι → ℝ} (hg : Continuous g) (hgn : ∀ y, 0 ≤ g y)
    (x : PhaseTorus ι) (z : PhaseTorus κ) (hz : 0 < g (x + parameterMap U z)) :
    0 < phaseAverage U g x := by
  have h := hg.comp (continuous_const.add (continuous_parameterMap U) (f := fun _ => x))
  exact integral_pos_of_integrable_nonneg_nonzero h
    (h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (fun _ => hgn _) hz.ne'

private theorem mode_parameter_integral {ι κ : Type*} [Fintype ι] [Fintype κ]
    (U : κ → ι → ℤ) (m : ι → ℤ) :
    (∫ z, torusMode m (parameterMap U z) ∂parameterMeasure κ) =
      if (∀ j, ∑ i, m i * U j i = 0) then 1 else 0 := by
  classical
  by_cases h : ∀ j, ∑ i, m i * U j i = 0
  · rw [if_pos h]
    have he (z : PhaseTorus κ) : torusMode m (parameterMap U z) = 1 := by
      change fourier 1 (torusEval m (parameterMap U z)) = _
      rw [torusEval_parameterMap]
      simp [h]
    simp [he]
  · rw [if_neg h]
    push Not at h
    obtain ⟨j,hj⟩ := h
    let k : ℤ := ∑ i, m i * U j i
    let y : PhaseTorus κ := Pi.single j (((1 / 2 / (k:ℝ) : ℝ)) : UnitAddCircle)
    have hc : torusMode m (parameterMap U y) = -1 := by
      change fourier 1 (torusEval m (parameterMap U y)) = _
      rw [torusEval_parameterMap]
      have hy : (∑ j', (∑ i, m i * U j' i) • y j') =
          k • (((1 / 2 / (k:ℝ) : ℝ)) : UnitAddCircle) := by
        rw [Finset.sum_eq_single j]
        · simp [y,k]
        · intro b _ hb
          simp [y,Pi.single_eq_of_ne hb]
        · simp
      rw [hy]
      have hh := fourier_add_half_inv_index (T := 1) hj (by norm_num) (0 : UnitAddCircle)
      calc
        _ = fourier k (((1 / 2 / (k:ℝ) : ℝ)) : UnitAddCircle) := by
          simp only [fourier_apply, one_zsmul]
        _ = _ := by simpa only [zero_add, fourier_eval_zero] using hh
    let f : PhaseTorus κ → ℂ := fun z => torusMode m (parameterMap U z)
    have he (z : PhaseTorus κ) : f (y+z) = -f z := by
      simp [f,parameterMap_add,torusMode_at_add,hc]
    have hh := integral_add_left_eq_self (μ := parameterMeasure κ) f y
    simp_rw [he,integral_neg] at hh
    change (∫ z, f z ∂parameterMeasure κ) = 0
    exact neg_eq_self.mp hh

theorem phaseAverage_polynomial {ι κ : Type*} [Fintype ι] [Fintype κ]
    (U : κ → ι → ℤ) (S : Finset (ι → ℤ)) (A : (ι → ℤ) → ℂ) (x : PhaseTorus ι) :
    phaseAverage U (fun y => ∑ m ∈ S, A m * torusMode m y) x =
      ∑ m ∈ S, if (∀ j, ∑ i, m i * U j i = 0) then A m * torusMode m x else 0 := by
  classical
  unfold phaseAverage
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro m _
    simp_rw [torusMode_at_add, ← mul_assoc]
    calc
      _ = (A m * torusMode m x) *
          (∫ z, torusMode m (parameterMap U z) ∂parameterMeasure κ) :=
        integral_const_mul (A m * torusMode m x) (fun z => torusMode m (parameterMap U z))
      _ = _ := by rw [mode_parameter_integral]; split <;> simp
  · intro m _
    exact (continuous_const.mul ((torusMode m).continuous.comp
      (continuous_const.add (continuous_parameterMap U)))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

#print axioms phaseAverage_polynomial

end

end Fresh.FiniteRelations
