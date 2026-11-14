import Fresh.RankFourTransfer
import Mathlib.Analysis.Fourier.AddCircle

namespace Fresh.FiniteRelations

open Set ContinuousMap
open scoped BigOperators

noncomputable section

abbrev PhaseTorus (ι : Type*) := ι → UnitAddCircle

def torusCast {ι : Type*} (x : ι → ℝ) : PhaseTorus ι := fun i => x i

@[simp] theorem torusCast_add {ι : Type*} (x y : ι → ℝ) :
    torusCast (x+y) = torusCast x+torusCast y := by
  funext i
  exact (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1:ℝ))).map_add (x i) (y i)

@[simp] theorem torusCast_two {ι : Type*} (x : ι → ℝ) :
    torusCast (fun i => 2*x i) = 2 • torusCast x := by
  simpa only [two_mul, two_nsmul, Pi.add_apply] using torusCast_add x x

def torusEval {ι : Type*} [Fintype ι] (m : ι → ℤ) (x : PhaseTorus ι) : UnitAddCircle :=
  ∑ i, m i • x i

def torusMode {ι : Type*} [Fintype ι] (m : ι → ℤ) : C(PhaseTorus ι,ℂ) :=
  ⟨fun x => fourier 1 (torusEval m x), (fourier 1).continuous.comp
    (continuous_finset_sum _ (fun i _ => (continuous_apply i).const_smul (m i)))⟩

@[simp] theorem torusMode_zero {ι : Type*} [Fintype ι] (x : PhaseTorus ι) :
    torusMode 0 x = 1 := by simp [torusMode,torusEval]

theorem torusMode_add {ι : Type*} [Fintype ι] (m k : ι → ℤ) (x : PhaseTorus ι) :
    torusMode (m+k) x = torusMode m x * torusMode k x := by
  simp [torusMode,torusEval, add_zsmul, Finset.sum_add_distrib, AddCircle.toCircle_add]

theorem torusMode_neg {ι : Type*} [Fintype ι] (m : ι → ℤ) (x : PhaseTorus ι) :
    torusMode (-m) x = star (torusMode m x) := by
  simp only [torusMode, coe_mk, torusEval, Pi.neg_apply, neg_zsmul, Finset.sum_neg_distrib]
  rw [show -(∑ i, m i • x i) = (-1:ℤ) • (∑ i, m i • x i) by simp,
    show (fourier (T := 1) 1) ((-1:ℤ) • (∑ i, m i • x i)) =
      fourier (-1) (∑ i, m i • x i) by simp only [fourier_apply,one_zsmul], fourier_neg]
  rfl

theorem torusMode_at_add {ι : Type*} [Fintype ι] (m : ι → ℤ) (x y : PhaseTorus ι) :
    torusMode m (x+y) = torusMode m x * torusMode m y := by
  simp [torusMode,torusEval,Finset.sum_add_distrib,AddCircle.toCircle_add]

theorem torusMode_cast {n : ℕ} (m : Fin n → ℤ) (x : Fin n → ℝ) :
    torusMode m (torusCast x) = character (2*Real.pi*rowEval m x) := by
  have he : torusEval m (torusCast x) = ((rowEval m x : ℝ) : UnitAddCircle) := by
    unfold torusEval rowEval
    let Q := QuotientAddGroup.mk' (AddSubgroup.zmultiples (1:ℝ))
    change _ = Q (∑ i, (m i : ℝ) * x i)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← zsmul_eq_mul, map_zsmul]
    rfl
  change fourier 1 (torusEval m (torusCast x)) = _
  rw [he,fourier_coe_apply]
  unfold character
  push_cast
  congr 1
  ring

private def torusModeAlgebra (ι : Type*) [Fintype ι] :
    StarSubalgebra ℂ C(PhaseTorus ι,ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (range torusMode)
  star_mem' := by
    change Algebra.adjoin ℂ (range (torusMode (ι := ι))) ≤
      star (Algebra.adjoin ℂ (range (torusMode (ι := ι))))
    refine Algebra.adjoin_le ?_
    rintro - ⟨m,rfl⟩
    exact Algebra.subset_adjoin ⟨-m,ext fun x => torusMode_neg m x⟩

private theorem torusModeAlgebra_span {ι : Type*} [Fintype ι] :
    (torusModeAlgebra ι).toSubalgebra.toSubmodule = Submodule.span ℂ (range torusMode) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine Subset.trans ?_ Submodule.subset_span
  intro x hx
  refine Submonoid.closure_induction (fun _ => id) ⟨0,?_⟩ ?_ hx
  · ext z
    exact torusMode_zero z
  · rintro - - - - ⟨m,rfl⟩ ⟨k,rfl⟩
    exact ⟨m+k,ext fun z => torusMode_add m k z⟩

theorem torusMode_dense (ι : Type*) [Fintype ι] :
    (Submodule.span ℂ (range (torusMode (ι := ι)))).topologicalClosure = ⊤ := by
  classical
  have hsep : (torusModeAlgebra ι).SeparatesPoints := by
    intro x y hxy
    obtain ⟨i,hi⟩ : ∃ i, x i ≠ y i := by
      by_contra! h
      exact hxy (funext h)
    refine ⟨torusMode (Pi.single i 1), ⟨torusMode (Pi.single i 1),
      Algebra.subset_adjoin ⟨_,rfl⟩,rfl⟩, ?_⟩
    have he (z : PhaseTorus ι) : torusMode (Pi.single i 1) z = AddCircle.toCircle (z i) := by
      change fourier 1 (torusEval (Pi.single i 1) z) = _
      rw [fourier_one]
      congr 1
      simp [torusEval,Pi.single_apply,ite_smul]
    rw [he,he]
    exact fun h => hi (AddCircle.injective_toCircle (by norm_num) (Subtype.ext h))
  rw [← torusModeAlgebra_span]
  exact congrArg (fun A : StarSubalgebra ℂ C(PhaseTorus ι,ℂ) => A.toSubalgebra.toSubmodule)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep)

/-- Finite sums suffice: no infinite Fourier series or coefficient decay
is required for a qualitative bounded-relation theorem. -/
theorem torusMode_approx {ι : Type*} [Fintype ι] (g : C(PhaseTorus ι,ℂ)) {e : ℝ}
    (he : 0 < e) :
    ∃ (S : Finset (ι → ℤ)) (A : (ι → ℤ) → ℂ),
      ∀ x, ‖(∑ m ∈ S, A m * torusMode m x) - g x‖ < e := by
  have hg : g ∈ closure (↑(Submodule.span ℂ (range (torusMode (ι := ι)))) : Set _) := by
    change g ∈ (Submodule.span ℂ (range (torusMode (ι := ι)))).topologicalClosure
    rw [torusMode_dense]
    trivial
  obtain ⟨f,hf,hfg⟩ := Metric.mem_closure_iff.mp hg e he
  obtain ⟨a,ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hf
  refine ⟨a.support,a,fun x => ?_⟩
  have hx : (∑ m ∈ a.support, a m * torusMode m x) = f x := by
    rw [← ha]
    simp [Finsupp.sum, ContinuousMap.sum_apply]
  rw [hx]
  exact (ContinuousMap.norm_coe_le_norm (f-g) x).trans_lt
    (by simpa only [dist_eq_norm, norm_sub_rev] using hfg)

#print axioms torusMode_approx

end

end Fresh.FiniteRelations
