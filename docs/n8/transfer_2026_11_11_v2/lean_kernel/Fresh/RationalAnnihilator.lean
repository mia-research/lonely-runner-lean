import Fresh.FibreMargin
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace Fresh.FiniteRelations

open Set
open scoped BigOperators

def dotForm {ι K : Type*} [Fintype ι] [Field K] (z : ι → K) : (ι → K) →ₗ[K] K :=
  ∑ i, z i • LinearMap.proj i

@[simp] theorem dotForm_apply {ι K : Type*} [Fintype ι] [Field K] (z w : ι → K) :
    dotForm z w = ∑ i, z i * w i := by
  simp [dotForm]

def rationalKernel {n : ℕ} (T : Finset (Fin n → ℤ)) : Submodule ℚ (Fin n → ℚ) :=
  ⨅ m : T, LinearMap.ker (dotForm (fun i => (m.val i : ℚ)))

noncomputable def rowSpace {n : ℕ} (T : Finset (Fin n → ℤ)) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ (Set.range (fun m : T => fun i => (m.val i : ℝ)))

theorem mem_rationalKernel {n : ℕ} {T : Finset (Fin n → ℤ)} {w : Fin n → ℚ} :
    w ∈ rationalKernel T ↔ ∀ m : T, ∑ i, (m.val i : ℚ) * w i = 0 := by
  simp [rationalKernel]

private theorem functional_dot {ι : Type*} [Fintype ι] (f : ℝ →ₗ[ℚ] ℚ) (m : ι → ℤ) (w : ι → ℝ) :
    f (∑ i, (m i : ℝ) * w i) = ∑ i, (m i : ℚ) * f (w i) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [zsmul_eq_mul] using map_zsmul f (m i) (w i)

private theorem cast_rows_independent {ι : Type*} [Fintype ι] {n : ℕ}
    (a : ι → Fin n → ℤ)
    (ha : LinearIndependent ℚ (fun j i => (a j i : ℚ))) :
    LinearIndependent ℝ (fun j i => (a j i : ℝ)) := by
  rw [Fintype.linearIndependent_iff] at ha ⊢
  intro g hg j
  by_contra hj
  obtain ⟨f,hf⟩ := Module.Projective.exists_dual_eq_one ℚ hj
  have hq : ∑ k, f (g k) • (fun i => (a k i : ℚ)) = 0 := by
    ext i
    have h := congrFun hg i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h ⊢
    have hh := functional_dot f (fun k => a k i) g
    rw [show (∑ k, (a k i : ℝ) * g k) = 0 by simpa only [mul_comm] using h, map_zero] at hh
    simpa only [mul_comm] using hh.symm
  have := ha (fun k => f (g k)) hq j
  rw [hf] at this
  exact one_ne_zero this

theorem rationalKernel_codim_le {n : ℕ} (T : Finset (Fin n → ℤ)) :
    n ≤ Module.finrank ℚ (rationalKernel T) + Module.finrank ℝ (rowSpace T) := by
  classical
  let a : T → Fin n → ℚ := fun m i => (m.val i : ℚ)
  let M : Matrix T (Fin n) ℚ := a
  have hk : LinearMap.ker M.mulVecLin = rationalKernel T := by
    ext w
    simp [mem_rationalKernel, LinearMap.mem_ker, Matrix.mulVec, dotProduct,
      funext_iff, M, a]
  have hdim := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  change M.rank + Module.finrank ℚ (LinearMap.ker M.mulVecLin) = _ at hdim
  rw [hk, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Matrix.rank_eq_finrank_span_row] at hdim
  obtain ⟨I,b,hb,hs,hi⟩ := exists_linearIndependent' ℚ a
  haveI : Finite I := Finite.of_injective b hb
  letI := Fintype.ofFinite I
  have hr : Module.finrank ℚ (Submodule.span ℚ (range a)) = Fintype.card I := by
    rw [← hs, finrank_span_eq_card hi]
  have hreal := cast_rows_independent (fun j : I => (b j).val) hi
  have hh : Submodule.span ℝ (range (fun j : I => fun i => ((b j).val i : ℝ))) ≤ rowSpace T := by
    apply Submodule.span_mono
    rintro _ ⟨j,rfl⟩
    exact ⟨b j,rfl⟩
  have hle := Submodule.finrank_mono hh
  rw [finrank_span_eq_card hreal] at hle
  change Module.finrank ℚ (Submodule.span ℚ (range a)) + _ = _ at hdim
  omega

theorem rationalKernel_moves {n : ℕ} (T : Finset (Fin n → ℤ))
    (h : ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧
      ∀ z ∈ rowSpace T, ∑ i, z i * w i = 0) :
    ∀ i, ∃ u : rationalKernel T, (u : Fin n → ℚ) i ≠ 0 := by
  obtain ⟨w,hw,hann⟩ := h
  intro i
  obtain ⟨f,hf⟩ := Module.Projective.exists_dual_eq_one ℚ (hw i).ne'
  have hz : (fun j => f (w j)) ∈ rationalKernel T := by
    rw [mem_rationalKernel]
    intro m
    rw [← functional_dot, hann _ (Submodule.subset_span ⟨m,rfl⟩), map_zero]
  exact ⟨⟨_,hz⟩,by simpa only [hf] using (one_ne_zero : (1:ℚ) ≠ 0)⟩

theorem mem_rowSpace_iff {n : ℕ} (T : Finset (Fin n → ℤ)) (m : Fin n → ℤ) :
    (fun i => (m i : ℝ)) ∈ rowSpace T ↔
      ∀ w ∈ rationalKernel T, ∑ i, (m i : ℚ) * w i = 0 := by
  constructor
  · intro hm w hw
    have he : dotForm (fun i => (m i : ℝ)) (fun i => (w i : ℝ)) = 0 := by
      apply Submodule.span_induction (p := fun z _ => dotForm z (fun i => (w i : ℝ)) = 0) _ _ _ _ hm
      · rintro _ ⟨a,rfl⟩
        simp only [dotForm_apply]
        exact_mod_cast (mem_rationalKernel.mp hw a)
      · simp
      · intro a b _ _ ha hb
        simp only [dotForm_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib] at *
        rw [ha,hb,add_zero]
      · intro c a _ ha
        simp only [dotForm_apply, Pi.smul_apply, smul_eq_mul] at *
        simp_rw [mul_assoc, ← Finset.mul_sum, ha, mul_zero]
    simp only [dotForm_apply] at he
    exact_mod_cast he
  · intro hm
    let D (a : T) : (Fin n → ℝ) →ₗ[ℝ] ℝ := dotForm (fun i => (a.val i : ℝ))
    have h : ⨅ a, LinearMap.ker (D a) ≤ LinearMap.ker (dotForm (fun i => (m i : ℝ))) := by
      intro w hw
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, D, dotForm_apply] at hw ⊢
      by_contra hn
      obtain ⟨f,hf⟩ := Module.Projective.exists_dual_eq_one ℚ hn
      have hq : (fun i => f (w i)) ∈ rationalKernel T := by
        rw [mem_rationalKernel]
        intro a
        rw [← functional_dot, hw a, map_zero]
      exact one_ne_zero (hf.symm.trans ((functional_dot f m w).trans (hm _ hq)))
    obtain ⟨c,hc⟩ := Submodule.mem_span_range_iff_exists_fun ℝ |>.mp (mem_span_of_iInf_ker_le_ker h)
    apply Submodule.mem_span_range_iff_exists_fun ℝ |>.mpr
    refine ⟨c,?_⟩
    ext i
    have hi := DFunLike.congr_fun hc (Pi.single i 1)
    classical
    simpa [D, Finset.sum_apply, Finset.mul_sum, Pi.single_apply, mul_ite, eq_comm] using hi

#print axioms rationalKernel_codim_le
#print axioms mem_rowSpace_iff

end Fresh.FiniteRelations
