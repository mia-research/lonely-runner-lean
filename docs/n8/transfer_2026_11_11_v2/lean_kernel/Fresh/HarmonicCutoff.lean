import Fresh.FiniteKernels

namespace Fresh.FiniteRelations

open Matrix
open scoped BigOperators

/-- Hadamard's determinant estimate, via the Euclidean volume form. -/
theorem det_abs_le_euclidean_rows {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    |B.det| ≤ ∏ i, ‖(WithLp.toLp 2 (B i) : EuclideanSpace ℝ (Fin n))‖ := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let f : Fin n → E := fun i => WithLp.toLp 2 (B i)
  letI : Fact (Module.finrank ℝ E = n) := ⟨by simp [E]⟩
  have h := e.toBasis.orientation.abs_volumeForm_apply_le f
  rw [e.toBasis.orientation.volumeForm_robust e rfl] at h
  have hm : e.toBasis.toMatrix f = Bᵀ := by
    ext i j
    rfl
  have hde : e.toBasis.det f = B.det :=
    (e.toBasis.det_apply f).trans ((congrArg Matrix.det hm).trans (Matrix.det_transpose B))
  calc
    |B.det| = |e.toBasis.det f| := congrArg abs hde.symm
    _ ≤ _ := h

/-- A primitive positive kernel generator is bounded by the product
of any four squared Euclidean row bounds. -/
theorem harmonic_square_bound_of_four_rows (A : Fin 4 → Fin 5 → ℤ) (p : Fin 5 → ℤ)
    (hp : ∀ i, 0 < p i)
    (hprim : ∃ u : Fin 5 → ℤ, ∑ i, u i*p i = 1)
    (hker : evaluate A (fun i => (p i : ℝ)) = 0)
    (hrank : Module.finrank ℝ (LinearMap.range (evaluate A)) = 4)
    (Bnd : Fin 4 → ℝ) (hrows : ∀ i, ∑ j, (A i j : ℝ)^2 ≤ Bnd i) :
    ∀ j, (p j : ℝ)^2 ≤ ∏ i, Bnd i := by
  classical
  let v : Fin 5 → ℝ := fun i => p i
  have hv (i : Fin 5) : 0 < v i := by dsimp [v]; exact_mod_cast hp i
  have hv0 : v ≠ 0 := by intro h; have he := congrFun h (0 : Fin 5); exact (hv 0).ne' he
  have hd := LinearMap.finrank_range_add_finrank_ker (evaluate A)
  rw [hrank, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hd
  have hline : LinearMap.ker (evaluate A) = ℝ ∙ v := by
    symm
    apply Submodule.eq_of_le_of_finrank_le
    · apply Submodule.span_le.mpr
      rw [Set.singleton_subset_iff]
      exact LinearMap.mem_ker.mpr hker
    · rw [finrank_span_singleton hv0]
      omega
  intro j
  let B : Matrix (Fin 4) (Fin 4) ℤ := fun i k => A i (j.succAbove k)
  let R : Matrix (Fin 4) (Fin 4) ℝ := fun i k => (B i k : ℝ)
  let col : Fin 4 → ℤ := fun i => A i j
  have hR : Function.Injective R.mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    let y : Fin 5 → ℝ := j.insertNth 0 x
    have hy : y ∈ LinearMap.ker (evaluate A) := by
      apply LinearMap.mem_ker.mpr
      funext i
      have hh := congrFun (LinearMap.mem_ker.mp hx) i
      change (R *ᵥ x) i = 0 at hh
      rw [evaluate_apply,Fin.sum_univ_succAbove _ j]
      simpa [y, R, B, Matrix.mulVec, dotProduct] using hh
    rw [hline] at hy
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hy
    have he := congrFun hc j
    change c*v j = y j at he
    simp only [y,Fin.insertNth_apply_same] at he
    have hc0 : c = 0 := (mul_eq_zero.mp he).resolve_right (hv j).ne'
    rw [hc0,zero_smul] at hc
    funext i
    have hh := congrFun hc (j.succAbove i)
    simpa [y] using hh.symm
  have hRd : R.det ≠ 0 := by
    have hh : IsUnit R := Matrix.mulVec_injective_iff_isUnit.mp hR
    exact ((Matrix.isUnit_iff_isUnit_det R).mp hh).ne_zero
  have hcast : (B.det : ℝ) = R.det := by exact (Int.castRingHom ℝ).map_det B
  let k : Fin 5 → ℤ := j.insertNth B.det (-(B.adjugate *ᵥ col))
  have hB : B *ᵥ (-(B.adjugate *ᵥ col)) = -(B.det • col) := by
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hk : (fun i => (k i : ℝ)) ∈ LinearMap.ker (evaluate A) := by
    apply LinearMap.mem_ker.mpr
    funext i
    rw [evaluate_apply, Fin.sum_univ_succAbove _ j]
    have hh := congrFun hB i
    have he : ∑ l, A i (j.succAbove l) * (-(B.adjugate *ᵥ col)) l = -(B.det * A i j) := hh
    simp only [k,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,Pi.zero_apply]
    exact_mod_cast (show A i j*B.det + ∑ l, A i (j.succAbove l) * (-(B.adjugate *ᵥ col)) l = 0 by
      rw [he]
      ring)
  rw [hline] at hk
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hk
  obtain ⟨u,hu⟩ := hprim
  let z : ℤ := ∑ i, u i*k i
  have hz : (z:ℝ) = a := by
    have h1 : ∑ i, (u i : ℝ)*(p i : ℝ) = 1 := by exact_mod_cast hu
    have he (i : Fin 5) : (k i : ℝ) = a*(p i : ℝ) := (congrFun ha i).symm
    unfold z
    push_cast
    simp_rw [he, show ∀ (x y : ℝ), x*(a*y) = a*(x*y) by intros; ring]
    rw [← Finset.mul_sum, h1, mul_one]
  have hdet : B.det = z*p j := by
    have he : a*(p j:ℝ) = (k j:ℝ) := congrFun ha j
    rw [← hz] at he
    simp only [k,Fin.insertNth_apply_same] at he
    exact_mod_cast he.symm
  have hz0 : z ≠ 0 := by
    intro hh
    apply hRd
    rw [← hcast,hdet,hh,zero_mul,Int.cast_zero]
  have hpj : (0:ℝ) ≤ p j := by exact_mod_cast (hp j).le
  have hab : (p j : ℝ) ≤ |R.det| := by
    rw [← hcast,hdet,Int.cast_mul,abs_mul,abs_of_nonneg hpj]
    have hza : (1:ℝ) ≤ |(z:ℝ)| := by exact_mod_cast (show (1:ℤ) ≤ |z| from by
      have := abs_pos.mpr hz0
      omega)
    exact le_mul_of_one_le_left hpj hza
  have hs (i : Fin 4) :
      ‖(WithLp.toLp 2 (R i) : EuclideanSpace ℝ (Fin 4))‖^2 ≤
      Bnd i := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs,sq_abs,R,B]
    have ht : (∑ l, (A i (j.succAbove l) : ℝ)^2) ≤ ∑ l, (A i l : ℝ)^2 := by
      rw [Fin.sum_univ_succAbove _ j]
      linarith only [sq_nonneg (A i j : ℝ)]
    exact ht.trans (hrows i)
  have he := det_abs_le_euclidean_rows R
  have hmul := pow_le_pow_left₀ (by exact_mod_cast (hp j).le) (hab.trans he) 2
  rw [← Finset.prod_pow] at hmul
  exact hmul.trans (Finset.prod_le_prod (by intro i _; positivity) (fun i _ => hs i))

/-- Four exact relations of the indicated lengths imply the numerical
cutoff. The existence of relations of these lengths is a separate step. -/
theorem harmonic_cutoff_of_four_rows (A : Fin 4 → Fin 5 → ℤ) (p : Fin 5 → ℤ)
    (hp : ∀ i, 0 < p i)
    (hprim : ∃ u : Fin 5 → ℤ, ∑ i, u i*p i = 1)
    (hker : evaluate A (fun i => (p i : ℝ)) = 0)
    (hrank : Module.finrank ℝ (LinearMap.range (evaluate A)) = 4)
    (hrows : ∀ i, ∑ j, (A i j)^2 ≤ (![28,177,3222,11269] : Fin 4 → ℤ) i) :
    ∀ j, p j ≤ 424200 := by
  intro j
  have hsq := harmonic_square_bound_of_four_rows A p hp hprim hker hrank
    ![28,177,3222,11269] (fun i => by
      have hh := hrows i
      fin_cases i <;> norm_num at hh ⊢ <;> exact_mod_cast hh) j
  norm_num [Fin.prod_univ_succ] at hsq
  by_contra! hn
  have hlarge : (424201:ℝ) ≤ p j := by exact_mod_cast (show (424201:ℤ) ≤ p j by omega)
  nlinarith only [hsq,pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 424201) hlarge 2]

#print axioms det_abs_le_euclidean_rows
#print axioms harmonic_square_bound_of_four_rows
#print axioms harmonic_cutoff_of_four_rows

end Fresh.FiniteRelations
