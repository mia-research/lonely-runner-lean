import Fresh.ExplicitFourierKernel
import Fresh.HarmonicCutoff

namespace Fresh.FiniteRelations

open Set Matrix
open scoped BigOperators

noncomputable section

private def cofactors {n : ℕ} (A : Matrix (Fin n) (Fin (n+1)) ℤ) :
    Fin (n+1) → ℤ := fun j => (-1)^(j : ℕ) * (A.submatrix id j.succAbove).det

private theorem cofactor_annihilates {n : ℕ} (A : Matrix (Fin n) (Fin (n+1)) ℤ) :
    ∀ i, ∑ j, A i j * cofactors A j = 0 := by
  intro i
  let M : Matrix (Fin (n+1)) (Fin (n+1)) ℤ := Fin.cons (A i) A
  have hzero : M.det = 0 :=
    Matrix.det_zero_of_row_eq (Fin.succ_ne_zero i).symm (by simp [M])
  rw [Matrix.det_succ_row_zero] at hzero
  convert hzero using 1
  apply Finset.sum_congr rfl
  intro j _
  have he : M.submatrix Fin.succ j.succAbove = A.submatrix id j.succAbove := by
    ext a b
    simp [Matrix.submatrix_apply,M]
  rw [he]
  simp only [cofactors,M,Fin.cons_zero]
  ring

private theorem cofactor_bound (A : Matrix (Fin 6) (Fin 7) ℤ)
    (M : ℝ) (hM : 0 ≤ M) (hA : ∀ i j, |(A i j : ℝ)| ≤ M) :
    ∀ j, |(cofactors A j : ℝ)| ≤ (6*M)^6 := by
  intro j
  let B : Matrix (Fin 6) (Fin 6) ℤ := A.submatrix id j.succAbove
  let R : Matrix (Fin 6) (Fin 6) ℝ := fun a b => B a b
  have hcast : (B.det : ℝ) = R.det := (Int.castRingHom ℝ).map_det B
  have hnorm (i : Fin 6) : ‖(WithLp.toLp 2 (R i) : EuclideanSpace ℝ (Fin 6))‖ ≤ 6*M := by
    rw [PiLp.norm_eq_of_L2]
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity,?_⟩
    simp only [Real.norm_eq_abs]
    calc
      ∑ j', |R i j'|^2 ≤ ∑ _j' : Fin 6, M^2 := by
        apply Finset.sum_le_sum
        intro k _
        exact pow_le_pow_left₀ (abs_nonneg _) (hA i (j.succAbove k)) _
      _ ≤ (6*M)^2 := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        norm_num
        nlinarith [sq_nonneg M]
  have he : |(cofactors A j : ℝ)| = |R.det| := by
    simp only [cofactors, Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,abs_mul,
      abs_pow,abs_neg,abs_one,one_pow,one_mul]
    exact congrArg abs hcast
  rw [he]
  exact (det_abs_le_euclidean_rows R).trans (by
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      (Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 6)))
        (f := fun i => ‖(WithLp.toLp 2 (R i) : EuclideanSpace ℝ (Fin 6))‖)
        (fun _ _ => norm_nonneg _) (fun i _ => hnorm i)))

/-- Six independent bounded relations give a bounded positive integer
representative, even before taking a gcd. -/
theorem bounded_representative_of_six_rows (A : Matrix (Fin 6) (Fin 7) ℤ)
    (p : Fin 7 → ℤ) (hp : ∀ i, 0 < p i)
    (hk : evaluate A (fun i => (p i : ℝ)) = 0)
    (hrank : Module.finrank ℝ (LinearMap.range (evaluate A)) = 6)
    (M : ℤ) (hM : 0 ≤ M) (hA : ∀ i j, |A i j| ≤ M) :
    ∃ q : Fin 7 → ℤ, (∀ j, 0 < q j ∧ q j ≤ (6*M)^6) ∧
      ∃ c : ℚ, ∀ i, c * (q i : ℚ) = (p i : ℚ) := by
  classical
  let v : Fin 7 → ℝ := fun i => p i
  have hv (i : Fin 7) : 0 < v i := by change (0:ℝ) < (p i : ℝ); exact_mod_cast hp i
  have hv0 : v ≠ 0 := fun h => (hv 0).ne' (congrFun h 0)
  have hdim := LinearMap.finrank_range_add_finrank_ker (evaluate A)
  rw [hrank,Module.finrank_fin_fun] at hdim
  have hline : LinearMap.ker (evaluate A) = ℝ ∙ v := by
    symm
    apply Submodule.eq_of_le_of_finrank_le
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (LinearMap.mem_ker.mpr hk))
    · rw [finrank_span_singleton hv0]
      omega
  let B : Matrix (Fin 6) (Fin 6) ℤ := A.submatrix id (0 : Fin 7).succAbove
  let R : Matrix (Fin 6) (Fin 6) ℝ := fun i j => B i j
  have hR : Function.Injective R.mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    let y : Fin 7 → ℝ := (0 : Fin 7).insertNth 0 x
    have hy : y ∈ LinearMap.ker (evaluate A) := by
      apply LinearMap.mem_ker.mpr
      funext i
      have hh := congrFun (LinearMap.mem_ker.mp hx) i
      change (R *ᵥ x) i = 0 at hh
      rw [evaluate_apply,Fin.sum_univ_succAbove _ (0 : Fin 7)]
      simpa [y,R,B,Matrix.mulVec,dotProduct] using hh
    rw [hline] at hy
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hy
    have he := congrFun hc 0
    change c*v 0 = y 0 at he
    simp only [y,Fin.insertNth_apply_same] at he
    have hc0 : c = 0 := (mul_eq_zero.mp he).resolve_right (hv 0).ne'
    rw [hc0,zero_smul] at hc
    funext i
    have hh := congrFun hc ((0 : Fin 7).succAbove i)
    simpa [y] using hh.symm
  have hRd : R.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det R).mp (Matrix.mulVec_injective_iff_isUnit.mp hR)).ne_zero
  have hB : (B.det : ℝ) = R.det := (Int.castRingHom ℝ).map_det B
  let w : Fin 7 → ℝ := fun i => cofactors A i
  have hw0 : w 0 ≠ 0 := by simpa [w,cofactors,← hB,B] using hRd
  have hw : w ∈ LinearMap.ker (evaluate A) := by
    apply LinearMap.mem_ker.mpr
    funext i
    rw [evaluate_apply]
    change (∑ j, (A i j : ℝ) * (cofactors A j : ℝ)) = 0
    exact_mod_cast cofactor_annihilates A i
  rw [hline] at hw
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hw
  have hc' (i : Fin 7) : w i = c * v i := (congrFun hc i).symm
  have hc0 : c ≠ 0 := fun h => hw0 (by rw [hc',h,zero_mul])
  let q (i : Fin 7) := |cofactors A i|
  have hq (i : Fin 7) : (q i : ℝ) = |c| * (p i : ℝ) := by
    change ((|cofactors A i| : ℤ) : ℝ) = |c| * v i
    rw [Int.cast_abs,show (cofactors A i : ℝ) = w i from rfl,hc',abs_mul,abs_of_pos (hv i)]
  refine ⟨q,fun j => ?_,⟨(p 0 : ℚ)/(q 0 : ℚ),fun i => ?_⟩⟩
  · constructor
    · have hpos : (0:ℝ) < q j := by
        rw [hq j]
        exact mul_pos (abs_pos.mpr hc0) (hv j)
      exact_mod_cast hpos
    · have hM' : (0:ℝ) ≤ M := by exact_mod_cast hM
      have hA' (i j) : |(A i j : ℝ)| ≤ (M : ℝ) := by exact_mod_cast hA i j
      have hbound := cofactor_bound A M hM' hA' j
      rw [← Int.cast_abs] at hbound
      exact_mod_cast hbound
  · have h0 : (q 0 : ℚ) ≠ 0 := by
      have he : (0:ℝ) < q 0 := by
        rw [hq 0]
        exact mul_pos (abs_pos.mpr hc0) (hv 0)
      exact_mod_cast he.ne'
    apply mul_right_cancel₀ h0
    have he : (q i : ℚ) * (p 0 : ℚ) = (q 0 : ℚ) * (p i : ℚ) := by
      exact_mod_cast (show (q i : ℝ) * (p 0 : ℝ) = (q 0 : ℝ) * (p i : ℝ) by
        rw [hq i,hq 0]
        ring)
    calc
      (p 0 : ℚ) / (q 0 : ℚ) * (q i : ℚ) * (q 0 : ℚ) =
          (q i : ℚ) * (p 0 : ℚ) := by field_simp
      _ = (p i : ℚ) * (q 0 : ℚ) := he.trans (mul_comm _ _)

private theorem six_rows_of_line {T : Finset (Fin 7 → ℤ)}
    (hT : Module.finrank ℚ (rationalKernel T) ≤ 1) :
    ∃ A : Matrix (Fin 6) (Fin 7) ℤ, (∀ i, A i ∈ T) ∧
      Module.finrank ℝ (LinearMap.range (evaluate A)) = 6 := by
  classical
  let a : T → Fin 7 → ℝ := fun m i => (m.val i : ℝ)
  obtain ⟨I,b,hb,hs,hi⟩ := exists_linearIndependent' ℝ a
  haveI : Finite I := Finite.of_injective b hb
  letI := Fintype.ofFinite I
  have hdim : Module.finrank ℝ (rowSpace T) = Fintype.card I := by
    change Module.finrank ℝ (Submodule.span ℝ (range a)) = _
    rw [← hs,finrank_span_eq_card hi]
  have h6 : 6 ≤ Fintype.card I := by
    have := rationalKernel_codim_le T
    omega
  obtain ⟨e⟩ := Fin.nonempty_embedding_iff.mpr h6
  let f : Fin 6 ↪ I := e.trans (Fintype.equivFin I).symm.toEmbedding
  let A : Matrix (Fin 6) (Fin 7) ℤ := fun i => (b (f i)).val
  refine ⟨A,fun i => (b (f i)).property,?_⟩
  change (Matrix.rank (fun i j => (A i j : ℝ) : Matrix (Fin 6) (Fin 7) ℝ)) = 6
  rw [Matrix.rank_eq_finrank_span_row]
  change Module.finrank ℝ (Submodule.span ℝ (range ((a ∘ b) ∘ f))) = 6
  rw [finrank_span_eq_card (hi.comp f f.injective),Fintype.card_fin]

/-- An explicit bound for a positive integer representative of every
line whose positive integer trajectory has no strict witness. -/
theorem explicit_bounded_representative
    (hmerge : ∀ (d : ℕ) (U : Fin d → Fin 7 → ℤ),
      (∀ i, (fun j => U j i) ≠ 0) →
      (∃ i k, ¬ ∀ j q, U j i * U q k = U q i * U j k) →
      MergedPhase U)
    (p : Fin 7 → ℤ) (hp : ∀ i, 0 < p i)
    (hn : ¬ StrictlyClears (fun i => (p i : ℝ)) (1/8)) :
    ∃ q : Fin 7 → ℤ, (∀ j, 0 < q j ∧ q j ≤ (6*100352)^6) ∧
      ∃ c : ℚ, ∀ i, c * (q i : ℚ) = (p i : ℚ) := by
  classical
  obtain ⟨A,hA,hrank⟩ := six_rows_of_line (explicit_matching_kernel_finrank hmerge p hp hn)
  have hk : evaluate A (fun i => (p i : ℝ)) = 0 := by
    funext i
    rw [evaluate_apply,Pi.zero_apply]
    have h := (Finset.mem_filter.mp (hA i)).2
    exact_mod_cast h
  apply bounded_representative_of_six_rows A p hp hk hrank 100352 (by norm_num)
  intro i j
  exact (mem_characterCube _ _).mp (Finset.mem_filter.mp (hA i)).1 j

#print axioms bounded_representative_of_six_rows
#print axioms explicit_bounded_representative

end
end Fresh.FiniteRelations
