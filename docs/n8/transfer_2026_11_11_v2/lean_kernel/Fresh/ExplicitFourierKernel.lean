import Fresh.ExactClassicalReduction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Nat.Choose.Sum

namespace Fresh.FiniteRelations

open Set MeasureTheory
open scoped BigOperators

noncomputable section

private theorem circle_int_zero (m : ℤ) : (((m : ℝ)) : UnitAddCircle) = 0 := by
  rw [← mul_one (m : ℝ), ← zsmul_eq_mul, AddCircle.coe_zsmul,
    AddCircle.coe_period, smul_zero]

private theorem chord_lower (x : UnitAddCircle) : 4 * ‖x‖ ≤ ‖fourier 1 x - 1‖ := by
  obtain ⟨s,hs⟩ := QuotientAddGroup.mk_surjective x
  let y := s - (round s : ℝ)
  have hxy : (y : UnitAddCircle) = x := by
    change ((s - (round s : ℝ) : ℝ) : UnitAddCircle) = x
    rw [AddCircle.coe_sub, circle_int_zero, sub_zero]
    exact hs
  have hy : |y| ≤ 1/2 := abs_sub_round s
  have hn : ‖x‖ = |y| := by rw [← hs]; exact UnitAddCircle.norm_eq
  have harg : 0 ≤ Real.pi * |y| := by positivity
  have harg' : Real.pi * |y| ≤ Real.pi / 2 := by
    linarith [mul_le_mul_of_nonneg_left hy Real.pi_pos.le]
  have hsin := Real.mul_le_sin harg harg'
  have hsin' : 2 * |y| ≤ Real.sin (Real.pi * |y|) := by
    convert hsin using 1
    field_simp [Real.pi_ne_zero]
  have hexp : fourier (T := 1) 1 (y : UnitAddCircle) =
      Complex.exp (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ)) := by
    rw [fourier_coe_apply]
    push_cast
    congr 1
    ring
  rw [hn, ← hxy, hexp, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * Real.pi * y / 2 = Real.pi * y by ring]
  have habs : |Real.pi * y| = Real.pi * |y| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  have hsabs : |Real.sin (Real.pi * y)| = Real.sin (Real.pi * |y|) := by
    rw [← habs]
    apply Real.abs_sin_eq_sin_abs_of_abs_le_pi
    rw [habs]
    nlinarith [mul_le_mul_of_nonneg_left hy Real.pi_pos.le]
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2),
    Real.norm_eq_abs, hsabs]
  linarith

private def binomialWeight (N k : ℕ) : ℝ :=
  ((2*N).choose k : ℝ) / (4:ℝ)^N

private def circleKernel (N : ℕ) (x : UnitAddCircle) : ℂ :=
  ∑ k : Fin (2*N+1), (binomialWeight N k.val : ℂ) * fourier ((k.val : ℤ) - (N : ℤ)) x

private theorem circleKernel_norm (N : ℕ) (x : UnitAddCircle) :
    ‖circleKernel N x‖ = (‖fourier 1 x + 1‖ ^ 2 / 4)^N := by
  let z := fourier (T := 1) 1 x
  have hnz : ‖z‖ = 1 := by
    rw [show z = (AddCircle.toCircle x : ℂ) by exact fourier_one]
    exact Circle.norm_coe _
  have hpow (k : ℕ) : fourier (T := 1) (k : ℤ) x = z^k := by
    induction k with
    | zero => simp
    | succ k ih => simp only [Nat.cast_succ,fourier_add,ih,pow_succ,z]
  have hpoly : circleKernel N x =
      fourier (-(N : ℤ)) x * (z+1)^(2*N) / (4:ℂ)^N := by
    unfold circleKernel
    rw [add_pow, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    rw [sub_eq_add_neg, fourier_add, hpow]
    simp only [binomialWeight,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_ofNat,
      Complex.ofReal_natCast, one_pow, mul_one]
    ring
  rw [hpoly,norm_div,norm_mul,norm_pow,norm_pow,pow_mul,div_pow]
  rw [show ‖fourier (T := 1) (-(N : ℤ)) x‖ = 1 by
    rw [fourier_apply]; exact Circle.norm_coe _]
  norm_num [one_mul,z]

private theorem circleKernel_norm_le (N : ℕ) (x : UnitAddCircle) :
    ‖circleKernel N x‖ ≤ 1 := by
  rw [circleKernel_norm]
  have h : ‖fourier (T := 1) 1 x + 1‖ ≤ 2 := by
    exact (norm_add_le _ _).trans (by norm_num [fourier_one])
  exact pow_le_one₀ (by positivity) (by
    apply (div_le_iff₀ (by norm_num)).2
    simpa only [one_mul,show (2:ℝ)^2 = 4 by norm_num] using pow_le_pow_left₀ (norm_nonneg _) h 2)

private theorem circleKernel_norm_le_separated (N : ℕ) (x : UnitAddCircle)
    (hx : (1/56:ℝ) ≤ ‖x‖) :
    ‖circleKernel N x‖ ≤ (783/784:ℝ)^N := by
  rw [circleKernel_norm]
  apply pow_le_pow_left₀ (by positivity) _ _
  apply (div_le_iff₀ (by norm_num)).2
  have h := parallelogram_law_with_norm ℂ (fourier (T := 1) 1 x) (1 : ℂ)
  have h1 : ‖fourier (T := 1) 1 x‖ = 1 := by rw [fourier_one]; exact Circle.norm_coe _
  rw [h1,norm_one] at h
  have h2 : (1/14:ℝ) ≤ ‖fourier (T := 1) 1 x - 1‖ := by
    linarith [chord_lower x]
  have h3 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/14) h2 2
  nlinarith

private theorem kernel_numerics :
    (783/784:ℝ)^100352 < (1/(2*100352+1):ℝ)^7 := by
  have hB := one_add_mul_le_pow (a := (1/783:ℝ)) (by norm_num) 784
  have hb : (2:ℝ) ≤ (784/783:ℝ)^784 := by
    exact (by norm_num : (2:ℝ) ≤ 1+784*(1/783:ℝ)).trans
      (by convert hB using 2; norm_num)
  have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) hb
  have hpow : (783/784:ℝ)^784 ≤ 1/2 := by
    rw [← one_div_pow] at hi
    convert hi using 2; norm_num
  calc
    (783/784:ℝ)^100352 = ((783/784:ℝ)^784)^128 := by rw [← pow_mul]
    _ ≤ (1/2:ℝ)^128 := pow_le_pow_left₀ (by positivity) hpow _
    _ < (1/(2*100352+1):ℝ)^7 := by norm_num

private def modeIndex (N : ℕ) (k : Fin 7 → Fin (2*N+1)) : Fin 7 → ℤ :=
  fun i => (k i).val - (N : ℤ)

private def tensorWeight (N : ℕ) (k : Fin 7 → Fin (2*N+1)) : ℝ :=
  ∏ i, binomialWeight N (k i).val

private def tensorKernel (N : ℕ) (x : PhaseTorus (Fin 7)) : ℂ :=
  ∑ k : Fin 7 → Fin (2*N+1), (tensorWeight N k : ℂ) * torusMode (modeIndex N k) x

private theorem tensorKernel_prod (N : ℕ) (x : PhaseTorus (Fin 7)) :
    tensorKernel N x = ∏ i, circleKernel N (x i) := by
  classical
  unfold tensorKernel circleKernel
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hm : torusMode (modeIndex N k) x = ∏ i, fourier (modeIndex N k i) (x i) := by
    simp only [torusMode,ContinuousMap.coe_mk,torusEval,fourier_apply,one_zsmul]
    induction (Finset.univ : Finset (Fin 7)) using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi,Finset.prod_insert hi,AddCircle.toCircle_add,Circle.coe_mul,ih]
  rw [hm, tensorWeight, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  rfl

private theorem tensorKernel_average {d : ℕ} (N : ℕ) (U : Fin d → Fin 7 → ℤ)
    (x : PhaseTorus (Fin 7)) :
    phaseAverage U (tensorKernel N) x =
      ∑ k : Fin 7 → Fin (2*N+1),
        if (∀ j, ∑ i, modeIndex N k i * U j i = 0) then
          (tensorWeight N k : ℂ) * torusMode (modeIndex N k) x else 0 := by
  classical
  let e : (Fin 7 → Fin (2*N+1)) ↪ (Fin 7 → ℤ) :=
    ⟨modeIndex N,fun a b h => funext fun i => Fin.ext (by
      have hi := congrFun h i
      dsimp [modeIndex] at hi
      omega)⟩
  let A := Function.extend e (fun k => (tensorWeight N k : ℂ)) 0
  have hA (k : Fin 7 → Fin (2*N+1)) : A (e k) = tensorWeight N k :=
    e.injective.extend_apply _ _ _
  have hkernel : tensorKernel N = fun y =>
      ∑ m ∈ Finset.univ.map e, A m * torusMode m y := by
    funext y
    rw [Finset.sum_map]
    simp only [hA, tensorKernel]
    rfl
  rw [hkernel,phaseAverage_polynomial,Finset.sum_map]
  simp only [hA]
  rfl

private theorem tensorKernel_average_lower {d : ℕ} (N : ℕ)
    (U : Fin d → Fin 7 → ℤ) :
    (1 / (2 * (N : ℝ) + 1))^7 ≤ (phaseAverage U (tensorKernel N) 0).re := by
  classical
  have hw : (1 / (2 * (N : ℝ) + 1)) ≤ binomialWeight N N := by
    unfold binomialWeight
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    simpa only [one_mul,mul_comm] using (show (4:ℝ)^N ≤
      (2 * (N : ℝ) + 1) * ((2*N).choose N : ℝ) by
        exact_mod_cast Nat.four_pow_le_two_mul_add_one_mul_central_binom N)
  let k₀ : Fin 7 → Fin (2*N+1) := fun _ => ⟨N,by omega⟩
  have hk : modeIndex N k₀ = 0 := by ext i; simp [modeIndex,k₀]
  rw [tensorKernel_average,Complex.re_sum]
  calc
    (1 / (2 * (N : ℝ) + 1))^7 ≤ tensorWeight N k₀ := by
      rw [tensorWeight]
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
        Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 7)))
          (f := fun _ => 1 / (2 * (N : ℝ) + 1)) (fun _ _ => by positivity)
          (fun i _ => (show _ ≤ binomialWeight N (k₀ i).val from hw))
    _ ≤ _ := by
      have h := Finset.single_le_sum (s := Finset.univ)
        (f := fun k : Fin 7 → Fin (2*N+1) =>
          (if (∀ j, ∑ i, modeIndex N k i * U j i = 0) then
            (tensorWeight N k : ℂ) * torusMode (modeIndex N k) 0 else 0).re)
        (by
          intro k _
          dsimp only
          split_ifs
          · have he : torusMode (modeIndex N k) 0 = 1 := by simp [torusMode,torusEval]
            rw [he,mul_one,Complex.ofReal_re]
            unfold tensorWeight binomialWeight
            positivity
          · simp)
        (Finset.mem_univ k₀)
      simpa [hk] using h

/-- For a model containing a phase clear at `1/7`, all integer trajectories
without a strict `1/8` witness differ on some frequency in the explicit cube. -/
private theorem character_test_of_power {d : ℕ} (N : ℕ)
    (hN : (783/784:ℝ)^N < (1/(2*(N:ℝ)+1))^7) (U : Fin d → Fin 7 → ℤ)
    (hu : MergedPhase U) (p : Fin 7 → ℤ)
    (hp : ¬ StrictlyClears (fun i => (p i : ℝ)) (1/8)) :
    ∃ m : Fin 7 → ℤ, (∀ i, |m i| ≤ (N : ℤ)) ∧
      ¬ ((∀ j, ∑ i, m i * U j i = 0) ↔ ∑ i, m i * p i = 0) := by
  classical
  obtain ⟨z,hz⟩ := hu
  let W (_ : Fin 1) := p
  let y := parameterMap U z
  let G (x : PhaseTorus (Fin 7)) := tensorKernel N (x + -y)
  by_contra! h
  have hsame : phaseAverage U (tensorKernel N) (-y) = phaseAverage W (tensorKernel N) (-y) := by
    rw [tensorKernel_average,tensorKernel_average]
    apply Finset.sum_congr rfl
    intro k _
    have hm (i : Fin 7) : |modeIndex N k i| ≤ (N : ℤ) := by
      have hi := (k i).isLt
      dsimp [modeIndex]
      exact abs_le.mpr (by omega)
    simp only [W, Fin.forall_fin_one, h _ hm]
  have hshift : phaseAverage U (tensorKernel N) (-y) = phaseAverage U (tensorKernel N) 0 := by
    have hneg : parameterMap U (-z) = -y := by
      apply eq_neg_of_add_eq_zero_left
      change parameterMap U (-z) + parameterMap U z = 0
      rw [← parameterMap_add,neg_add_cancel]
      ext i
      simp [parameterMap]
    simpa only [phaseAverage,parameterMap_add,hneg,zero_add] using
      integral_add_left_eq_self (μ := parameterMeasure (Fin d))
        (fun x => tensorKernel N (parameterMap U x)) (-z)
  have hc (k : ℕ) : Continuous (tensorKernel k) :=
    continuous_finset_sum _ fun m _ =>
      continuous_const.mul (torusMode (modeIndex k m)).continuous
  have hG : Continuous G := (hc N).comp (continuous_id.add continuous_const)
  have hupper (x : PhaseTorus (Fin 1)) :
      (G (parameterMap W x)).re ≤ (783/784:ℝ)^N := by
    obtain ⟨i,hi⟩ := blocked_period_point p hp x
    have hgap : (1/56:ℝ) ≤ ‖(parameterMap W x + -y) i‖ := by
      have h1 := norm_sub_norm_le (y i) (parameterMap W x i)
      rw [← norm_neg (y i - parameterMap W x i),neg_sub] at h1
      simp only [Pi.add_apply, Pi.neg_apply, ← sub_eq_add_neg]
      have h2 := hz i
      change (1/7:ℝ) ≤ ‖y i‖ at h2
      linarith
    apply (Complex.re_le_norm _).trans
    dsimp only [G]
    rw [tensorKernel_prod,Complex.norm_prod]
    have hprod := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 7)))
      (f := fun j => ‖circleKernel N ((parameterMap W x + -y) j)‖)
      (g := fun j => if j = i then (783/784:ℝ)^N else 1)
      (fun _ _ => norm_nonneg _) (fun j _ => by
        dsimp only
        split_ifs with hj
        · subst j; exact circleKernel_norm_le_separated _ _ hgap
        · exact circleKernel_norm_le _ _)
    simpa using hprod
  have hmean := period_average_le W G hG _ hupper
  have he : phaseAverage W G 0 = phaseAverage W (tensorKernel N) (-y) := by
    unfold phaseAverage
    congr 1
    funext w
    simp only [G,zero_add]
    rw [add_comm]
  rw [he,← hsame,hshift] at hmean
  exact (not_le_of_gt hN) ((tensorKernel_average_lower N U).trans hmean)

theorem explicit_character_test {d : ℕ} (U : Fin d → Fin 7 → ℤ)
    (hu : MergedPhase U) (p : Fin 7 → ℤ)
    (hp : ¬ StrictlyClears (fun i => (p i : ℝ)) (1/8)) :
    ∃ m : Fin 7 → ℤ, (∀ i, |m i| ≤ 100352) ∧
      ¬ ((∀ j, ∑ i, m i * U j i = 0) ↔ ∑ i, m i * p i = 0) :=
  character_test_of_power 100352 (by have h := kernel_numerics; norm_num at h ⊢; exact h) U hu p hp

/-- The single finite set of candidate relations for the explicit test. -/
@[irreducible] def characterCube (N : ℤ) : Finset (Fin 7 → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-N) N)

theorem mem_characterCube (N : ℤ) (m : Fin 7 → ℤ) :
    m ∈ characterCube N ↔ ∀ i, |m i| ≤ N := by
  simp only [characterCube,Fintype.mem_piFinset,Finset.mem_Icc,abs_le]

private theorem short_cube_test {d : ℕ} (U : Fin d → Fin 7 → ℤ)
    (hU : MergedPhase U) (p : Fin 7 → ℤ)
    (hp : ¬ StrictlyClears (fun i => (p i : ℝ)) (1/8)) :
    ∃ m ∈ (characterCube 100352), ¬ ((∀ j, ∑ i, m i * U j i = 0) ↔ ∑ i, m i * p i = 0) := by
  obtain ⟨m,hm,h⟩ := explicit_character_test U hU p hp
  exact ⟨m,(mem_characterCube 100352 m).mpr hm,h⟩

theorem explicit_matching_kernel_finrank
    (hmerge : ∀ (d : ℕ) (U : Fin d → Fin 7 → ℤ),
      (∀ i, (fun j => U j i) ≠ 0) →
      (∃ i k, ¬ ∀ j q, U j i * U q k = U q i * U j k) →
      MergedPhase U)
    (p : Fin 7 → ℤ) (hp : ∀ i, 0 < p i)
    (hn : ¬ StrictlyClears (fun i => (p i : ℝ)) (1/8)) :
    Module.finrank ℚ (rationalKernel ((characterCube 100352).filter fun m => ∑ i, m i * p i = 0)) ≤ 1 :=
  matching_kernel_finrank_le_one (characterCube 100352) short_cube_test hmerge p hp hn

theorem explicit_integer_profiles
    (hmerge : ∀ (d : ℕ) (U : Fin d → Fin 7 → ℤ),
      (∀ i, (fun j => U j i) ≠ 0) →
      (∃ i k, ¬ ∀ j q, U j i * U q k = U q i * U j k) →
      MergedPhase U) :
    ∃ F : Finset (Fin 7 → ℤ), (∀ q ∈ F, ∀ i, 0 < q i) ∧
      ∀ p : Fin 7 → ℤ, (∀ i, 0 < p i) →
        StrictlyClears (fun i => (p i : ℝ)) (1/8) ∨
        ∃ q ∈ F, ∃ c : ℚ, ∀ i, c * (q i : ℚ) = (p i : ℚ) :=
  finite_integer_profiles_of_character_test (characterCube 100352) short_cube_test hmerge

#print axioms explicit_character_test
#print axioms explicit_integer_profiles

end
end Fresh.FiniteRelations
