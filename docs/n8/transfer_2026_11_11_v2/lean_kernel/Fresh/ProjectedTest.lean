import Fresh.FibreTest

namespace Fresh.FiniteRelations

open Set MeasureTheory
open scoped BigOperators

noncomputable section

def PairedLower {n : ℕ} (T : Finset (Fin n → ℤ)) (μ : ℝ) : Prop :=
  ∃ (d : ℕ) (U : Fin d → Fin n → ℤ),
    (∀ m : Fin n → ℤ, (∀ j, ∑ i, m i * U j i = 0) ↔
      (fun i => (m i : ℝ)) ∈ rowSpace T) ∧
    ∀ x, μ ≤ phaseAverage U (phaseBump n) x + phaseAverage U (phaseBump n) (2 • x)

theorem common_paired_lower {n : ℕ} (S : Finset (Fin n → ℤ)) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ T ⊆ S, AdmissibleRows T → PairedLower T μ := by
  classical
  suffices ∀ F : Finset (Finset (Fin n → ℤ)),
      ∃ μ : ℝ, 0 < μ ∧ ∀ T ∈ F, AdmissibleRows T → PairedLower T μ by
    obtain ⟨μ,hμ,h⟩ := this S.powerset
    exact ⟨μ,hμ,fun T hT => h T (Finset.mem_powerset.mpr hT)⟩
  intro F
  induction F using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert T F _ ih =>
    obtain ⟨μ,hμ,h⟩ := ih
    by_cases ht : AdmissibleRows T
    · obtain ⟨d,U,η,hη,hU,hu⟩ := positive_paired_average T ht
      refine ⟨min μ η,lt_min hμ hη,fun W hw hW => ?_⟩
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact ⟨d,U,hU,fun x => (min_le_right _ _).trans (hu x)⟩
      · obtain ⟨d,U,hU,hu⟩ := h W hw hW
        exact ⟨d,U,hU,fun x => (min_le_left _ _).trans (hu x)⟩
    · refine ⟨μ,hμ,fun W hw hW => ?_⟩
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact (ht hW).elim
      · exact h W hw hW

theorem average_approx_below {n d : ℕ}
    (U : Fin d → Fin n → ℤ) (S : Finset (Fin n → ℤ)) (A : (Fin n → ℤ) → ℂ)
    (e : ℝ) (h : ∀ y, phaseBump n y - e ≤ (∑ m ∈ S, A m * torusMode m y).re)
    (x : PhaseTorus (Fin n)) :
    phaseAverage U (phaseBump n) x - e ≤
      (phaseAverage U (fun y => ∑ m ∈ S, A m * torusMode m y) x).re := by
  let P (y : PhaseTorus (Fin n)) := ∑ m ∈ S, A m * torusMode m y
  have hc : Continuous P := continuous_finset_sum _ fun m _ =>
    continuous_const.mul (torusMode m).continuous
  have ht := (continuous_const : Continuous (fun _ : PhaseTorus (Fin d) => x)).add
    (continuous_parameterMap U)
  have h1 := (phaseBump_continuous n).comp ht
  have h2 := Complex.continuous_re.comp (hc.comp ht)
  have hi₁ := h1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := parameterMeasure (Fin d))
  have hi₂ := h2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := parameterMeasure (Fin d))
  have hh := integral_mono (hi₁.sub (integrable_const e)) hi₂ (fun z => h (x+parameterMap U z))
  change (∫ z, phaseBump n (x+parameterMap U z)-e ∂parameterMeasure (Fin d)) ≤
    (∫ z, (P (x+parameterMap U z)).re ∂parameterMeasure (Fin d)) at hh
  have heq : (∫ z, phaseBump n (x+parameterMap U z)-e ∂parameterMeasure (Fin d)) =
      (∫ z, phaseBump n (x+parameterMap U z) ∂parameterMeasure (Fin d)) -
        (∫ _z, e ∂parameterMeasure (Fin d)) := integral_sub hi₁ (integrable_const e)
  rw [heq] at hh
  have hr := Complex.reCLM.integral_comp_comm
    ((hc.comp ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      (μ := parameterMeasure (Fin d)))
  change (∫ z, (P (x+parameterMap U z)).re ∂parameterMeasure (Fin d)) =
    (∫ z, P (x+parameterMap U z) ∂parameterMeasure (Fin d)).re at hr
  rw [hr] at hh
  simpa only [phaseAverage, integral_const, probReal_univ, one_smul] using hh

private theorem projected_at {n d : ℕ}
    (T : Finset (Fin n → ℤ)) (U : Fin d → Fin n → ℤ)
    (hU : ∀ m : Fin n → ℤ, (∀ j, ∑ i, m i * U j i = 0) ↔
      (fun i => (m i : ℝ)) ∈ rowSpace T)
    (S : Finset (Fin n → ℤ)) (A : (Fin n → ℤ) → ℂ) (x : Fin n → ℝ) :
    phaseAverage U (fun y => ∑ m ∈ S, A m * torusMode m y) (torusCast x) =
      phasePolynomial (projectedModes S (rowSpace T)) A x := by
  classical
  rw [phaseAverage_polynomial]
  simp only [hU,torusMode_cast,phasePolynomial,projectedModes,Finset.sum_filter]

/-- A single finite Fourier test serves every low rank space generated
at the preceding stage. Coefficients are scaled after approximation,
so no quantitative Fourier decay is needed. -/
theorem finite_projected_test {n : ℕ} (S : Finset (Fin n → ℤ)) :
    ∃ (S' : Finset (Fin n → ℤ)) (A : (Fin n → ℤ) → ℂ) (ε μ : ℝ),
      S ⊆ S' ∧ 0 < μ - 2*ε ∧
      (∑ m ∈ S', ‖A m‖ ≤ 1) ∧
      (∀ x : Fin n → ℝ, (∃ i, distInt (x i) ≤ 1/8) → (phasePolynomial S' A x).re ≤ ε) ∧
      (∀ T ⊆ S, AdmissibleRows T → ∀ x : Fin n → ℝ,
        μ ≤ (phasePolynomial (projectedModes S' (rowSpace T)) A x).re +
          (phasePolynomial (projectedModes S' (rowSpace T)) A (fun i => 2*x i)).re) := by
  classical
  obtain ⟨η,hη,hηall⟩ := common_paired_lower S
  let e := η/8
  have he : 0 < e := by dsimp [e]; positivity
  let g : C(PhaseTorus (Fin n),ℂ) :=
    ⟨fun x => (phaseBump n x : ℂ), Complex.continuous_ofReal.comp (phaseBump_continuous n)⟩
  obtain ⟨R,a,ha⟩ := torusMode_approx g he
  let Q := R ∪ S
  let B (m : Fin n → ℤ) := if m ∈ R then a m else 0
  have hQ (x : PhaseTorus (Fin n)) : (∑ m ∈ Q, B m * torusMode m x) =
      ∑ m ∈ R, a m * torusMode m x := by
    rw [← Finset.sum_subset (Finset.subset_union_left : R ⊆ Q)
      (fun m _ hm => by simp [B,hm])]
    exact Finset.sum_congr rfl fun m hm => by simp [B,hm]
  have happ (x : PhaseTorus (Fin n)) :
      |(∑ m ∈ Q, B m * torusMode m x).re - phaseBump n x| ≤ e := by
    rw [hQ]
    exact (Complex.abs_re_le_norm _).trans (ha x).le
  have hblo (x : Fin n → ℝ) (hx : ∃ i, distInt (x i) ≤ 1/8) :
      (phasePolynomial Q B x).re ≤ e := by
    have hh := (abs_le.mp (happ (torusCast x))).2
    simp only [torusMode_cast, phaseBump_blocked x hx, sub_zero] at hh
    exact hh
  have hlow (x : PhaseTorus (Fin n)) :
      phaseBump n x - e ≤ (∑ m ∈ Q, B m * torusMode m x).re := by
    linarith [(abs_le.mp (happ x)).1]
  have hproj (T : Finset (Fin n → ℤ)) (ht : T ⊆ S) (had : AdmissibleRows T) (x : Fin n → ℝ) :
      η - 2*e ≤ (phasePolynomial (projectedModes Q (rowSpace T)) B x).re +
        (phasePolynomial (projectedModes Q (rowSpace T)) B (fun i => 2*x i)).re := by
    obtain ⟨d,U,hU,hh⟩ := hηall T ht had
    have h₁ := average_approx_below U Q B e hlow (torusCast x)
    have h₂ := average_approx_below U Q B e hlow (torusCast (fun i => 2*x i))
    rw [projected_at T U hU] at h₁ h₂
    rw [torusCast_two] at h₂
    linarith [hh (torusCast x)]
  let K := 1 + ∑ m ∈ Q, ‖B m‖
  have hs : 0 ≤ ∑ m ∈ Q, ‖B m‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hK : 0 < K := by dsimp [K]; linarith
  let A (m : Fin n → ℤ) := ((K⁻¹ : ℝ) : ℂ) * B m
  have hA (P : Finset (Fin n → ℤ)) (x : Fin n → ℝ) :
      (phasePolynomial P A x).re = (phasePolynomial P B x).re / K := by
    have hh : phasePolynomial P A x = ((K⁻¹ : ℝ) : ℂ) * phasePolynomial P B x := by
      unfold phasePolynomial A
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      exact mul_assoc _ _ _
    rw [hh,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact mul_comm _ _
  refine ⟨Q,A,e/K,(η-2*e)/K,Finset.subset_union_right,?_,?_,?_,?_⟩
  · apply sub_pos.mpr
    rw [← mul_div_assoc]
    exact (div_lt_div_iff_of_pos_right hK).2 (by dsimp [e]; linarith)
  · have hh : (∑ m ∈ Q, ‖A m‖) = K⁻¹ * ∑ m ∈ Q, ‖B m‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      change ‖((K⁻¹ : ℝ) : ℂ) * B m‖ = _
      rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hK.le)]
    rw [hh,mul_comm, ← div_eq_mul_inv, div_le_one hK]
    dsimp [K]
    linarith
  · intro x hx
    rw [hA]
    exact div_le_div_of_nonneg_right (hblo x hx) hK.le
  · intro T ht had x
    rw [hA,hA,← add_div]
    exact div_le_div_of_nonneg_right (hproj T ht had x) hK.le

#print axioms finite_projected_test

end
end Fresh.FiniteRelations
