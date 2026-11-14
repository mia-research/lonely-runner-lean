import Fresh.RankFour
import Fresh.PhaseFibres

namespace Fresh.FiniteRelations

open scoped BigOperators
open Set

/-- A finite Fourier test on the phases. -/
noncomputable def phasePolynomial {n : ℕ} (modes : Finset (Fin n → ℤ))
    (A : (Fin n → ℤ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  ∑ m ∈ modes, A m * character (2*Real.pi*rowEval m x)

noncomputable def projectedModes {n : ℕ} (modes : Finset (Fin n → ℤ))
    (L : Submodule ℝ (Fin n → ℝ)) : Finset (Fin n → ℤ) := by
  classical
  exact modes.filter fun m => (fun i => (m i : ℝ)) ∈ L

private theorem continuous_phaseAlong {n : ℕ} (modes : Finset (Fin n → ℤ))
    (A : (Fin n → ℤ) → ℂ) (v : Fin n → ℝ) (q : ℝ) :
    Continuous (fun t : ℝ => phasePolynomial modes A (fun i => q*(v i*t))) := by
  unfold phasePolynomial rowEval character
  fun_prop

/-- At a stable span, separated omitted frequencies cannot hide a
positive projected test on both dilations. -/
theorem clear_of_projected_polynomial {n : ℕ}
    (modes : Finset (Fin n → ℤ)) (A : (Fin n → ℤ) → ℂ)
    (ha : ∑ m ∈ modes, ‖A m‖ ≤ 1) (L : Submodule ℝ (Fin n → ℝ))
    (v : Fin n → ℝ) (D a b ε μ : ℝ) (hD : 0 < D) (hab : a < b)
    (hsep : ∀ m ∈ modes \ projectedModes modes L, D ≤ |rowEval m v|)
    (hblocked : ∀ x : Fin n → ℝ, (∃ i, distInt (x i) ≤ 1/8) →
      (phasePolynomial modes A x).re ≤ ε)
    (hproj : ∀ x : Fin n → ℝ,
        μ ≤ (phasePolynomial (projectedModes modes L) A x).re +
            (phasePolynomial (projectedModes modes L) A (fun i => 2*x i)).re)
    (hgap : 2*ε*(b-a) + 2/D < μ*(b-a)) :
    ∃ t ∈ Icc a b,
      (∀ i, (1/8:ℝ) < distInt (v i*t)) ∨
      (∀ i, (1/8:ℝ) < distInt (2*(v i*t))) := by
  classical
  by_contra! hn
  let retained := projectedModes modes L
  let F (s : Finset (Fin n → ℤ)) (q t : ℝ) :=
    phasePolynomial s A (fun i => q*(v i*t))
  let G (s : Finset (Fin n → ℤ)) (q t : ℝ) := (F s q t).re
  have hc (s : Finset (Fin n → ℤ)) (q : ℝ) : Continuous (F s q) :=
    continuous_phaseAlong s A v q
  have hg (s : Finset (Fin n → ℤ)) (q : ℝ) : Continuous (G s q) :=
    Complex.continuous_re.comp (hc s q)
  have hrep (s : Finset (Fin n → ℤ)) (q t : ℝ) :
      F s q t = ∑ m ∈ s, A m * character (2*Real.pi*(q*rowEval m v)*t) := by
    unfold F phasePolynomial
    apply Finset.sum_congr rfl
    intro m _
    have hm : rowEval m (fun i => q*(v i*t)) = (q*rowEval m v)*t := by
      unfold rowEval
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hm]
    ring_nf
  have hint (q : ℝ) (hq : 1 ≤ q) :
      (∫ t in a..b, G retained q t) ≤ (∫ t in a..b, G modes q t) + 1/D := by
    have he := projected_integral_error modes retained A (fun m => q*rowEval m v)
      (a := a) (b := b) (D := D)
      (by exact Finset.filter_subset _ _) hD ha (by
        intro m hm
        rw [abs_mul,abs_of_nonneg (by linarith)]
        exact (hsep m hm).trans (le_mul_of_one_le_left (abs_nonneg _) hq))
    simp_rw [← hrep] at he
    have he' := (Complex.abs_re_le_norm _).trans he
    rw [Complex.sub_re] at he'
    have h1 := (abs_le.mp he').1
    have hreal (s : Finset (Fin n → ℤ)) :
        (∫ t in a..b, G s q t) = (∫ t in a..b, F s q t).re :=
      Complex.reCLM.intervalIntegral_comp_comm ((hc s q).intervalIntegrable _ _)
    rw [hreal,hreal]
    linarith
  have hupper (q : ℝ) (h : ∀ t ∈ Icc a b, ∃ i, distInt (q*(v i*t)) ≤ 1/8) :
      (∫ t in a..b, G modes q t) ≤ ε*(b-a) := by
    have hh := intervalIntegral.integral_mono_on hab.le ((hg modes q).intervalIntegrable (μ := MeasureTheory.volume) a b)
      (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) a b) (fun t ht => hblocked _ (h t ht))
    simpa [intervalIntegral.integral_const,smul_eq_mul,mul_comm] using hh
  have h1 := hupper 1 (fun t ht => by simpa only [one_mul] using (hn t ht).1)
  have h2 := hupper 2 (fun t ht => (hn t ht).2)
  have hl := intervalIntegral.integral_mono_on hab.le
    (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) a b)
    (((hg retained 1).add (hg retained 2)).intervalIntegrable a b)
    (fun t _ => by simpa only [G,F,one_mul,Pi.add_apply] using hproj (fun i => v i*t))
  change (∫ t in a..b, μ) ≤ (∫ t in a..b, G retained 1 t + G retained 2 t) at hl
  rw [intervalIntegral.integral_add ((hg retained 1).intervalIntegrable _ _)
    ((hg retained 2).intervalIntegrable _ _)] at hl
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hl
  have hl' : μ*(b-a) ≤ (∫ t in a..b, G retained 1 t) + ∫ t in a..b, G retained 2 t := by
    simpa only [mul_comm (b-a) μ] using hl
  have hd : 2 / D = 1 / D + 1 / D := by rw [← add_div]; norm_num
  rw [hd] at hgap
  have hh1 := (hint 1 (by norm_num)).trans (add_le_add_left h1 _)
  have hh2 := (hint 2 (by norm_num)).trans (add_le_add_left h2 _)
  have hh := hl'.trans (add_le_add hh1 hh2)
  apply (not_lt_of_ge hh)
  convert hgap using 1
  ring

/-- The integral estimate and the finite rank argument fit together
without enumerating any inputs. The remaining analytical hypothesis is
a uniform positive lower bound for the projected two-dilation test. -/
theorem clear_or_four_rows_of_projection {n bound : ℕ}
    (modes : Finset (Fin n → ℤ)) (A : (Fin n → ℤ) → ℂ)
    (hb : ∀ m ∈ modes, ∀ i, |m i| ≤ (bound : ℤ))
    (ha : ∑ m ∈ modes, ‖A m‖ ≤ 1)
    (ε μ : ℝ)
    (hblocked : ∀ x : Fin n → ℝ, (∃ i, distInt (x i) ≤ 1/8) →
      (phasePolynomial modes A x).re ≤ ε)
    (hproj : ∀ L : Submodule ℝ (Fin n → ℝ), Module.finrank ℝ L ≤ 3 →
      (∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧ ∀ z ∈ L, ∑ i, z i*w i = 0) →
      ∀ x : Fin n → ℝ,
        μ ≤ (phasePolynomial (projectedModes modes L) A x).re +
            (phasePolynomial (projectedModes modes L) A (fun i => 2*x i)).re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : Fin n → ℝ) (D a b : ℝ), 0 < D → a < b →
      (∀ i, C*D < v i) →
      2*ε*(b-a) + 2/D < μ*(b-a) →
      (∃ t ∈ Icc a b,
        (∀ i, (1/8:ℝ) < distInt (v i*t)) ∨
        (∀ i, (1/8:ℝ) < distInt (2*(v i*t)))) ∨
      (∃ rows : Fin 4 → Fin n → ℤ, (∀ j, rows j ∈ modes) ∧
        (∀ j, |rowEval (rows j) v| ≤ D) ∧
        LinearIndependent ℝ (fun j i => (rows j i : ℝ))) := by
  classical
  obtain ⟨C,hC,hrows⟩ := four_short_rows_or_positive_annihilator n bound
  refine ⟨C,hC,fun v D a b hD hab hfast hgap => ?_⟩
  rcases hrows modes v D hD.le hb hfast with hfour | ⟨hrank,hann⟩
  · exact Or.inr hfour
  apply Or.inl
  apply clear_of_projected_polynomial modes A ha (shortSpan modes v D) v D a b ε μ hD hab
    _ hblocked (hproj _ hrank hann) hgap
  intro m hm
  by_contra! hh
  obtain ⟨hmm,hnr⟩ := Finset.mem_sdiff.mp hm
  apply hnr
  unfold projectedModes
  exact Finset.mem_filter.mpr ⟨hmm, mem_shortSpan hmm hh.le⟩

#print axioms clear_of_projected_polynomial
#print axioms clear_or_four_rows_of_projection

end Fresh.FiniteRelations
