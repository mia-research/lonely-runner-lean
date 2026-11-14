import Fresh.ProjectedTest
import Fresh.UniformPhaseAverage

namespace Fresh.FiniteRelations

open Set MeasureTheory
open scoped BigOperators

noncomputable section

def Clears {n : ℕ} (v : Fin n → ℝ) (c : ℝ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ ∀ i, c ≤ distInt (v i * t)

def StrictlyClears {n : ℕ} (v : Fin n → ℝ) (c : ℝ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ ∀ i, c < distInt (v i * t)

def MergedPhase {d : ℕ} (U : Fin d → Fin 7 → ℤ) : Prop :=
  ∃ z, ∀ i, (1/7:ℝ) ≤ ‖parameterMap U z i‖

private theorem common_merged_lower :
    ∃ μ : ℝ, 0 < μ ∧ ∀ {d : ℕ} (U : Fin d → Fin 7 → ℤ),
      MergedPhase U → μ ≤ phaseAverage U (phaseBump 7) 0 := by
  obtain ⟨μ,hμ,h⟩ := uniform_phase_average 7
    (r := 1/224) (a := (1/112)^7) (by norm_num) (by norm_num)
  refine ⟨μ,hμ,fun U hU => h U _ (phaseBump_continuous 7) phaseBump_nonneg ?_⟩
  obtain ⟨z,hz⟩ := hU
  refine ⟨z,fun x hx => ?_⟩
  have hdist := (dist_pi_lt_iff (by norm_num : (0:ℝ) < 2*(1/224))).mp hx
  have hb (i : Fin 7) : (1/112:ℝ) ≤ max 0 (‖x i‖ - 1/8) := by
    have hd := hdist i
    rw [dist_comm,dist_eq_norm] at hd
    have := norm_sub_norm_le (parameterMap U z i) (x i)
    exact (by linarith [hz i] : (1/112:ℝ) ≤ ‖x i‖ - 1/8).trans (le_max_right _ _)
  calc
    (1/112:ℝ)^7 = ∏ _i : Fin 7, (1/112:ℝ) := by simp
    _ ≤ phaseBump 7 x := Finset.prod_le_prod (fun _ _ => by norm_num) (fun i _ => hb i)

theorem period_average_le {n d : ℕ} (U : Fin d → Fin n → ℤ)
    (P : PhaseTorus (Fin n) → ℂ) (hc : Continuous P) (e : ℝ)
    (h : ∀ z, (P (parameterMap U z)).re ≤ e) :
    (phaseAverage U P 0).re ≤ e := by
  have hi := (hc.comp (continuous_parameterMap U)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := parameterMeasure (Fin d))
  have hh := integral_mono (Complex.continuous_re.comp (hc.comp (continuous_parameterMap U))
    |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      (μ := parameterMeasure (Fin d))) (integrable_const e) h
  have he := Complex.reCLM.integral_comp_comm hi
  change (∫ z, (P (parameterMap U z)).re ∂parameterMeasure (Fin d)) =
    (∫ z, P (parameterMap U z) ∂parameterMeasure (Fin d)).re at he
  change (∫ z, (P (parameterMap U z)).re ∂parameterMeasure (Fin d)) ≤ _ at hh
  rw [he] at hh
  simpa only [phaseAverage, zero_add, integral_const, probReal_univ, one_smul] using hh

theorem blocked_period_point {n : ℕ} (p : Fin n → ℤ)
    (hp : ¬ StrictlyClears (fun i => (p i : ℝ)) (1/8))
    (x : PhaseTorus (Fin 1)) :
    ∃ i, ‖parameterMap (fun _ : Fin 1 => p) x i‖ ≤ 1/8 := by
    obtain ⟨s,hs⟩ := QuotientAddGroup.mk_surjective (x 0)
    have hx : x = torusCast (fun _ => s + (1 + ⌈|s|⌉ : ℤ)) := by
      ext j
      fin_cases j
      change x 0 = ((s + (1 + ⌈|s|⌉ : ℤ) : ℝ) : UnitAddCircle)
      rw [← hs, AddCircle.coe_add]
      have hz : ((((1 + ⌈|s|⌉ : ℤ) : ℝ)) : UnitAddCircle) = 0 := by
        rw [← mul_one (((1 + ⌈|s|⌉ : ℤ) : ℝ)), ← zsmul_eq_mul, AddCircle.coe_zsmul,
          AddCircle.coe_period, smul_zero]
      rw [hz,add_zero]
    have ht : 0 < s + ((1 + ⌈|s|⌉ : ℤ) : ℝ) := by
      push_cast
      linarith [neg_abs_le s, Int.le_ceil |s|]
    rw [hx,parameterMap_cast]
    by_contra! h
    apply hp
    refine ⟨_,ht,fun i => ?_⟩
    have hi := h i
    rw [torusCast,UnitAddCircle.norm_eq] at hi
    simpa only [Fin.sum_univ_one] using hi

/-- One finite set of characters tests every model whose bump average is
bounded below by the same positive constant. -/
theorem finite_character_test (n : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    ∃ S : Finset (Fin n → ℤ), ∀ {d : ℕ} (U : Fin d → Fin n → ℤ),
      μ ≤ phaseAverage U (phaseBump n) 0 →
      ∀ p : Fin n → ℤ, ¬ StrictlyClears (fun i => (p i : ℝ)) (1/8) →
      ∃ m ∈ S, ¬ ((∀ j, ∑ i, m i * U j i = 0) ↔ ∑ i, m i * p i = 0) := by
  classical
  let e := μ / 4
  have he : 0 < e := div_pos hμ (by norm_num)
  let g : C(PhaseTorus (Fin n),ℂ) :=
    ⟨fun x => (phaseBump n x : ℂ), Complex.continuous_ofReal.comp (phaseBump_continuous n)⟩
  obtain ⟨S,A,hA⟩ := torusMode_approx g he
  refine ⟨S,fun U hu p hp => ?_⟩
  by_contra! hm
  let P (x : PhaseTorus (Fin n)) := ∑ m ∈ S, A m * torusMode m x
  let W (_ : Fin 1) := p
  have hlow (x : PhaseTorus (Fin n)) : phaseBump n x - e ≤ (P x).re := by
    have h := (Complex.abs_re_le_norm _).trans_lt (hA x)
    change |(P x - (phaseBump n x : ℂ)).re| < e at h
    rw [Complex.sub_re, Complex.ofReal_re] at h
    linarith [(abs_lt.mp h).1]
  have hmodel := average_approx_below U S A e hlow 0
  have hsame : phaseAverage U P 0 = phaseAverage W P 0 := by
    unfold P
    rw [phaseAverage_polynomial, phaseAverage_polynomial]
    apply Finset.sum_congr rfl
    intro m hms
    simp only [W, Fin.forall_fin_one, hm m hms]
  have hblocked (x : PhaseTorus (Fin 1)) : phaseBump n (parameterMap W x) = 0 := by
    obtain ⟨i,hi⟩ := blocked_period_point p hp x
    exact Finset.prod_eq_zero (Finset.mem_univ i) (max_eq_left (sub_nonpos.mpr hi))
  have hline := period_average_le W P
    (continuous_finset_sum _ fun m _ => continuous_const.mul (torusMode m).continuous) e
    (fun x => by
      have h := (Complex.abs_re_le_norm _).trans_lt (hA (parameterMap W x))
      change |(P (parameterMap W x) - (phaseBump n (parameterMap W x) : ℂ)).re| < e at h
      simpa only [hblocked x,Complex.ofReal_zero,sub_zero] using (le_of_lt (lt_of_le_of_lt
        (le_abs_self _) h)))
  have hm' : μ - e ≤ (phaseAverage U P 0).re :=
    (sub_le_sub_right hu e).trans hmodel
  clear hmodel
  rw [hsame] at hm'
  dsimp [e] at hm' hline
  linarith

private theorem has_nonparallel_rows {d : ℕ} (V : Submodule ℚ (Fin 7 → ℚ))
    (U : Fin d → Fin 7 → ℤ) (hU : ∀ j, (fun i => (U j i : ℚ)) ∈ V)
    (hrep : ∀ w ∈ V, ∃ c : Fin d → ℚ, ∀ i, ∑ j, c j * (U j i : ℚ) = w i)
    (hdim : 1 < Module.finrank ℚ V) (hnz : ∀ i, (fun j => U j i) ≠ 0) :
    ∃ i k, ¬ ∀ j q, U j i * U q k = U q i * U j k := by
  by_contra! h
  obtain ⟨q,hq⟩ := Function.ne_iff.mp (hnz 0)
  have hq' : (U q 0 : ℚ) ≠ 0 := by exact_mod_cast hq
  apply (not_le_of_gt hdim)
  apply finrank_le_one ⟨(fun i => (U q i : ℚ)), hU q⟩
  intro w
  obtain ⟨c,hc⟩ := hrep w.val w.property
  refine ⟨w.val 0 / (U q 0 : ℚ),Subtype.ext (funext fun i => ?_)⟩
  change w.val 0 / (U q 0 : ℚ) * (U q i : ℚ) = w.val i
  apply (mul_right_cancel₀ hq')
  calc
    (w.val 0 / (U q 0 : ℚ) * (U q i : ℚ)) * (U q 0 : ℚ) =
        w.val 0 * (U q i : ℚ) := by field_simp
    _ = w.val i * (U q 0 : ℚ) := by
      rw [← hc 0, ← hc i, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      have hj : (U j 0 : ℚ) * (U q i : ℚ) = (U q 0 : ℚ) * (U j i : ℚ) := by
        exact_mod_cast h 0 i j q
      rw [mul_assoc, hj, mul_comm (U q 0 : ℚ), ← mul_assoc]

private def integerPoint (p : Fin 7 → ℤ) : Fin 7 → ℚ := fun i => p i

/-- A single test fixes all relevant exact relations at once. If a
positive integer profile has no strict witness, their kernel has dimension one. -/
theorem matching_kernel_finrank_le_one
    (S : Finset (Fin 7 → ℤ))
    (hS : ∀ {d : ℕ} (U : Fin d → Fin 7 → ℤ), MergedPhase U →
      ∀ p : Fin 7 → ℤ, ¬ StrictlyClears (fun i => (p i : ℝ)) (1/8) →
        ∃ m ∈ S, ¬ ((∀ j, ∑ i, m i * U j i = 0) ↔ ∑ i, m i * p i = 0))
    (hmerge : ∀ (d : ℕ) (U : Fin d → Fin 7 → ℤ),
      (∀ i, (fun j => U j i) ≠ 0) →
      (∃ i k, ¬ ∀ j q, U j i * U q k = U q i * U j k) →
      MergedPhase U)
    (p : Fin 7 → ℤ) (hp : ∀ i, 0 < p i)
    (hpclear : ¬ StrictlyClears (fun i => (p i : ℝ)) (1/8)) :
    Module.finrank ℚ (rationalKernel (S.filter fun m => ∑ i, m i * p i = 0)) ≤ 1 := by
  classical
  let T := S.filter fun m => ∑ i, m i * p i = 0
  have hpV : integerPoint p ∈ rationalKernel T := by
    apply mem_rationalKernel.mpr
    intro m
    have hh := (Finset.mem_filter.mp m.property).2
    change (∑ i, (m.val i : ℚ) * (p i : ℚ)) = 0
    exact_mod_cast hh
  by_contra! hd
  obtain ⟨d,U,hU,hbasis,hann⟩ := integer_parameters_basis (rationalKernel T)
  have hnz (i : Fin 7) : (fun j => U j i) ≠ 0 := by
    intro hz
    obtain ⟨c,hc⟩ := hbasis (integerPoint p) hpV
    have hzero : integerPoint p i = 0 := by
      rw [← hc i]
      simp [show ∀ j, U j i = 0 from fun j => congrFun hz j]
    exact (hp i).ne' (by dsimp [integerPoint] at hzero; exact_mod_cast hzero)
  have hphase := hmerge d U hnz (has_nonparallel_rows (rationalKernel T) U hU hbasis hd hnz)
  obtain ⟨m,hm,hchange⟩ := hS U hphase p hpclear
  apply hchange
  rw [hann]
  constructor
  · intro h
    have hz := h _ hpV
    dsimp only [integerPoint] at hz
    exact_mod_cast hz
  · intro h w hw
    exact mem_rationalKernel.mp hw ⟨m,Finset.mem_filter.mpr ⟨hm,h⟩⟩

/-- An exact-character test forces the common kernel of the matching
relations to be a line for every profile without strict clearance. -/
theorem finite_integer_profiles_of_character_test
    (S : Finset (Fin 7 → ℤ))
    (hS : ∀ {d : ℕ} (U : Fin d → Fin 7 → ℤ), MergedPhase U →
      ∀ p : Fin 7 → ℤ, ¬ StrictlyClears (fun i => (p i : ℝ)) (1/8) →
        ∃ m ∈ S, ¬ ((∀ j, ∑ i, m i * U j i = 0) ↔ ∑ i, m i * p i = 0))
    (hmerge : ∀ (d : ℕ) (U : Fin d → Fin 7 → ℤ),
      (∀ i, (fun j => U j i) ≠ 0) →
      (∃ i k, ¬ ∀ j q, U j i * U q k = U q i * U j k) →
      MergedPhase U) :
    ∃ F : Finset (Fin 7 → ℤ), (∀ q ∈ F, ∀ i, 0 < q i) ∧
      ∀ p : Fin 7 → ℤ, (∀ i, 0 < p i) →
        StrictlyClears (fun i => (p i : ℝ)) (1/8) ∨
        ∃ q ∈ F, ∃ c : ℚ, ∀ i, c * (q i : ℚ) = (p i : ℚ) := by
  classical
  let line (T : Finset (Fin 7 → ℤ)) := rationalKernel T
  let positivePoint (T : Finset (Fin 7 → ℤ)) :=
    ∃ q : Fin 7 → ℤ, integerPoint q ∈ line T ∧ ∀ i, 0 < q i
  let A := S.powerset.filter fun T => Module.finrank ℚ (line T) ≤ 1 ∧ positivePoint T
  let representative (T : A) : Fin 7 → ℤ := (Finset.mem_filter.mp T.property).2.2.choose
  have hrep (T : A) : integerPoint (representative T) ∈ line T.val ∧
      ∀ i, 0 < representative T i := (Finset.mem_filter.mp T.property).2.2.choose_spec
  refine ⟨A.attach.image representative,?_,fun p hp => ?_⟩
  · intro q hq
    obtain ⟨T,_,rfl⟩ := Finset.mem_image.mp hq
    exact (hrep T).2
  by_cases hpclear : StrictlyClears (fun i => (p i : ℝ)) (1/8)
  · exact Or.inl hpclear
  let T := S.filter fun m => ∑ i, m i * p i = 0
  have hpV : integerPoint p ∈ line T := by
    apply mem_rationalKernel.mpr
    intro m
    have hh := (Finset.mem_filter.mp m.property).2
    change (∑ i, (m.val i : ℚ) * (p i : ℚ)) = 0
    exact_mod_cast hh
  have hdim : Module.finrank ℚ (line T) ≤ 1 :=
    matching_kernel_finrank_le_one S hS hmerge p hp hpclear
  let T' : A := ⟨T,Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),hdim,⟨p,hpV,hp⟩⟩⟩
  let q := representative T'
  have hspan : Submodule.span ℚ {integerPoint q} ≤ line T := by
    simpa only [Submodule.span_le,Set.singleton_subset_iff] using (hrep T').1
  have hne : integerPoint q ≠ 0 := by
    intro e
    have hz : (q 0 : ℚ) = 0 := congrFun e 0
    exact ((hrep T').2 0).ne' (by exact_mod_cast hz)
  have heq : Submodule.span ℚ {integerPoint q} = line T := by
    apply Submodule.eq_of_le_of_finrank_le hspan
    rwa [finrank_span_singleton hne]
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (heq ▸ hpV)
  exact Or.inr ⟨q,Finset.mem_image_of_mem _ (Finset.mem_attach _ _),c,congrFun hc⟩

/-- A finite family of positive integer profiles handles every line
left by the strict-witness alternative. -/
theorem finite_integer_profiles
    (hmerge : ∀ (d : ℕ) (U : Fin d → Fin 7 → ℤ),
      (∀ i, (fun j => U j i) ≠ 0) →
      (∃ i k, ¬ ∀ j q, U j i * U q k = U q i * U j k) →
      MergedPhase U) :
    ∃ F : Finset (Fin 7 → ℤ), (∀ q ∈ F, ∀ i, 0 < q i) ∧
      ∀ p : Fin 7 → ℤ, (∀ i, 0 < p i) →
        StrictlyClears (fun i => (p i : ℝ)) (1/8) ∨
        ∃ q ∈ F, ∃ c : ℚ, ∀ i, c * (q i : ℚ) = (p i : ℚ) := by
  obtain ⟨μ,hμ,hlower⟩ := common_merged_lower
  obtain ⟨S,hS⟩ := finite_character_test 7 hμ
  exact finite_integer_profiles_of_character_test S
    (fun U hU p hp => hS U (hlower U hU) p hp) hmerge

#print axioms finite_character_test
#print axioms finite_integer_profiles

end
end Fresh.FiniteRelations
