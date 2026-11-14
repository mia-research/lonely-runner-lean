import Fresh.BufferedFast
import Fresh.HarmonicCutoff

namespace Fresh.FiniteRelations

open Set MeasureTheory
open scoped BigOperators

/-- The same finite tests work for exact shifted harmonic circles.
This proves a finite cutoff qualitatively, without lattice transference. -/
theorem harmonic_clear_or_exact_rows (n : ℕ) :
    ∃ S : Finset (Fin n → ℤ), ∀ p : Fin n → ℤ, (∀ i, 0 < p i) →
      (∀ x : Fin n → ℝ, ∃ q : ℕ, (q=1 ∨ q=2) ∧ ∃ t : ℝ,
        ∀ i, (1/8:ℝ) < distInt ((q:ℝ)*x i+(p i:ℝ)*t)) ∨
      (∃ rows : Fin 4 → Fin n → ℤ, (∀ j, rows j ∈ S) ∧
        (∀ j, ∑ i, rows j i*p i = 0) ∧ LinearIndependent ℝ (fun j i => (rows j i : ℝ))) := by
  classical
  let S := stages n
  refine ⟨S 4,fun p hp => ?_⟩
  let v : Fin n → ℝ := fun i => p i
  let L (j : ℕ) := shortSpan (S j) v 0
  have hS : Monotone S := monotone_nat_of_le_succ fun j => (next (S j)).subset
  have hmono : Monotone L := fun _ _ hj => shortSpan_mono (hS hj) le_rfl
  let N := ∑ m ∈ S 4, ∑ i : Fin n, (m i).natAbs
  have hb (m : Fin n → ℤ) (hm : m ∈ S 4) (i : Fin n) : |m i| ≤ (N : ℤ) := by
    have h1 : (m i).natAbs ≤ ∑ i : Fin n, (m i).natAbs :=
      Finset.single_le_sum (f := fun k : Fin n => (m k).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 : (∑ i : Fin n, (m i).natAbs) ≤ N :=
      Finset.single_le_sum (f := fun z : Fin n → ℤ => ∑ i : Fin n, (z i).natAbs)
        (fun _ _ => Nat.zero_le _) hm
    rw [← Int.natCast_natAbs]
    exact_mod_cast h1.trans h2
  obtain ⟨C,_,hC⟩ := four_short_rows_or_positive_annihilator n N
  rcases hC (S 4) v 0 le_rfl hb (fun i => by
    rw [mul_zero]
    change (0:ℝ) < (p i:ℝ)
    exact_mod_cast hp i) with ⟨r,hr,hfreq,hli⟩ | ⟨hr,hann⟩
  · refine Or.inr ⟨r,hr,fun j => ?_,hli⟩
    have h := abs_nonpos_iff.mp (hfreq j)
    dsimp only [v] at h
    exact_mod_cast h
  obtain ⟨j,hj,he⟩ := stable_rank_transition L hmono hr
  have hj4 := hmono (show j ≤ 4 by omega)
  let P := next (S j)
  let T := (S j).filter fun m => ∑ i, m i*p i = 0
  have hT : rowSpace T = L j := by
    rw [rowSpace_eq_span_image]
    unfold L shortSpan
    apply congrArg (Submodule.span ℝ)
    ext x
    simp only [T,Finset.coe_filter,Set.mem_image,Set.mem_setOf_eq,abs_nonpos_iff,v]
    constructor
    · rintro ⟨m,⟨hm,hf⟩,rfl⟩
      exact ⟨m,hm,by exact_mod_cast hf,rfl⟩
    · rintro ⟨m,hm,hf,rfl⟩
      exact ⟨m,⟨hm,by exact_mod_cast hf⟩,rfl⟩
  have had : AdmissibleRows T := by
    unfold AdmissibleRows
    rw [hT]
    obtain ⟨w,hwpos,hwe⟩ := hann
    exact ⟨(Submodule.finrank_mono hj4).trans hr,⟨w,hwpos,fun z hz => hwe z (hj4 hz)⟩⟩
  have hproj := P.projected T (Finset.filter_subset _ _) had
  have hexact (m : Fin n → ℤ) (hm : m ∈ P.modes) :
      (fun i => (m i : ℝ)) ∈ rowSpace T ↔ ∑ i, m i*p i = 0 := by
    constructor
    · intro h
      have hv : v ∈ LinearMap.ker (dotForm (fun i => (m i : ℝ))) := by
        apply LinearMap.mem_ker.mpr
        have hp' : ∀ z ∈ L j, dotForm z v = 0 := by
          intro z hz
          apply Submodule.span_induction (p := fun y _ => dotForm y v = 0) _ _ _ _ hz
          · rintro _ ⟨k,_,hk,rfl⟩
            simpa only [dotForm_apply] using abs_nonpos_iff.mp hk
          · simp
          · intro a b _ _ ha hb
            simp only [dotForm_apply,Pi.add_apply,add_mul,Finset.sum_add_distrib] at *
            rw [ha,hb,add_zero]
          · intro c a _ ha
            simp only [dotForm_apply,Pi.smul_apply,smul_eq_mul] at *
            simp_rw [mul_assoc,← Finset.mul_sum,ha,mul_zero]
        exact hp' _ (hT ▸ h)
      have hh := LinearMap.mem_ker.mp hv
      simp only [dotForm_apply,v] at hh
      exact_mod_cast hh
    · intro h
      rw [hT,he]
      exact mem_shortSpan hm (abs_nonpos_iff.mpr (by dsimp only [v]; exact_mod_cast h))
  let U : Fin 1 → Fin n → ℤ := fun _ => p
  let F (y : PhaseTorus (Fin n)) := ∑ m ∈ P.modes, P.coeff m * torusMode m y
  have hidentity (y : Fin n → ℝ) :
      phaseAverage U F (torusCast y) =
        phasePolynomial (projectedModes P.modes (rowSpace T)) P.coeff y := by
    unfold F
    rw [phaseAverage_polynomial]
    simp only [phasePolynomial,projectedModes,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    have hh : (∀ k, ∑ i, m i * U k i = 0) ↔ (fun i => (m i : ℝ)) ∈ rowSpace T :=
      (show (∀ k, ∑ i, m i * U k i = 0) ↔ ∑ i, m i * p i = 0 from
        ⟨fun h => h 0,fun h _ => h⟩).trans (hexact m hm).symm
    simp only [hh,torusMode_cast]
  apply Or.inl
  intro x
  by_contra! h
  have hblocked (q : ℕ) (hq : q=1 ∨ q=2) :
      (phaseAverage U F (torusCast (fun i => (q:ℝ)*x i))).re ≤ P.eps := by
    have hc : Continuous F := continuous_finset_sum _ fun m _ =>
      continuous_const.mul (torusMode m).continuous
    let y : Fin n → ℝ := fun i => (q:ℝ)*x i
    have ht := (continuous_const : Continuous (fun _ : PhaseTorus (Fin 1) => torusCast y)).add
      (continuous_parameterMap U)
    have hi := (hc.comp ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      (μ := parameterMeasure (Fin 1))
    have heq : (∫ z, (F (torusCast y+parameterMap U z)).re ∂parameterMeasure (Fin 1)) =
        (phaseAverage U F (torusCast y)).re :=
      Complex.reCLM.integral_comp_comm hi
    change (phaseAverage U F (torusCast y)).re ≤ _
    rw [← heq]
    have hh := integral_mono (Complex.reCLM.integrable_comp hi) (integrable_const P.eps) (by
      intro z
      obtain ⟨t,ht⟩ := QuotientAddGroup.mk_surjective (z 0)
      have hz : parameterMap U z = torusCast (fun i => (p i:ℝ)*t) := by
        have hz' : z = torusCast (fun _ => t) := by
          funext i
          fin_cases i
          exact ht.symm
        rw [hz', parameterMap_cast]
        simp [U]
      change (F (torusCast y+parameterMap U z)).re ≤ P.eps
      rw [hz,← torusCast_add]
      simpa only [F,torusMode_cast,phasePolynomial,Pi.add_apply,y] using
        P.blocked (fun i => (q:ℝ)*x i+(p i:ℝ)*t) (h q hq t))
    simpa only [integral_const,probReal_univ,one_smul] using hh
  have h1 := hblocked 1 (Or.inl rfl)
  have h2 := hblocked 2 (Or.inr rfl)
  simp only [Nat.cast_one,one_mul,Nat.cast_ofNat,hidentity] at h1 h2
  linarith only [P.gap,h1,h2,hproj x]

/-- There are only finitely many positive primitive five-reading slopes
that can fail the two-dilation test. The cutoff is existential; the
sharper value 424200 requires additional quantitative input. -/
theorem harmonic_five_finite :
    ∃ B : ℤ, ∀ p : Fin 5 → ℤ, (∀ i, 0 < p i) →
      (∃ u : Fin 5 → ℤ, ∑ i, u i*p i = 1) →
      (∀ x : Fin 5 → ℝ, ∃ q : ℕ, (q=1 ∨ q=2) ∧ ∃ t : ℝ,
        ∀ i, (1/8:ℝ) < distInt ((q:ℝ)*x i+(p i:ℝ)*t)) ∨ (∀ j, p j ≤ B) := by
  classical
  obtain ⟨S,hS⟩ := harmonic_clear_or_exact_rows 5
  let R : ℝ := 1 + ∑ m ∈ S, ∑ i : Fin 5, (m i : ℝ)^2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨⌈R^2⌉,fun p hp hprim => ?_⟩
  rcases hS p hp with h | ⟨rows,hr,he,hli⟩
  · exact Or.inl h
  have hker : evaluate rows (fun i => (p i:ℝ)) = 0 := by
    ext i
    rw [evaluate_apply,Pi.zero_apply]
    exact_mod_cast he i
  have hrank : Module.finrank ℝ (LinearMap.range (evaluate rows)) = 4 := by
    change (Matrix.rank (fun j i => (rows j i : ℝ) : Matrix (Fin 4) (Fin 5) ℝ)) = 4
    rw [Matrix.rank_eq_finrank_span_row]
    change Module.finrank ℝ (Submodule.span ℝ (range (fun j i => (rows j i : ℝ)))) = 4
    rw [finrank_span_eq_card hli,Fintype.card_fin]
  have hb (i : Fin 4) : ∑ j, (rows i j : ℝ)^2 ≤ R := by
    have h := Finset.single_le_sum (f := fun m => ∑ j, (m j:ℝ)^2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (hr i)
    dsimp [R]
    linarith
  have h := harmonic_square_bound_of_four_rows rows p hp hprim hker hrank (fun _ => R) hb
  refine Or.inr (fun j => ?_)
  have hj := h j
  simp only [Finset.prod_const, Finset.card_univ,Fintype.card_fin] at hj
  have hle : (p j : ℝ) ≤ R^2 := by
    by_contra! hg
    have hs := pow_lt_pow_left₀ hg (sq_nonneg R) (by decide : 2 ≠ 0)
    nlinarith only [hs,hj]
  exact_mod_cast (hle.trans (Int.le_ceil (R^2)))

#print axioms harmonic_clear_or_exact_rows
#print axioms harmonic_five_finite

end Fresh.FiniteRelations
