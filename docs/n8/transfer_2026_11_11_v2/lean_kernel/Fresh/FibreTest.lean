import Fresh.RationalAnnihilator
import Fresh.TorusAverage

namespace Fresh.FiniteRelations

open Set MeasureTheory
open scoped BigOperators

noncomputable section

/-- Integer parameters suffice even when the witnesses are rational. -/
theorem integer_parameters_basis {n : ℕ} (V : Submodule ℚ (Fin n → ℚ)) :
    ∃ (d : ℕ) (U : Fin d → Fin n → ℤ),
      (∀ j, (fun i => (U j i : ℚ)) ∈ V) ∧
      (∀ w ∈ V, ∃ c : Fin d → ℚ, ∀ i, ∑ j, c j * (U j i : ℚ) = w i) ∧
      (∀ m : Fin n → ℤ, (∀ j, ∑ i, m i * U j i = 0) ↔
        ∀ w ∈ V, ∑ i, (m i : ℚ)*w i = 0) := by
  classical
  let d := Module.finrank ℚ V
  let b : Module.Basis (Fin d) ℚ V := Module.finBasis ℚ V
  let u (j : Fin d) : Fin n → ℚ := b j
  let N (j : Fin d) : ℕ := ∏ i, (u j i).den
  have hp (j : Fin d) : 0 < N j := Finset.prod_pos fun i _ => (u j i).pos
  have hd (j : Fin d) (i : Fin n) : (u j i).den ∣ N j :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  choose a ha using hd
  let U (j : Fin d) (i : Fin n) : ℤ := (a j i : ℤ)*(u j i).num
  have hU (j : Fin d) (i : Fin n) : (U j i : ℚ) = (N j : ℚ)*(u j i) := by
    have hh := ha j i
    unfold U
    push_cast
    conv_rhs => rw [← Rat.num_div_den (u j i)]
    rw [hh]
    push_cast
    have hn : (0:ℚ) < (u j i).den := by exact_mod_cast (u j i).pos
    field_simp
  have hrepr (w : V) (i : Fin n) : ∑ j, b.repr w j * u j i = (w : Fin n → ℚ) i := by
    calc
      _ = ((↑(∑ j, b.repr w j • b j) : Fin n → ℚ) i) := by
        rw [Submodule.coe_sum,Finset.sum_apply]
        rfl
      _ = _ := congrArg (fun z : V => (z : Fin n → ℚ) i) (b.sum_repr w)
  refine ⟨d,U,?_,?_,fun m => ?_⟩
  · intro j
    have hh : (fun i => (U j i : ℚ)) = (N j : ℚ) • u j := funext (hU j)
    rw [hh]
    exact V.smul_mem _ (b j).property
  · intro w hw
    refine ⟨fun j => b.repr ⟨w,hw⟩ j / (N j : ℚ),fun i => ?_⟩
    have hr : (∑ j, b.repr ⟨w,hw⟩ j * u j i) = w i := hrepr ⟨w,hw⟩ i
    rw [← hr]
    apply Finset.sum_congr rfl
    intro j _
    rw [hU]
    have hn : (N j : ℚ) ≠ 0 := by exact_mod_cast (hp j).ne'
    field_simp
  · have he (j : Fin d) :
        (∑ i, m i * U j i = 0) ↔ (∑ i, (m i : ℚ) * u j i = 0) := by
      have hh : ((∑ i, m i * U j i : ℤ) : ℚ) =
          (N j : ℚ) * ∑ i, (m i : ℚ) * u j i := by
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hU]
        ring
      have hn : (N j : ℚ) ≠ 0 := by exact_mod_cast (hp j).ne'
      constructor
      · intro h
        rw [h,Int.cast_zero] at hh
        exact (mul_eq_zero.mp hh.symm).resolve_left hn
      · intro h
        rw [h,mul_zero] at hh
        exact_mod_cast hh
    constructor
    · intro h w hw
      let z : V := ⟨w,hw⟩
      change ∑ i, (m i : ℚ) * ((z : Fin n → ℚ) i) = 0
      simp_rw [← hrepr z]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro j _
      have h0 := (he j).mp (h j)
      calc
        ∑ i, (m i : ℚ) * (b.repr z j * u j i) =
            b.repr z j * ∑ i, (m i : ℚ) * u j i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = 0 := by rw [h0,mul_zero]
    · intro h j
      exact (he j).mpr (h (u j) (b j).property)

/-- Integer parameters cover the torus image of every rational vector in the submodule. -/
theorem integer_parameters {n : ℕ} (V : Submodule ℚ (Fin n → ℚ)) :
    ∃ (d : ℕ) (U : Fin d → Fin n → ℤ),
      (∀ w ∈ V, ∃ z, parameterMap U z = torusCast (fun i => (w i : ℝ))) ∧
      (∀ m : Fin n → ℤ, (∀ j, ∑ i, m i * U j i = 0) ↔
        ∀ w ∈ V, ∑ i, (m i : ℚ)*w i = 0) := by
  obtain ⟨d,U,_,hrep,hann⟩ := integer_parameters_basis V
  refine ⟨d,U,?_,hann⟩
  intro w hw
  obtain ⟨c,hc⟩ := hrep w hw
  refine ⟨torusCast (fun j => (c j : ℝ)),?_⟩
  rw [parameterMap_cast]
  congr 1
  funext i
  simpa only [mul_comm] using (show ∑ j, (c j : ℝ) * (U j i : ℝ) = (w i : ℝ) by
    exact_mod_cast hc i)

def phaseBump (n : ℕ) (x : PhaseTorus (Fin n)) : ℝ :=
  ∏ i, max 0 (‖x i‖ - 1/8)

theorem phaseBump_continuous (n : ℕ) : Continuous (phaseBump n) := by
  unfold phaseBump
  fun_prop

theorem phaseBump_nonneg {n : ℕ} (x : PhaseTorus (Fin n)) : 0 ≤ phaseBump n x :=
  Finset.prod_nonneg fun _ _ => le_max_left _ _

theorem phaseBump_blocked {n : ℕ} (x : Fin n → ℝ)
    (h : ∃ i, distInt (x i) ≤ 1/8) : phaseBump n (torusCast x) = 0 := by
  obtain ⟨i,hi⟩ := h
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [torusCast,UnitAddCircle.norm_eq]
  exact max_eq_left (sub_nonpos.mpr hi)

theorem phaseBump_clear {n : ℕ} (x : Fin n → ℝ)
    (h : ∀ i, (1/8:ℝ) < distInt (x i)) : 0 < phaseBump n (torusCast x) := by
  apply Finset.prod_pos
  intro i _
  rw [torusCast,UnitAddCircle.norm_eq]
  exact (sub_pos.mpr (h i)).trans_le (le_max_right _ _)

def AdmissibleRows {n : ℕ} (T : Finset (Fin n → ℤ)) : Prop :=
  Module.finrank ℝ (rowSpace T) ≤ 3 ∧
    ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧ ∀ z ∈ rowSpace T, ∑ i, z i * w i = 0

theorem positive_paired_average {n : ℕ} (T : Finset (Fin n → ℤ)) (hT : AdmissibleRows T) :
    ∃ (d : ℕ) (U : Fin d → Fin n → ℤ) (μ : ℝ), 0 < μ ∧
      (∀ m : Fin n → ℤ, (∀ j, ∑ i, m i * U j i = 0) ↔
        (fun i => (m i : ℝ)) ∈ rowSpace T) ∧
      ∀ x, μ ≤ phaseAverage U (phaseBump n) x + phaseAverage U (phaseBump n) (2 • x) := by
  let V := rationalKernel T
  obtain ⟨d,U,hU,hrows⟩ := integer_parameters V
  have hd : Fintype.card (Fin n) ≤ Module.finrank ℚ V+3 := by
    rw [Fintype.card_fin]
    exact (rationalKernel_codim_le T).trans (Nat.add_le_add_left hT.1 _)
  let g (x : PhaseTorus (Fin n)) := phaseAverage U (phaseBump n) x +
    phaseAverage U (phaseBump n) (2 • x)
  have hg : Continuous g := (phaseAverage_continuous U (phaseBump_continuous n)).add
    ((phaseAverage_continuous U (phaseBump_continuous n)).comp (continuous_id.const_smul (2:ℕ)))
  have hpos (x : PhaseTorus (Fin n)) : 0 < g x := by
    choose y hy using fun i => QuotientAddGroup.mk_surjective (x i)
    have hx : torusCast y = x := funext hy
    obtain ⟨q,hq,w,hw⟩ := rank_three_fibre_clear V hd (rationalKernel_moves T hT.2) y
    obtain ⟨z,hz⟩ := hU w w.property
    have hp := phaseBump_clear _ hw
    have ht : torusCast (fun i => (q:ℝ)*y i+((w : Fin n → ℚ) i:ℝ)) =
        torusCast (fun i => (q:ℝ)*y i) + parameterMap U z := by
      rw [hz,← torusCast_add]
      rfl
    rw [ht] at hp
    have h1 := phaseAverage_nonneg U phaseBump_nonneg x
    have h2 := phaseAverage_nonneg U phaseBump_nonneg (2 • x)
    rcases hq with rfl | rfl
    · simp only [Nat.cast_one,one_mul,hx] at hp
      exact add_pos_of_pos_of_nonneg (phaseAverage_pos U (phaseBump_continuous n) phaseBump_nonneg x z hp) h2
    · simp only [Nat.cast_ofNat,torusCast_two,hx] at hp
      exact add_pos_of_nonneg_of_pos h1 (phaseAverage_pos U (phaseBump_continuous n) phaseBump_nonneg _ z hp)
  obtain ⟨y,_,hy⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hg.continuousOn
  refine ⟨d,U,g y,hpos y,fun m => (hrows m).trans (mem_rowSpace_iff T m).symm,fun x => ?_⟩
  exact hy (Set.mem_univ x)

#print axioms integer_parameters
#print axioms positive_paired_average

end
end Fresh.FiniteRelations
