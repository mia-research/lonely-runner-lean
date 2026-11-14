import Fresh.CircuitProjection
import Fresh.SmallCircuits

namespace Fresh.FiniteRelations

open scoped BigOperators
open Set

private theorem integer_direction {ι : Type*} [Fintype ι] (u : ι → ℚ) :
    ∃ (D : ℝ) (p : ι → ℤ), 0 < D ∧ ∀ i, (p i : ℝ) = D*(u i : ℝ) := by
  classical
  let N := ∏ i, (u i).den
  have hN : 0 < N := Finset.prod_pos fun i _ => (u i).pos
  have hd (i : ι) : (u i).den ∣ N :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  choose a ha using hd
  refine ⟨(N:ℝ),fun i => (a i : ℤ)*(u i).num,by exact_mod_cast hN,fun i => ?_⟩
  have h := ha i
  push_cast
  rw [Rat.cast_def, h]
  push_cast
  have hn : (0:ℝ) < (u i).den := by exact_mod_cast (u i).pos
  field_simp

private theorem continuous_distInt : Continuous distInt := by
  have h := (AddCircle.continuous_mk' (1:ℝ)).norm
  convert h using 1
  funext x
  exact UnitAddCircle.norm_eq.symm

private theorem rational_move {ι : Type*} [Fintype ι] (x : ι → ℝ) (u : ι → ℚ) (c : ℝ)
    (h : ∃ t : ℝ, ∀ i, c < distInt (x i+t*(u i : ℝ))) :
    ∃ q : ℚ, ∀ i, c < distInt (x i+(q:ℝ)*(u i : ℝ)) := by
  obtain ⟨t,ht⟩ := h
  let U : Set ℝ := ⋂ i, {t : ℝ | c < distInt (x i+t*(u i : ℝ))}
  have ho : IsOpen U := isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (continuous_distInt.comp (by fun_prop))
  obtain ⟨q,hq⟩ := (Rat.denseRange_cast (𝕜 := ℝ)).exists_mem_open ho
    ⟨t,mem_iInter.mpr ht⟩
  exact ⟨q,mem_iInter.mp hq⟩

private theorem small_rational_circle {ι : Type*} [Fintype ι] (hcard : Fintype.card ι ≤ 3)
    (u : ι → ℚ) (hu : ∀ i, u i ≠ 0) (x : ι → ℝ) :
    ∃ t : ℚ, ∀ i, (1/7:ℝ) < distInt (x i+(t:ℝ)*(u i : ℝ)) := by
  obtain ⟨D,p,hD,hp⟩ := integer_direction u
  have hn (i : ι) : p i ≠ 0 := by
    intro he
    have hh := hp i
    rw [he,Int.cast_zero] at hh
    exact (mul_ne_zero hD.ne' (by exact_mod_cast hu i)) hh.symm
  obtain ⟨t,ht⟩ := small_circle_phase hcard p hn x
  apply rational_move
  refine ⟨D*t,fun i => ?_⟩
  have hh := ht i
  rw [hp i] at hh
  convert hh using 2
  ring

/-- The only circle statement needed beyond three coordinates. -/
def FourCircleClear (c : ℝ) : Prop :=
  ∀ p : Fin 4 → ℤ, (∀ i, p i ≠ 0) → ∀ x : Fin 4 → ℝ,
    ∃ q : ℕ, (q = 1 ∨ q = 2) ∧ ∃ t : ℝ,
      ∀ i, c < distInt ((q:ℝ)*x i+(p i : ℝ)*t)

/-- Rank at most three reduces to supported circles. At rank at most
two the result needs no four-coordinate hypothesis. -/
theorem low_rank_rational_fibre {ι : Type*} [Fintype ι]
    (V : Submodule ℚ (ι → ℚ)) {rank : ℕ} (hrank : rank ≤ 3)
    (hdim : Fintype.card ι ≤ Module.finrank ℚ V+rank)
    (hmoves : ∀ i, ∃ u : V, (u : ι → ℚ) i ≠ 0)
    {c : ℝ} (hc : c < 1/7) (hfour : rank = 3 → FourCircleClear c)
    (x : ι → ℝ) :
    ∃ q : ℕ, (q = 1 ∨ q = 2) ∧ ∃ w : V,
      ∀ i, c < distInt ((q:ℝ)*x i+((w : ι → ℚ) i : ℝ)) := by
  classical
  by_cases hι : IsEmpty ι
  · exact ⟨1,Or.inl rfl,0,fun i => (hι.false i).elim⟩
  have hV : V ≠ ⊥ := by
    intro h
    obtain ⟨i⟩ := not_isEmpty_iff.mp hι
    obtain ⟨u,hu⟩ := hmoves i
    have he : (u : ι → ℚ) = 0 := by simpa [h] using u.property
    exact hu (congrFun he i)
  obtain ⟨u,hu,hmin⟩ := exists_circuit V hV
  let s := coordSupport (u : ι → ℚ)
  let P := restrictOutside V s
  obtain ⟨_,hP,hsize⟩ := circuit_projection V u hu hmin
  change Module.finrank ℚ P.range+1 = Module.finrank ℚ V at hP
  change s.card + Module.finrank ℚ V ≤ Fintype.card ι+1 at hsize
  have hspos : 0 < s.card := by
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hu
    exact Finset.card_pos.mpr ⟨i,(mem_coordSupport _ _).2 hi⟩
  have hs4 : s.card ≤ 4 := by omega
  have hout : Fintype.card (sᶜ : Finset ι) = Fintype.card ι-s.card := by
    rw [Fintype.card_coe,Finset.card_compl]
  have hsz := Finset.card_le_univ s
  have hsmall (i : ι) (hi : i ∉ s) : (u : ι → ℚ) i = 0 := by
    by_contra! h
    exact hi ((mem_coordSupport _ _).2 h)
  let us : s → ℚ := fun i => (u : ι → ℚ) i
  have hus (i : s) : us i ≠ 0 := (mem_coordSupport (u : ι → ℚ) i.val).1 i.property
  by_cases hs3 : s.card ≤ 3
  · have hdim' : Fintype.card (sᶜ : Finset ι) ≤ Module.finrank ℚ P.range+rank := by omega
    have hmov' (i : ↥(sᶜ)) : ∃ y : P.range, (y : ↥(sᶜ) → ℚ) i ≠ 0 := by
      obtain ⟨v,hv⟩ := hmoves i
      exact ⟨P.rangeRestrict v,hv⟩
    obtain ⟨q,hq,y,hy⟩ := low_rank_rational_fibre P.range hrank hdim' hmov' hc hfour
      (fun i => x i)
    obtain ⟨w,hw⟩ := y.property
    obtain ⟨t,ht⟩ := small_rational_circle (by simpa using hs3 : Fintype.card s ≤ 3)
      us hus (fun i => (q:ℝ)*x i+((w : ι → ℚ) i : ℝ))
    refine ⟨q,hq,w+t • u,fun i => ?_⟩
    by_cases hi : i ∈ s
    · have hh := ht ⟨i,hi⟩
      change c < distInt ((q:ℝ)*x i+(((w : ι → ℚ) i+t*(u : ι → ℚ) i : ℚ) : ℝ))
      push_cast
      rw [← add_assoc]
      exact hc.trans hh
    · have hh := hy ⟨i,Finset.mem_compl.mpr hi⟩
      change c < distInt ((q:ℝ)*x i+(((w : ι → ℚ) i+t*(u : ι → ℚ) i : ℚ) : ℝ))
      rw [hsmall i hi,mul_zero,add_zero]
      rw [← hw] at hh
      exact hh
  · have hsEq : s.card = 4 := by omega
    have hrEq : rank = 3 := by omega
    have hsurj : Function.Surjective P := by
      apply LinearMap.range_eq_top.mp
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fintype_fun_eq_card]
      omega
    have near (i : ↥(sᶜ)) : ∃ a : ℚ, (1/3-1/100:ℝ) < x i+(a:ℝ) ∧
        x i+(a:ℝ) < 1/3+1/100 := by
      obtain ⟨a,hl,hh⟩ := exists_rat_btwn (show (1/3-1/100:ℝ)-x i <
        (1/3+1/100:ℝ)-x i by linarith)
      exact ⟨a,by linarith,by linarith⟩
    choose z hz using near
    obtain ⟨w,hw⟩ := hsurj z
    obtain ⟨D,p,hD,hp⟩ := integer_direction us
    let e : s ≃ Fin 4 := Fintype.equivFinOfCardEq (by simpa using hsEq)
    have hpn (i : Fin 4) : p (e.symm i) ≠ 0 := by
      intro he
      have hh := hp (e.symm i)
      rw [he,Int.cast_zero] at hh
      exact (mul_ne_zero hD.ne' (by exact_mod_cast hus (e.symm i))) hh.symm
    obtain ⟨q,hq,t,ht⟩ := hfour hrEq (p ∘ e.symm) hpn
      (fun i => x (e.symm i) + ((w : ι → ℚ) (e.symm i) : ℝ))
    have hm : ∃ t' : ℝ, ∀ i : s, c < distInt ((q:ℝ)*(x i+((w : ι → ℚ) i : ℝ))+
        t'*(us i : ℝ)) := by
      refine ⟨D*t,fun i => ?_⟩
      have hh := ht (e i)
      simp only [Function.comp_apply,Equiv.symm_apply_apply,hp] at hh
      convert hh using 2
      ring
    obtain ⟨t',ht'⟩ := rational_move _ us c hm
    refine ⟨q,hq,(q:ℚ) • w+t' • u,fun i => ?_⟩
    change c < distInt ((q:ℝ)*x i+((((q:ℚ)*(w : ι → ℚ) i+t'*(u : ι → ℚ) i):ℚ):ℝ))
    push_cast
    rw [show (q:ℝ)*x i+((q:ℝ)*((w : ι → ℚ) i : ℝ)+(t':ℝ)*((u : ι → ℚ) i : ℝ)) =
      (q:ℝ)*(x i+((w : ι → ℚ) i : ℝ))+(t':ℝ)*((u : ι → ℚ) i : ℝ) by ring]
    by_cases hi : i ∈ s
    · exact ht' ⟨i,hi⟩
    · rw [hsmall i hi,Rat.cast_zero,mul_zero,add_zero]
      have he : (w : ι → ℚ) i = z ⟨i,Finset.mem_compl.mpr hi⟩ :=
        congrFun hw ⟨i,Finset.mem_compl.mpr hi⟩
      rw [he]
      have hh := hz ⟨i,Finset.mem_compl.mpr hi⟩
      apply (show c < 1/4 by linarith).trans_le
      rcases hq with rfl | rfl <;> push_cast <;>
        exact clear_quarter (by linarith [hh.1]) (by linarith [hh.2])
termination_by Fintype.card ι
decreasing_by
  classical
  change Fintype.card (sᶜ : Finset ι) < Fintype.card ι
  omega

#print axioms low_rank_rational_fibre

end Fresh.FiniteRelations
