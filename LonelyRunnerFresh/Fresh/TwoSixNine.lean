import Fresh.TwoSixTight
import Fresh.TranslatedSixArrangement

/-!
Rules: 1–4, 8–18. Two-plus-six physical AP blocks at original gap9max.
The two outside subjects use the new packet-opening law. The six frozen
AP subjects REUSE native S2Complete with two arbitrary distinct movers;
no first AP-window fit or new frozen-role existence premise is imposed.
Exact cascade controls BEFORE this assembly: two_six_nine_v1.py.
[PROVISIONAL: counting tool; covering] inherited source boundary selectors.
-/
namespace Fresh.TwoSixNine
open Fresh Fresh.OneMover Fresh.Localisation Fresh.UnequalAPArrangement Fresh.TwoSixTight

/-- Six retained AP subjects, directly reusing the complete native S2 library. -/
theorem frozen_six {d a z : ℝ} (k : Fin 8) (hk0 : k≠0) (hk7 : k≠7)
    (ha : 0 < |a-(d+((k : ℕ) : ℝ))|)
    (hz : 0 < |z-(d+((k : ℕ) : ℝ))|) :
    Isolation (twoMover d a z 0 7) k := by
  fin_cases k
  · exact False.elim (hk0 rfl)
  · obtain ⟨T,hlo,hf,_⟩ := landing_twoMoverComplete_12345 d a z (1 : Fin 8) 0 7
      (by decide) (by decide) (by decide) (by decide) ha hz
    refine ⟨T,lt_of_lt_of_le (by positivity) hlo,?_⟩
    exact (Fresh.Cascade.isolatedAt_iff_lonelyAt _ _ _).2 hf.1
  · obtain ⟨T,hlo,hf,_⟩ := landing_twoMoverComplete_1234 d a z (2 : Fin 8) 0 7
      (by decide) (by decide) (by decide) (by decide) ha hz
    refine ⟨T,lt_of_lt_of_le (by positivity) hlo,?_⟩
    exact (Fresh.Cascade.isolatedAt_iff_lonelyAt _ _ _).2 hf.1
  · obtain ⟨T,hlo,hf,_⟩ := landing_twoMoverComplete_123 d a z (3 : Fin 8) 0 7
      (by decide) (by decide) (by decide) (by decide) ha hz
    refine ⟨T,lt_of_lt_of_le (by positivity) hlo,?_⟩
    exact (Fresh.Cascade.isolatedAt_iff_lonelyAt _ _ _).2 hf.1
  · obtain ⟨T,hlo,hf,_⟩ := landing_twoMoverComplete_123 d a z (4 : Fin 8) 0 7
      (by decide) (by decide) (by decide) (by decide) ha hz
    refine ⟨T,lt_of_lt_of_le (by positivity) hlo,?_⟩
    exact (Fresh.Cascade.isolatedAt_iff_lonelyAt _ _ _).2 hf.1
  · obtain ⟨T,hlo,hf,_⟩ := landing_twoMoverComplete_1234 d a z (5 : Fin 8) 0 7
      (by decide) (by decide) (by decide) (by decide) ha hz
    refine ⟨T,lt_of_lt_of_le (by positivity) hlo,?_⟩
    exact (Fresh.Cascade.isolatedAt_iff_lonelyAt _ _ _).2 hf.1
  · obtain ⟨T,hlo,hf,_⟩ := landing_twoMoverComplete_12345 d a z (6 : Fin 8) 0 7
      (by decide) (by decide) (by decide) (by decide) ha hz
    refine ⟨T,lt_of_lt_of_le (by positivity) hlo,?_⟩
    exact (Fresh.Cascade.isolatedAt_iff_lonelyAt _ _ _).2 hf.1
  · exact False.elim (hk7 rfl)

theorem two_six_nine_all_subjects (c A b : ℝ) (hb : 0<b)
    (hg : 9*max 1 b≤A-1) :
    ∀k : Fin 8, Isolation (speeds c A 1 b 2) k := by
  have hmax1 : (1 : ℝ)≤ max 1 b := le_max_left _ _
  have hgap : 0<A-1 := by nlinarith
  intro k
  by_cases hkp : (k : ℕ)<2
  · let x : ℝ := A-((k : ℕ) : ℝ)
    have hkR : ((k : ℕ) : ℝ)≤1 := by exact_mod_cast (show (k : ℕ)≤1 by omega)
    have hxg : A-1≤x := by dsimp [x]; linarith
    have hx9 : 9*max 1 b≤x := by linarith
    obtain ⟨T,hT,hcore,hpacket⟩ := two_six_low_tight hb hx9
    refine ⟨T,hT,fun i hik=>?_⟩
    by_cases hip : (i : ℕ)<2
    · let n := (((i : ℕ) : ℤ)-((k : ℕ) : ℤ)).natAbs
      have hn : n=1 := by dsimp [n]; have := Fin.val_ne_of_ne hik; omega
      have hd : speeds c A 1 b 2 i-speeds c A 1 b 2 k = ((i : ℕ) : ℝ)-((k : ℕ) : ℝ) := by simp [speeds,hip,hkp]
      have he : |speeds c A 1 b 2 i-speeds c A 1 b 2 k|=(n : ℝ) := by
        rw [hd,←natAbs_cast_abs i k]
      rw [←Fresh.Localisation.distInt_abs_mul,he,hn]
      simpa only [Nat.cast_one,one_mul] using hcore
    · have hj : (i : ℕ)-2≤5 := by have := i.isLt; omega
      have hd : speeds c A 1 b 2 i-speeds c A 1 b 2 k = x+(((i : ℕ)-2 : ℕ) : ℝ)*b := by simp [speeds,hip,hkp,x]; ring
      rw [hd]
      exact hpacket _ hj
  · let d : ℝ := (c+A-b)/b
    let w : Fin 8→ℝ := twoMover d (c/b) ((c+1)/b) 0 7
    let σ := Fresh.TranslatedSixArrangement.displayPerm
    have hk2 : 2≤(k : ℕ) := by omega
    have hσ : (σ k : ℕ)=(k : ℕ)-1 := by
      fin_cases k <;> norm_num [σ,Fresh.TranslatedSixArrangement.displayPerm] at *
    have hσ0 : σ k≠0 := by intro h; have hh:=congrArg Fin.val h; simp [hσ] at hh; omega
    have hσ7 : σ k≠7 := by intro h; have hh:=congrArg Fin.val h; simp [hσ] at hh; have :=k.isLt; omega
    have hkR : (1 : ℝ)≤((σ k : ℕ) : ℝ) := by
      exact_mod_cast (show 1≤(σ k : ℕ) by omega)
    have ha : 0 < |c/b-(d+((σ k : ℕ) : ℝ))| := by
      apply abs_pos.mpr
      have hn : 0<A-b+b*((σ k : ℕ) : ℝ) := by nlinarith
      dsimp [d]
      intro he
      have hh := (div_eq_iff hb.ne').mp (show (c-(c+A-b))/b=((σ k : ℕ) : ℝ) by rw [sub_div]; linarith)
      nlinarith
    have hz : 0 < |(c+1)/b-(d+((σ k : ℕ) : ℝ))| := by
      apply abs_pos.mpr
      have hn : 0<A-1-b+b*((σ k : ℕ) : ℝ) := by nlinarith
      dsimp [d]
      intro he
      have hh := (div_eq_iff hb.ne').mp (show ((c+1)-(c+A-b))/b=((σ k : ℕ) : ℝ) by rw [sub_div]; linarith)
      nlinarith
    have hi : Isolation w (σ k) := frozen_six (σ k) hσ0 hσ7 ha hz
    have hs := Fresh.OneMover.subject_isolation_affine 0 b hb.ne' hi
    have hr := (Fresh.isolation_comp_perm _ σ k).2 hs
    have he : speeds c A 1 b 2=(fun i=>0+b*w (σ i)) := by
      funext i
      fin_cases i <;> norm_num only [speeds,Fin.val_zero,Fin.val_one,Fin.val_ofNat,show (0 : ℕ)<2 by omega,show (1 : ℕ)<2 by omega,ite_true,ite_false,Nat.reduceLT,Nat.reduceSub,Nat.cast_zero,Nat.cast_one,one_mul,zero_mul,add_zero]
      · change _=0+b*(c/b)
        field_simp
        ring
      · change _=0+b*((c+1)/b)
        field_simp
        ring
      · change _=0+b*((c+A-b)/b+((1 : ℕ) : ℝ))
        field_simp
        ring
      · change _=0+b*((c+A-b)/b+(2 : ℝ))
        field_simp
        ring
      · change _=0+b*((c+A-b)/b+(3 : ℝ))
        field_simp
        ring
      · change _=0+b*((c+A-b)/b+(4 : ℝ))
        field_simp
        ring
      · change _=0+b*((c+A-b)/b+(5 : ℝ))
        field_simp
        ring
      · change _=0+b*((c+A-b)/b+(6 : ℝ))
        field_simp
        ring
    rw [he]
    exact hr

/-- Physical positive distinct arrangements, with signed affine scale,
physical mirror and arbitrary labels. In unnormalised steps u,v>0 the
original gap condition is9max(u,v). -/
-- STANDING: DEFINITION
def TwoSixNineClass (V : Fin 8→ℝ) : Prop :=
  (∀i,0<V i) ∧ Function.Injective V ∧
  ∃ (c A b B s : ℝ) (σ : Equiv.Perm (Fin 8)),
    0<b ∧ 9*max 1 b≤A-1 ∧ s≠0 ∧
    V=(fun i=>B+s*speeds c A 1 b 2 (σ i))

theorem twoSixNine_isolation {V : Fin 8→ℝ} (h : TwoSixNineClass V)
    (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,A,b,B,s,σ,hb,hg,hs,hV⟩ := h
  rw [hV]
  have hi := subject_isolation_affine B s hs (two_six_nine_all_subjects c A b hb hg (σ k))
  exact (Fresh.isolation_comp_perm _ σ k).2 hi

#print axioms frozen_six
#print axioms two_six_nine_all_subjects
#print axioms twoSixNine_isolation
end Fresh.TwoSixNine
