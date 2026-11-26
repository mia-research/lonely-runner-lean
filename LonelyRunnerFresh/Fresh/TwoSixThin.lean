import Fresh.TwoSixNine

/-!
Rules: 1–4, 8–18. Thin six-packet all-subject assembly. Exact original
cascade/named-opening controls preceded this assembly: two_six_thin_v1.py.
Upper six subjects REUSE complete native S2; only low packet conditions
are imposed. [PROVISIONAL: counting tool; covering] inherited selectors.
-/
namespace Fresh.TwoSixThin
open Fresh Fresh.OneMover Fresh.Localisation Fresh.UnequalAPArrangement
open Fresh.TwoSixNine

theorem two_six_low_thin {x b : ℝ} (hb : 0<b) (hx : 4≤3*x)
    (hpoly : 40*b≤x*(6-5*b)) :
    ∃T : ℝ, 0<T ∧ (1/8 : ℝ)≤distInt T ∧
      ∀j : ℕ, j≤5 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  have hxpos : 0<x := by linarith
  let C : Finset ℝ := (Finset.range 6).image (fun j : ℕ=>x+(j : ℝ)*b)
  have hC : ∀d∈C, x≤d ∧ d≤x+5*b := by
    intro d hd
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
    have hj0 : (0 : ℝ)≤j := Nat.cast_nonneg _
    have hj5 : (j : ℝ)≤5 := by exact_mod_cast (show j≤5 by have := Finset.mem_range.mp hj; omega)
    constructor <;> nlinarith
  have hdev : (5*b)*(1/(8*1)+1/x)≤(3/4 : ℝ) := by
    have he : (5*b)*(1/(8*1)+1/x)=(5*b*x+40*b)/(8*x) := by
      field_simp
      ring
    rw [he]
    apply (div_le_iff₀ (by positivity : 0<8*x)).mpr
    nlinarith
  obtain ⟨ht,hcore,hpacket⟩ := Fresh.OpeningClump.single_slow_opening (s:=(1 : ℝ))
    (by norm_num) hxpos (by positivity : 0≤5*b) hC (by nlinarith) hdev
  refine ⟨_,ht,?_,fun j hj=>?_⟩
  · simpa only [one_mul] using hcore
  · exact hpacket _ (Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr (by omega),rfl⟩)

theorem two_six_thin_all_subjects (c A b : ℝ) (hb : 0<b)
    (hsep : 4≤3*(A-1)) (hpoly : 40*b≤(A-1)*(6-5*b)) :
    ∀k : Fin 8, Isolation (speeds c A 1 b 2) k := by
  have hgap : 0<A-1 := by linarith
  have hbwidth : 0<6-5*b := by nlinarith
  intro k
  by_cases hkp : (k : ℕ)<2
  · let x : ℝ := A-((k : ℕ) : ℝ)
    have hkR : ((k : ℕ) : ℝ)≤1 := by exact_mod_cast (show (k : ℕ)≤1 by omega)
    have hxg : A-1≤x := by dsimp [x]; linarith
    have hxs : 4≤3*x := by linarith
    have hxp : 40*b≤x*(6-5*b) := by nlinarith
    obtain ⟨T,hT,hcore,hpacket⟩ := two_six_low_thin hb hxs hxp
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

/-- Closed polynomial original-gap strip, physical signed scale and labels. -/
-- STANDING: DEFINITION
def TwoSixThinClass (V : Fin 8→ℝ) : Prop :=
  (∀i,0<V i) ∧ Function.Injective V ∧
  ∃ (c A b B s : ℝ) (σ : Equiv.Perm (Fin 8)),
    0<b ∧ 4≤3*(A-1) ∧ 40*b≤(A-1)*(6-5*b) ∧ s≠0 ∧
    V=(fun i=>B+s*speeds c A 1 b 2 (σ i))

theorem twoSixThin_isolation {V : Fin 8→ℝ} (h : TwoSixThinClass V)
    (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,A,b,B,s,σ,hb,hsep,hpoly,hs,hV⟩ := h
  rw [hV]
  have hi := subject_isolation_affine B s hs (two_six_thin_all_subjects c A b hb hsep hpoly (σ k))
  exact (Fresh.isolation_comp_perm _ σ k).2 hi

#print axioms two_six_low_thin
#print axioms two_six_thin_all_subjects
#print axioms twoSixThin_isolation
end Fresh.TwoSixThin
