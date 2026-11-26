import Fresh.APCoreOpening
import Fresh.TwoMoverSubjectTransport

/-!
Rules: 1–4, 8–18. Physical all-subject assembly for two separated AP blocks
with independent positive real steps, total eight runners. Uniform original
gap/width inequalities derive each subject's retained AP-core opening;
no clearance at an unspecified future output is assumed.
[PROVISIONAL: counting tool] inherited from the named boundary-opening selector.
-/
open Classical
namespace Fresh.UnequalAPArrangement
open Fresh Fresh.OneMover Fresh.APCoreOpening

noncomputable def speeds (c A u v : ℝ) (p : ℕ) (i : Fin 8) : ℝ :=
  if (i : ℕ)<p then c+u*(i : ℕ) else c+A+v*((i : ℕ)-p : ℕ)

theorem unequal_two_block_all (c A u v : ℝ) (p : ℕ) (hp2 : 2 ≤ p) (hp6 : p ≤ 6)
    (hu : 0<u) (hv : 0<v) (hg : 0<A-((p : ℝ)-1)*u)
    (hsepL : 8*((p : ℝ)-1)*u ≤ (A-((p : ℝ)-1)*u)*(8-(p : ℝ)))
    (hsepR : 8*(7-(p : ℝ))*v ≤ (A-((p : ℝ)-1)*u)*(p : ℝ))
    (hwL : (7-(p : ℝ))*v*(1/(8*u)+1/(A-((p : ℝ)-1)*u)) ≤ 3/4)
    (hwR : ((p : ℝ)-1)*u*(1/(8*v)+1/(A-((p : ℝ)-1)*u)) ≤ 3/4) :
    ∀ k : Fin 8, Isolation (speeds c A u v p) k := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hpR6 : (p : ℝ) ≤ 6 := by exact_mod_cast hp6
  have hcastL : ((p-1 : ℕ) : ℝ)=(p : ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ p)]; norm_num
  have hcastR : ((7-p : ℕ) : ℝ)=7-(p : ℝ) := by rw [Nat.cast_sub (by omega : p ≤ 7)]; norm_num
  intro k
  by_cases hkp : (k : ℕ)<p
  · let x := A-((k : ℕ) : ℝ)*u
    let w := (7-(p : ℝ))*v
    let C := (Finset.range (8-p)).image (fun j : ℕ => x+(j : ℝ)*v)
    have hkR : ((k : ℕ) : ℝ) ≤ (p : ℝ)-1 := by
      have hh : ((k : ℕ) : ℝ)+1 ≤ p := by exact_mod_cast (show (k : ℕ)+1 ≤ p by omega)
      linarith
    have hxg : A-((p : ℝ)-1)*u ≤ x := by dsimp [x]; nlinarith
    have hx : 0<x := hg.trans_le hxg
    have hw : 0≤w := by dsimp [w]; apply mul_nonneg (by linarith) (le_of_lt hv)
    have hC : ∀ d∈C, x≤d ∧ d≤x+w := by
      intro d hd
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
      have hjR : (j : ℝ) ≤ 7-(p : ℝ) := by
        have hh : j+p ≤ 7 := by have := Finset.mem_range.mp hj; omega
        have hhR : (j : ℝ)+(p : ℝ) ≤ 7 := by exact_mod_cast hh
        linarith
      have hj0 := Nat.cast_nonneg (α := ℝ) j
      dsimp [w]
      constructor <;> nlinarith
    have hsep : 8*((p-1 : ℕ) : ℝ)*u ≤ x*(7-((p-1 : ℕ) : ℝ)) := by
      rw [hcastL]
      nlinarith
    have hwidth : w*(1/(8*u)+1/x) ≤ 3/4 := by
      have hi := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hg hxg
      have hm := mul_le_mul_of_nonneg_left (add_le_add_left hi (1/(8*u))) hw
      dsimp [w] at hm ⊢
      linarith
    obtain ⟨ht,hcore,hpacket⟩ := ap_core_clump_opening (p-1) (by omega) (by omega) hu hx hw hC hsep hwidth
    refine ⟨_,ht,fun i hik => ?_⟩
    by_cases hip : (i : ℕ)<p
    · let n := (((i : ℕ) : ℤ)-((k : ℕ) : ℤ)).natAbs
      have hn1 : 1 ≤ n := by dsimp [n]; have := Fin.val_ne_of_ne hik; omega
      have hnle : n ≤ p-1 := by dsimp [n]; omega
      have hd : speeds c A u v p i-speeds c A u v p k = (((i : ℕ) : ℝ)-((k : ℕ) : ℝ))*u := by simp [speeds,hip,hkp]; ring
      have he : |speeds c A u v p i-speeds c A u v p k|=(n : ℝ)*u := by
        rw [hd,abs_mul,abs_of_pos hu,← natAbs_cast_abs i k]
      rw [← Fresh.Localisation.distInt_abs_mul,he]
      exact hcore n hn1 hnle
    · have hj : (i : ℕ)-p<8-p := by have := i.isLt; omega
      have hm : x+(((i : ℕ)-p : ℕ) : ℝ)*v ∈ C :=
        Finset.mem_image.mpr ⟨(i : ℕ)-p,Finset.mem_range.mpr hj,rfl⟩
      have hd : speeds c A u v p i-speeds c A u v p k = x+(((i : ℕ)-p : ℕ) : ℝ)*v := by simp [speeds,hip,hkp,x]; ring
      rw [hd]
      exact hpacket _ hm
  · let x := A-((p : ℝ)-1)*u+(((k : ℕ)-p : ℕ) : ℝ)*v
    let w := ((p : ℝ)-1)*u
    let C := (Finset.range p).image (fun j : ℕ => x+(j : ℝ)*u)
    have hk0 := Nat.cast_nonneg (α := ℝ) ((k : ℕ)-p)
    have hxg : A-((p : ℝ)-1)*u ≤ x := by dsimp [x]; nlinarith
    have hx : 0<x := hg.trans_le hxg
    have hw : 0≤w := by dsimp [w]; apply mul_nonneg (by linarith) (le_of_lt hu)
    have hC : ∀ d∈C, x≤d ∧ d≤x+w := by
      intro d hd
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
      have hjR : (j : ℝ) ≤ (p : ℝ)-1 := by
        have hh : (j : ℝ)+1 ≤ p := by exact_mod_cast (show j+1 ≤ p by have := Finset.mem_range.mp hj; omega)
        linarith
      have hj0 := Nat.cast_nonneg (α := ℝ) j
      dsimp [w]
      constructor <;> nlinarith
    have hsep : 8*((7-p : ℕ) : ℝ)*v ≤ x*(7-((7-p : ℕ) : ℝ)) := by
      rw [hcastR]
      nlinarith
    have hwidth : w*(1/(8*v)+1/x) ≤ 3/4 := by
      have hi := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hg hxg
      have hm := mul_le_mul_of_nonneg_left (add_le_add_left hi (1/(8*v))) hw
      dsimp [w] at hm ⊢
      linarith
    obtain ⟨ht,hcore,hpacket⟩ := ap_core_clump_opening (7-p) (by omega) (by omega) hv hx hw hC hsep hwidth
    refine ⟨_,ht,fun i hik => ?_⟩
    by_cases hip : (i : ℕ)<p
    · have hj : p-1-(i : ℕ)<p := by omega
      have hjcast : ((p-1-(i : ℕ) : ℕ) : ℝ)=(p : ℝ)-1-((i : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega : (i : ℕ) ≤ p-1),hcastL]
      have hm : x+((p-1-(i : ℕ) : ℕ) : ℝ)*u ∈ C :=
        Finset.mem_image.mpr ⟨p-1-(i : ℕ),Finset.mem_range.mpr hj,rfl⟩
      have hd : speeds c A u v p i-speeds c A u v p k = -(x+((p-1-(i : ℕ) : ℕ) : ℝ)*u) := by
        rw [hjcast]
        simp [speeds,hip,hkp,x]
        ring
      rw [hd,neg_mul,Fresh.Localisation.distInt_neg]
      exact hpacket _ hm
    · have hip' : p ≤ (i : ℕ) := by omega
      have hkp' : p ≤ (k : ℕ) := by omega
      have hicas : (((i : ℕ)-p : ℕ) : ℝ)=((i : ℕ) : ℝ)-(p : ℝ) := by norm_cast
      have hkcas : (((k : ℕ)-p : ℕ) : ℝ)=((k : ℕ) : ℝ)-(p : ℝ) := by norm_cast
      let n := (((i : ℕ) : ℤ)-((k : ℕ) : ℤ)).natAbs
      have hn1 : 1 ≤ n := by dsimp [n]; have := Fin.val_ne_of_ne hik; omega
      have hnle : n ≤ 7-p := by dsimp [n]; have := i.isLt; have := k.isLt; omega
      have hd : speeds c A u v p i-speeds c A u v p k = (((i : ℕ) : ℝ)-((k : ℕ) : ℝ))*v := by
        simp only [speeds,if_neg hip,if_neg hkp]
        rw [hicas,hkcas]
        ring
      have he : |speeds c A u v p i-speeds c A u v p k|=(n : ℝ)*v := by
        rw [hd,abs_mul,abs_of_pos hv,← natAbs_cast_abs i k]
      rw [← Fresh.Localisation.distInt_abs_mul,he]
      exact hcore n hn1 hnle

/-- Positive distinct physical speeds, independent internal AP steps,
original gap/width inequalities, and arbitrary affine labels/mirror/scale. -/
-- STANDING: DEFINITION
def UnequalTwoAPBlockClass (V : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < V i) ∧ Function.Injective V ∧
  ∃ (c A u v B s : ℝ) (p : ℕ) (σ : Equiv.Perm (Fin 8)),
    2 ≤ p ∧ p ≤ 6 ∧ 0<u ∧ 0<v ∧ 0<A-((p : ℝ)-1)*u ∧ s ≠ 0 ∧
    8*((p : ℝ)-1)*u ≤ (A-((p : ℝ)-1)*u)*(8-(p : ℝ)) ∧
    8*(7-(p : ℝ))*v ≤ (A-((p : ℝ)-1)*u)*(p : ℝ) ∧
    (7-(p : ℝ))*v*(1/(8*u)+1/(A-((p : ℝ)-1)*u)) ≤ 3/4 ∧
    ((p : ℝ)-1)*u*(1/(8*v)+1/(A-((p : ℝ)-1)*u)) ≤ 3/4 ∧
    V = (fun i => B+s*speeds c A u v p (σ i))

theorem unequalTwoAPBlock_isolation {V : Fin 8 → ℝ}
    (h : UnequalTwoAPBlockClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,A,u,v,B,s,p,σ,hp2,hp6,hu,hv,hg,hs,hsepL,hsepR,hwL,hwR,hV⟩ := h
  rw [hV]
  have hi := unequal_two_block_all c A u v p hp2 hp6 hu hv hg hsepL hsepR hwL hwR (σ k)
  have ha := subject_isolation_affine B s hs hi
  exact (Fresh.isolation_comp_perm _ σ k).2 ha

#print axioms unequal_two_block_all
#print axioms unequalTwoAPBlock_isolation
end Fresh.UnequalAPArrangement
