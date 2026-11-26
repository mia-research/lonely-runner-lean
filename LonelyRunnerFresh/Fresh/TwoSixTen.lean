import Fresh.TwoSixTight
import Fresh.PairGapHalf

/-!
Rules1–4,8–18. Reuse of the existing PairGapHalf boundary construction
sharpens the same physical two-plus-six assembly from15max to10max.
Actual-cascade/named-native-candidate tests preceded formalisation:
two_six_ten_v1.py reproduces pair_phase's rho<2 branches at the new edge.
[PROVISIONAL: counting tool] inherited exact boundary selection;
[PROVISIONAL: covering] inherited pair-window fit and finite step split.
No existing proof/API is changed; the half-gap pair theorem is reused.
-/
namespace Fresh.TwoSixTen
open Fresh Fresh.Localisation Fresh.OneMover Fresh.TwoSixPhase
open Fresh.TwoSixTight Fresh.UnequalAPArrangement

theorem ap_core_pair_half (r : ℕ) (hr1 : 1≤r) (hr6 : r≤6)
    {u a b : ℝ} (hu : 0<u) (ha : 0<a) (hab : a≤b)
    (hsep : 4*(r : ℝ)*u≤a*(7-(r : ℝ))) :
    ∃T : ℝ, 0<T ∧
      (∀j : ℕ, 1≤j → j≤r → (1/8 : ℝ)≤distInt (((j : ℝ)*u)*T)) ∧
      (1/8 : ℝ)≤distInt (a*T) ∧ (1/8 : ℝ)≤distInt (b*T) := by
  have hr : (0 : ℝ)<r := by exact_mod_cast (show 0<r by omega)
  obtain ⟨T,hlo,hhi,hpair⟩ := Fresh.PairGapHalf.pair_gap_half ha hab (1/(8*u))
  have ht : 0<T := lt_of_lt_of_le (by positivity) hlo
  have hfit : 1/(8*u)+1/(2*a)≤7/(8*(r : ℝ)*u) := by
    apply (le_div_iff₀ (by positivity : 0<8*(r : ℝ)*u)).2
    have he : (1/(8*u)+1/(2*a))*(8*(r : ℝ)*u)=((r : ℝ)*a+4*(r : ℝ)*u)/a := by field_simp <;> ring
    rw [he,div_le_iff₀ ha]
    nlinarith
  have hbound := hhi.trans hfit
  refine ⟨T,ht,?_,hpair a (by simp),hpair b (by simp)⟩
  intro j hj1 hjr
  have hjlo : (1 : ℝ)≤j := by exact_mod_cast hj1
  have hjhi : (j : ℝ)≤r := by exact_mod_cast hjr
  have hju : 0≤(j : ℝ)*u := by positivity
  apply clear_of_window 0 <;> push_cast
  · have hh := mul_le_mul_of_nonneg_left hlo hju
    have he : ((j : ℝ)*u)*(1/(8*u))=(j : ℝ)/8 := by field_simp
    rw [he] at hh
    linarith
  · have h1 := (le_div_iff₀ (by positivity : 0<8*(r : ℝ)*u)).mp hbound
    have h2 := mul_le_mul_of_nonneg_right hjhi ht.le
    nlinarith [mul_le_mul_of_nonneg_right h2 hu.le]

theorem two_six_ten_all_subjects (c A b : ℝ) (hb : 0<b)
    (hg : 10*max 1 b≤A-1) :
    ∀k : Fin 8, Isolation (speeds c A 1 b 2) k := by
  have hmax1 : (1 : ℝ)≤ max 1 b := le_max_left _ _
  have hmaxb : b≤ max 1 b := le_max_right _ _
  have hgpos : 0<A-1 := by nlinarith
  have hgb : 10*b≤A-1 := by nlinarith
  intro k
  by_cases hkp : (k : ℕ)<2
  · let x : ℝ := A-((k : ℕ) : ℝ)
    have hkR : ((k : ℕ) : ℝ)≤1 := by exact_mod_cast (show (k : ℕ)≤1 by omega)
    have hxg : A-1≤x := by dsimp [x]; linarith
    have hx9 : 9*max 1 b≤x := by nlinarith
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
  · let x : ℝ := A-1+(((k : ℕ)-2 : ℕ) : ℝ)*b
    have hk0 : (0 : ℝ)≤((k : ℕ)-2 : ℕ) := Nat.cast_nonneg _
    have hxg : A-1≤x := by dsimp [x]; nlinarith
    have hx : 0<x := hgpos.trans_le hxg
    obtain ⟨T,hT,hcore,hA,hB⟩ := ap_core_pair_half 5 (by omega) (by omega) hb hx
      (b:=x+1) (by linarith) (by norm_num; nlinarith)
    refine ⟨T,hT,fun i hik=>?_⟩
    by_cases hip : (i : ℕ)<2
    · have hij : (i : ℕ)=0 ∨ (i : ℕ)=1 := by omega
      rcases hij with hi | hi
      · have hd : speeds c A 1 b 2 i-speeds c A 1 b 2 k = -(x+1) := by simp [speeds,hkp,hi,x]; ring
        rw [hd,neg_mul,distInt_neg]
        exact hB
      · have hd : speeds c A 1 b 2 i-speeds c A 1 b 2 k = -x := by simp [speeds,hkp,hi,x]; ring
        rw [hd,neg_mul,distInt_neg]
        exact hA
    · have hip' : 2≤(i : ℕ) := by omega
      have hkp' : 2≤(k : ℕ) := by omega
      have hicas : (((i : ℕ)-2 : ℕ) : ℝ)=((i : ℕ) : ℝ)-2 := by norm_cast
      have hkcas : (((k : ℕ)-2 : ℕ) : ℝ)=((k : ℕ) : ℝ)-2 := by norm_cast
      let n := (((i : ℕ) : ℤ)-((k : ℕ) : ℤ)).natAbs
      have hn1 : 1≤n := by dsimp [n]; have := Fin.val_ne_of_ne hik; omega
      have hn5 : n≤5 := by dsimp [n]; have := i.isLt; have := k.isLt; omega
      have hd : speeds c A 1 b 2 i-speeds c A 1 b 2 k = (((i : ℕ) : ℝ)-((k : ℕ) : ℝ))*b := by
        simp only [speeds,if_neg hip,if_neg hkp]
        rw [hicas,hkcas]
        ring
      have he : |speeds c A 1 b 2 i-speeds c A 1 b 2 k|=(n : ℝ)*b := by
        rw [hd,abs_mul,abs_of_pos hb,←natAbs_cast_abs i k]
      rw [←Fresh.Localisation.distInt_abs_mul,he]
      exact hcore n hn1 hn5

#print axioms ap_core_pair_half
#print axioms two_six_ten_all_subjects
end Fresh.TwoSixTen
