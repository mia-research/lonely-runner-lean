import Fresh.TwoSixPhase
import Fresh.APCorePair
import Fresh.UnequalAPArrangement

/-!
Rules1–4,8–18. All eight physical subjects for two AP speeds followed by
six AP speeds, arbitrary positive step ratio. The original gap bound20max
supplies every subject's retained reading inequalities. Upper six subjects
reuse the established AP-core-plus-pair boundary fact; this is not a new
claim that its already-known frozen-core family was previously unproved.
[PROVISIONAL: counting tool] inherited named boundary selection;
[PROVISIONAL: covering] inherited pair-window fit and finite b split.
-/
namespace Fresh.TwoSixArrangement
open Fresh Fresh.Localisation Fresh.OneMover Fresh.TwoSixPhase
open Fresh.APCorePair Fresh.UnequalAPArrangement

theorem two_six_all_subjects (c A b : ℝ) (hb : 0<b)
    (hg : 20*max 1 b≤A-1) :
    ∀k : Fin 8, Isolation (speeds c A 1 b 2) k := by
  have hmax1 : (1 : ℝ)≤ max 1 b := le_max_left _ _
  have hmaxb : b≤ max 1 b := le_max_right _ _
  have hgpos : 0<A-1 := by nlinarith
  have hgb : 20*b≤A-1 := by nlinarith
  intro k
  by_cases hkp : (k : ℕ)<2
  · let x : ℝ := A-((k : ℕ) : ℝ)
    have hkR : ((k : ℕ) : ℝ)≤1 := by exact_mod_cast (show (k : ℕ)≤1 by omega)
    have hxg : A-1≤x := by dsimp [x]; linarith
    obtain ⟨T,hT,hcore,hpacket⟩ := two_six_any hb (hg.trans hxg)
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
    obtain ⟨T,hT,hcore,hA,hB⟩ := ap_core_pair 5 (by omega) (by omega) hb hx
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

#print axioms two_six_all_subjects
end Fresh.TwoSixArrangement
