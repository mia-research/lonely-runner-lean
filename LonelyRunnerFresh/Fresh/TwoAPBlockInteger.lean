import Fresh.SplitAPArrangementAll

/-!
Rules: 1–4, 8–18. At an integer relative offset, two same-step physical AP
blocks can only be disjoint: otherwise an explicit pair of labels has equal
speed. This reduction retains the conjecture's physical collision exclusion.
-/
namespace Fresh.SplitAPArrangement
open Fresh

theorem integer_offset_separated (c A : ℝ) (p : ℕ) (hp2 : 2 ≤ p) (hp6 : p ≤ 6)
    (m : ℤ) (hA : A=(m : ℝ)) (hinj : Function.Injective (speeds c A p)) :
    (p : ℝ)-1 < A ∨ A+((7-p : ℕ) : ℝ)<0 := by
  by_cases hpos : (p : ℝ)-1 < A
  · exact Or.inl hpos
  by_cases hneg : A+((7-p : ℕ) : ℝ)<0
  · exact Or.inr hneg
  have hAle : A ≤ (p : ℝ)-1 := le_of_not_gt hpos
  have hAge : 0 ≤ A+((7-p : ℕ) : ℝ) := le_of_not_gt hneg
  by_cases hm : 0 ≤ m
  · let n := m.toNat
    have hnR : (n : ℝ)=A := by
      have hnI : (n : ℤ)=m := Int.toNat_of_nonneg hm
      rw [hA]
      exact_mod_cast hnI
    have hnp : n<p := by
      have hh : (n : ℝ)<(p : ℝ) := by linarith
      exact_mod_cast hh
    let i : Fin 8 := ⟨n,by omega⟩
    let j : Fin 8 := ⟨p,by omega⟩
    have hi : (i : ℕ)<p := hnp
    have hj : ¬(j : ℕ)<p := by dsimp [j]; omega
    have he : speeds c A p i=speeds c A p j := by
      simp only [speeds,if_pos hi,if_neg hj]
      dsimp [i,j]
      simp only [Nat.sub_self,Nat.cast_zero,add_zero]
      rw [hnR]
    have hv := congrArg Fin.val (hinj he)
    dsimp [i,j] at hv
    omega
  · have hmneg : m<0 := lt_of_not_ge hm
    let n := (-m).toNat
    have hnR : (n : ℝ) = -A := by
      have hnI : (n : ℤ) = -m := Int.toNat_of_nonneg (by omega : 0 ≤ -m)
      rw [hA]
      exact_mod_cast hnI
    have hnle : n ≤ 7-p := by
      have hh : (n : ℝ) ≤ ((7-p : ℕ) : ℝ) := by linarith
      exact_mod_cast hh
    let j : Fin 8 := ⟨p+n,by omega⟩
    have hj : ¬(j : ℕ)<p := by dsimp [j]; omega
    have he : speeds c A p (0 : Fin 8)=speeds c A p j := by
      have h0 : ((0 : Fin 8) : ℕ)<p := by simp; omega
      simp only [speeds,if_pos h0,if_neg hj]
      dsimp [j]
      simp only [Fin.val_zero,Nat.cast_zero,add_zero,Nat.add_sub_cancel_left]
      rw [hnR]
      ring
    have hv := congrArg Fin.val (hinj he)
    dsimp [j] at hv
    simp at hv
    omega

#print axioms integer_offset_separated
end Fresh.SplitAPArrangement
