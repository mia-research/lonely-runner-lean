import Fresh.ThreeBlockReverseLaps
import Fresh.ThreeBlockWideLaps

/-! An integer grand return turns a reverse-grid reference into the forward
reference. This is an overlap result, not another arrangement family. -/
namespace Fresh.ThreeBlockReturnJoins

theorem reverse_bands_return (g h : ℝ) (m a b P G H : ℤ)
    (hP : m+1 ≤ P)
    (hPg : (P : ℝ)*g = (G : ℝ)) (hPh : (P : ℝ)*h = (H : ℝ))
    (hg : (8*(m : ℝ)-1)*g ≤ 8*(a : ℝ)-1)
    (hh : (8*(m : ℝ)-1)*h ≤ 8*(b : ℝ)-1)
    (hsum : 8*((a : ℝ)+(b : ℝ))-3 ≤ (8*(m : ℝ)-1)*(g+h)) :
    1 ≤ P-m ∧
    8*((G-a : ℤ) : ℝ)+1 ≤ (8*((P-m : ℤ) : ℝ)+1)*g ∧
    8*((H-b : ℤ) : ℝ)+1 ≤ (8*((P-m : ℤ) : ℝ)+1)*h ∧
    (8*((P-m : ℤ) : ℝ)+1)*(g+h) ≤
      8*(((G-a : ℤ) : ℝ)+((H-b : ℤ) : ℝ))+3 := by
  refine ⟨by omega,?_,?_,?_⟩
  all_goals push_cast
  all_goals nlinarith

#print axioms reverse_bands_return
end Fresh.ThreeBlockReturnJoins
