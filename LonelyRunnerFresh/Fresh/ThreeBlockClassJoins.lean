import Fresh.ThreeBlockIndependentLaps
import Fresh.ThreeBlockComparableGaps
import Fresh.ThreeBlockNearGrid

/-! Rules:1–4,8–18. Explicit containment of physical three-block reference
classes. These inclusions prevent counting the same family repeatedly. -/
open Classical
namespace Fresh.ThreeBlockClassJoins
open Fresh.ThreeBlockCarry Fresh.ThreeBlockGridTriangle
  Fresh.ThreeBlockIndependentLaps Fresh.ThreeBlockComparableGaps Fresh.ThreeBlockNearGrid

theorem triangle_into_independent {V : Fin 8 → ℝ}
    (h : ThreeBlockGridTriangleClass V) : ThreeBlockIndependentLapsClass V := by
  obtain ⟨hpos,hinj,c,g,h,B,z,m,σ,hm,hg,hh,hsum,hz,hV⟩ := h
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 0 < 8*(m : ℝ)+1 := by linarith
  have hgpos : 0<g := by nlinarith
  have hhpos : 0<h := by nlinarith
  have hsmall : g+h≤1/3 := by nlinarith
  refine ⟨hpos,hinj,c,g,h,B,z,m,0,0,σ,hm,hgpos,hhpos,hsmall,?_,?_,?_,hz,hV⟩
  all_goals simpa using (by assumption)

theorem comparable_into_triangle {V : Fin 8 → ℝ}
    (h : ThreeBlockComparableGapsClass V) : ThreeBlockGridTriangleClass V := by
  obtain ⟨hpos,hinj,c,g,h,B,z,σ,hg,hh,hcomp,hsmall,hz,hV⟩ := h
  obtain ⟨m,hm,hgq,hhq,hsum⟩ := canonical_grid g h hg hh hcomp hsmall
  exact ⟨hpos,hinj,c,g,h,B,z,m,σ,hm,hgq,hhq,hsum,hz,hV⟩

theorem comparable_into_independent {V : Fin 8 → ℝ}
    (h : ThreeBlockComparableGapsClass V) : ThreeBlockIndependentLapsClass V :=
  triangle_into_independent (comparable_into_triangle h)

theorem near_grid_into_triangle {V : Fin 8 → ℝ}
    (h : ThreeBlockNearGridClass V) : ThreeBlockGridTriangleClass V := by
  obtain ⟨hpos,hinj,c,g,h,B,z,m,σ,hm,hg,hgrid,hlo,hhi,hz,hV⟩ := h
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hgmax : g≤1/8 := by nlinarith
  have hq : 0<8*(m : ℝ)+1 := by linarith
  have hgq : 1≤(8*(m : ℝ)+1)*g := by nlinarith
  have hhq : 1≤(8*(m : ℝ)+1)*h := by
    have hh := mul_le_mul_of_nonneg_left hlo hq.le
    nlinarith
  have hsum : (8*(m : ℝ)+1)*(g+h)≤3 := by
    have hh := mul_le_mul_of_nonneg_left hhi hq.le
    nlinarith
  exact ⟨hpos,hinj,c,g,h,B,z,m,σ,hm,hgq,hhq,hsum,hz,hV⟩

#print axioms triangle_into_independent
#print axioms comparable_into_triangle
#print axioms comparable_into_independent
#print axioms near_grid_into_triangle
end Fresh.ThreeBlockClassJoins
