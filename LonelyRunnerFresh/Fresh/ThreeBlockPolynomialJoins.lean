import Fresh.ThreeBlockPolynomialGaps
import Fresh.ThreeBlockClassJoins

/-! Containment of the polynomial input region in the independent-lap family.
[PROVISIONAL: counting tool] inherited canonical ceiling index. -/
namespace Fresh.ThreeBlockPolynomialJoins
open Fresh.ThreeBlockPolynomialGaps Fresh.ThreeBlockGridTriangle
  Fresh.ThreeBlockIndependentLaps

theorem polynomial_into_triangle {V : Fin 8 → ℝ}
    (h : ThreeBlockPolynomialGapsClass V) : ThreeBlockGridTriangleClass V := by
  obtain ⟨hpos,hinj,c,g,h,B,z,σ,hg,hh,hpoly,hz,hV⟩ := h
  obtain ⟨m,hm,hgq,hhq,hsum⟩ := polynomial_grid g h hg hh hpoly
  exact ⟨hpos,hinj,c,g,h,B,z,m,σ,hm,hgq,hhq,hsum,hz,hV⟩

theorem polynomial_into_independent {V : Fin 8 → ℝ}
    (h : ThreeBlockPolynomialGapsClass V) : ThreeBlockIndependentLapsClass V :=
  Fresh.ThreeBlockClassJoins.triangle_into_independent (polynomial_into_triangle h)

#print axioms polynomial_into_triangle
#print axioms polynomial_into_independent
end Fresh.ThreeBlockPolynomialJoins
