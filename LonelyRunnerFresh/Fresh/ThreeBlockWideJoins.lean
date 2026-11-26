import Fresh.ThreeBlockWideLaps
import Fresh.ThreeBlockPolynomialJoins

namespace Fresh.ThreeBlockWideJoins
open Fresh.ThreeBlockWideLaps Fresh.ThreeBlockIndependentLaps

theorem independent_into_wide {V : Fin 8 → ℝ}
    (h : ThreeBlockIndependentLapsClass V) : ThreeBlockWideLapsClass V := by
  obtain ⟨hpos,hinj,c,g,h,B,z,m,a,b,σ,hm,hgpos,hhpos,hsmall,hg,hh,hsum,hz,hV⟩ := h
  exact ⟨hpos,hinj,c,g,h,B,z,m,a,b,σ,hm,hgpos,hhpos,by linarith,hg,hh,hsum,hz,hV⟩

theorem polynomial_into_wide {V : Fin 8 → ℝ}
    (h : Fresh.ThreeBlockPolynomialGaps.ThreeBlockPolynomialGapsClass V) :
    ThreeBlockWideLapsClass V :=
  independent_into_wide (Fresh.ThreeBlockPolynomialJoins.polynomial_into_independent h)

#print axioms independent_into_wide
#print axioms polynomial_into_wide
end Fresh.ThreeBlockWideJoins
