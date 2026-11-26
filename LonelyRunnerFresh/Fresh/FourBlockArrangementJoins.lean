import Fresh.FourBlockArrangement

/-! Formal retention of the earlier all-subject three-block and four-pair
families. A unit gap refines an existing AP block without changing speeds. -/
namespace Fresh.FourBlockArrangementJoins
open Fresh Fresh.FourBlockNeighbour Fresh.FourBlockNeighbourJoins Fresh.FourBlockArrangement

theorem pairs_into_four {V : Fin 8 → ℝ} (hV : FourAPPairs.FourAPPairsClass V) :
    FourBlockClass V := by
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,σ,hg,hh,hj,hsmall,hm,hU,hV,hW,hUVW,hz,hEq⟩ := hV
  refine ⟨hpos,hinj,c,g,h,j,B,z,2,2,2,m,a,b,e,σ,
    by norm_num,by norm_num,by norm_num,by norm_num,hg,hh,hj,hsmall,
    by norm_num,by norm_num,hm,hU,hV,hW,hUVW,hz,?_⟩
  simpa only [pair_speeds] using hEq

theorem three_into_four {V : Fin 8 → ℝ}
    (hV : ThreeBlockNeighbour.ThreeBlockNeighbourClass V) : FourBlockClass V := by
  obtain ⟨hpos,hinj,c,g,h,B,z,p,q,m,a,b,σ,hp,hq,hpq,hgpos,hhpos,hsmall,hleft,hright,hm,hg,hh,hsum,hz,hV⟩ := hV
  by_cases hp2 : 2 ≤ p
  · refine ⟨hpos,hinj,c,1,g,h,B,z,1,p-1,q,m,m,a,b,σ,
      by omega,by omega,hq,by omega,by norm_num,hgpos,hhpos,by linarith,
      by norm_num,?_,hm,by nlinarith,hg,hh,by nlinarith,hz,?_⟩
    · intro hcut
      exact hright (by omega)
    · simpa only [refine_left c g h p q hp2] using hV
  · by_cases hq2 : 2 ≤ q
    · refine ⟨hpos,hinj,c,g,1,h,B,z,p,1,q-1,m,a,m,b,σ,
        hp,by omega,by omega,by omega,hgpos,by norm_num,hhpos,by linarith,
        hleft,?_,hm,hg,by nlinarith,hh,by nlinarith,hz,?_⟩
      · intro hcut
        exact hright (by omega)
      · simpa only [refine_middle c g h p q hq2] using hV
    · refine ⟨hpos,hinj,c,g,h,1,B,z,p,q,1,m,a,b,m,σ,
        hp,hq,by omega,by omega,hgpos,hhpos,by norm_num,by linarith,
        hleft,by norm_num,hm,hg,hh,by nlinarith,by nlinarith,hz,?_⟩
      simpa only [refine_right c g h p q] using hV

#print axioms pairs_into_four
#print axioms three_into_four
end Fresh.FourBlockArrangementJoins
