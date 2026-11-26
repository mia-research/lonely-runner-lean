import Fresh.ThreeBlockNeighbour
import Fresh.ThreeBlockMiddlePartitions
import Fresh.ThreeBlockEndpointSingleton

/-! Earlier partition families embed in the uniform neighbour rule.
No assertion of disjointness or an exhaustive arrangement classification. -/
namespace Fresh.ThreeBlockNeighbourJoins
open Fresh.ThreeBlockNeighbour

theorem middle_into_neighbour {V : Fin 8 → ℝ}
    (h : Fresh.ThreeBlockMiddlePartitions.ThreeBlockMiddlePartitionsClass V) :
    ThreeBlockNeighbourClass V := by
  obtain ⟨hpos,hinj,c,g,h,B,z,p,q,m,a,b,σ,hp,hq,hpq,hm,hgpos,hhpos,hsmall,hg,hh,hsum,hz,hV⟩ := h
  refine ⟨hpos,hinj,c,g,h,B,z,p,q,m,a,b,σ,by omega,hq,by omega,
    hgpos,hhpos,hsmall,?_,?_,hm,hg,hh,hsum,hz,hV⟩
  · intro he
    omega
  · intro he
    omega

theorem endpoint_into_neighbour {V : Fin 8 → ℝ}
    (h : Fresh.ThreeBlockEndpointSingleton.EndpointSingletonClass V) :
    ThreeBlockNeighbourClass V := by
  obtain ⟨hpos,hinj,c,g,h,B,z,q,m,a,b,σ,hq1,hq5,hm,hgpos,hhpos,hsmall,hg,hh,hsum,hz,hV⟩ := h
  refine ⟨hpos,hinj,c,g,h,B,z,1,q,m,a,b,σ,by norm_num,hq1,by omega,
    by linarith,hhpos,hsmall,fun _ => hgpos,?_,hm,hg,hh,hsum,hz,hV⟩
  intro he
  omega

#print axioms middle_into_neighbour
#print axioms endpoint_into_neighbour
end Fresh.ThreeBlockNeighbourJoins
