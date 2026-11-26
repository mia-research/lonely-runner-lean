import Fresh.ThreeBlockPartitions
import Fresh.ThreeBlockWideJoins

/-! Rules: 1–4, 8–18. Containment prevents counting the2+4+2 source class
again as an independent family. Other partitions are not claimed disjoint
from every earlier physical class. -/
namespace Fresh.TrainFlankPartitionJoins
open Fresh.ThreeBlockPartitions Fresh.ThreeBlockWideLaps

theorem wide_into_partitions {V : Fin 8→ℝ} (h : ThreeBlockWideLapsClass V) :
    ThreeBlockPartitionsClass V := by
  obtain ⟨hpos,hinj,c,g,h,B,z,m,a,b,σ,hm,hgpos,hhpos,hsmall,hg,hh,hsum,hz,hV⟩ := h
  exact ⟨hpos,hinj,c,g,h,B,z,2,4,m,a,b,σ,by omega,by omega,by omega,
    hm,hgpos,hhpos,hsmall,hg,hh,hsum,hz,hV⟩

theorem independent_into_partitions {V : Fin 8→ℝ}
    (h : Fresh.ThreeBlockIndependentLaps.ThreeBlockIndependentLapsClass V) :
    ThreeBlockPartitionsClass V :=
  wide_into_partitions (Fresh.ThreeBlockWideJoins.independent_into_wide h)

theorem polynomial_into_partitions {V : Fin 8→ℝ}
    (h : Fresh.ThreeBlockPolynomialGaps.ThreeBlockPolynomialGapsClass V) :
    ThreeBlockPartitionsClass V :=
  wide_into_partitions (Fresh.ThreeBlockWideJoins.polynomial_into_wide h)

#print axioms wide_into_partitions
#print axioms independent_into_partitions
#print axioms polynomial_into_partitions
end Fresh.TrainFlankPartitionJoins
