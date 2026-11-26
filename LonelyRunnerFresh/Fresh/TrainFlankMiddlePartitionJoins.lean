import Fresh.ThreeBlockMiddlePartitions
import Fresh.TrainFlankPartitionJoins

/-! Rules: 1–4, 8–18. Existing six-partition class is contained in the
middle-singleton extension. This prevents duplicate family counting. -/
namespace Fresh.TrainFlankMiddlePartitionJoins
open Fresh.ThreeBlockMiddlePartitions Fresh.ThreeBlockPartitions

theorem partitions_into_middle {V : Fin 8→ℝ}
    (h : ThreeBlockPartitionsClass V) : ThreeBlockMiddlePartitionsClass V := by
  obtain ⟨hpos,hinj,c,g,h,B,z,p,q,m,a,b,σ,hp,hq,hpq,hm,hgpos,hhpos,hsmall,hg,hh,hsum,hz,hV⟩ := h
  exact ⟨hpos,hinj,c,g,h,B,z,p,q,m,a,b,σ,hp,by omega,hpq,hm,hgpos,hhpos,hsmall,hg,hh,hsum,hz,hV⟩

theorem wide_into_middle {V : Fin 8→ℝ}
    (h : Fresh.ThreeBlockWideLaps.ThreeBlockWideLapsClass V) : ThreeBlockMiddlePartitionsClass V :=
  partitions_into_middle (Fresh.TrainFlankPartitionJoins.wide_into_partitions h)

set_option pp.fullNames true in
#print axioms partitions_into_middle
set_option pp.fullNames true in
#print axioms wide_into_middle
set_option pp.fullNames true in
#print axioms Fresh.ThreeBlockMiddlePartitions.middle_partitions_all_subjects
end Fresh.TrainFlankMiddlePartitionJoins
