import Fresh.ThreeBlockReverseMiddlePartitions
import Fresh.TrainFlankReversePartitionJoins

/-! Rules: 1–4, 8–18. Existing reflected six-partition class is contained
in the middle-singleton extension; no strict reflected new-space claim. -/
namespace Fresh.TrainFlankReverseMiddlePartitionJoins
open Fresh.ThreeBlockReverseMiddlePartitions Fresh.ThreeBlockReversePartitions

theorem reverse_partitions_into_middle {V : Fin 8→ℝ}
    (h : ThreeBlockReversePartitionsClass V) : ThreeBlockReverseMiddlePartitionsClass V := by
  obtain ⟨hpos,hinj,c,g,h,B,z,p,q,m,a,b,σ,hp,hq,hpq,hm,hgpos,hhpos,hsmall,hg,hh,hsum,hz,hV⟩ := h
  exact ⟨hpos,hinj,c,g,h,B,z,p,q,m,a,b,σ,hp,by omega,hpq,hm,hgpos,hhpos,hsmall,hg,hh,hsum,hz,hV⟩

theorem reverse_into_middle {V : Fin 8→ℝ}
    (h : Fresh.ThreeBlockReverseLaps.ThreeBlockReverseLapsClass V) : ThreeBlockReverseMiddlePartitionsClass V :=
  reverse_partitions_into_middle (Fresh.TrainFlankReversePartitionJoins.reverse_into_reverse_partitions h)

set_option pp.fullNames true in
#print axioms reverse_partitions_into_middle
set_option pp.fullNames true in
#print axioms reverse_into_middle
set_option pp.fullNames true in
#print axioms Fresh.ThreeBlockReverseMiddlePartitions.reverse_middle_partitions_all_subjects
end Fresh.TrainFlankReverseMiddlePartitionJoins
