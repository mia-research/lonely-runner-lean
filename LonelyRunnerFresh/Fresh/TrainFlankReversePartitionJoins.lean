import Fresh.ThreeBlockReversePartitions
import Fresh.ThreeBlockReverseLaps

/-! Rules: 1–4, 8–18. Root2+4+2 reverse class is contained in the
all-six partition class; no claim of strict new reverse arrangement space. -/
namespace Fresh.TrainFlankReversePartitionJoins
open Fresh.ThreeBlockReversePartitions Fresh.ThreeBlockReverseLaps

theorem reverse_into_reverse_partitions {V : Fin 8→ℝ}
    (h : ThreeBlockReverseLapsClass V) : ThreeBlockReversePartitionsClass V := by
  obtain ⟨hpos,hinj,c,g,h,B,z,m,a,b,σ,hm,hgpos,hhpos,hsmall,hg,hh,hsum,hz,hV⟩ := h
  exact ⟨hpos,hinj,c,g,h,B,z,2,4,m,a,b,σ,by omega,by omega,by omega,
    hm,hgpos,hhpos,hsmall,hg,hh,hsum,hz,hV⟩

set_option pp.fullNames true in
#print axioms reverse_into_reverse_partitions
set_option pp.fullNames true in
#print axioms Fresh.ThreeBlockPartitions.partitions_all_subjects
set_option pp.fullNames true in
#print axioms Fresh.ThreeBlockReversePartitions.reverse_partitions_all_subjects
end Fresh.TrainFlankReversePartitionJoins
