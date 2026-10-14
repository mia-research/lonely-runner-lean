/-
Axiom check for `LonelyRunner/LRC/Spec/Doors.lean` -- the doors stated on arrangements.
Like `Spec/Target.lean`, this module sits outside both gates, so it carries its own witness.
Compile with:  cd LonelyRunner && lake env lean ../experiments/n8/v9_6_doors_axioms_v1.lean
-/
import LonelyRunner.LRC.Spec.Doors

#print axioms LRC.Spec.leastDisp_mem
#print axioms LRC.Spec.leastDisp_le
#print axioms LRC.Spec.leastDisp_pos
#print axioms LRC.Spec.firstReading_pos
#print axioms LRC.Spec.existenceOnArrangements_iff_subjects
#print axioms LRC.Spec.lonelyForSubject_iff_diffSet
#print axioms LRC.Spec.doorFlank_iff
#print axioms LRC.Spec.doorArrives_iff
#print axioms LRC.Spec.doorCapped_iff
#print axioms LRC.Spec.doorFAM_iff
#print axioms LRC.Spec.lonelyForSubject_of_threeLargest
#print axioms LRC.Spec.doors_agree
#print axioms LRC.Spec.lonelyRunnerAt8_of_doorFlank
#print axioms LRC.Spec.lonelyRunnerAt8_of_doorArrives
#print axioms LRC.Spec.lonelyRunnerAt8_of_doorCapped
#print axioms LRC.Spec.lonelyRunnerAt8_of_doorFAM
#print axioms LRC.Spec.lonelyAt_iff_blockDegree_zero
#print axioms LRC.Spec.blockDegree_symm_pairs
#print axioms LRC.Spec.sum_blockDegree
#print axioms LRC.Spec.existenceOnArrangements_iff_isolated
