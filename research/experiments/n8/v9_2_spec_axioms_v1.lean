/- Axiom check for the specification file `LonelyRunner/LRC/Spec/Target.lean`.

That file is deliberately outside both artefacts, so neither gate builds it or runs `#print axioms` on
it. This is the artefact witnessing the manuscript's claim that the reduction is within the three
axioms. Run:  lake env lean experiments/n8/v9_2_spec_axioms_v1.lean  -/
import LonelyRunner.LRC.Spec.Target

#print axioms LRC.Spec.target_forms_agree
#print axioms LRC.Spec.target_flank_agrees
#print axioms LRC.Spec.existence_of_capped
#print axioms LRC.Spec.capped_of_existence
