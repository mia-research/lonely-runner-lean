/-
Axiom check for the whole of `LonelyRunner/LRC/Spec/Target.lean`.

WHY THIS FILE EXISTS.  `Spec/Target.lean` sits outside both gates: neither the Construction8 gate nor
the cascade gate builds it or runs `#print axioms` on it.  Its predecessor artefact,
`v9_2_spec_axioms_v1.lean`, covered four declarations.  Target.lean now carries 17 theorems, and the
2026-09-18 target amendment rests on seven declarations that artefact never named -- so it had become
a stale witness passing for a file it no longer described.  This file names EVERY theorem in the
module.  Compile with:  cd LonelyRunner && lake env lean ../experiments/n8/v9_6_spec_axioms_v1.lean
-/
import LonelyRunner.LRC.Spec.Target

-- the difference-set form and its equivalents (unchanged from v9_2_spec_axioms_v1)
#print axioms LRC.Spec.target_forms_agree
#print axioms LRC.Spec.target_flank_agrees
#print axioms LRC.Spec.existence_of_capped
#print axioms LRC.Spec.capped_of_existence

-- finite active membership
#print axioms LRC.Spec.cascade_of_FAM
#print axioms LRC.Spec.FAM_of_existence
#print axioms LRC.Spec.FAM_iff_existence

-- the three-largest-flanks conjecture and the congruence form
#print axioms LRC.Spec.exists_lonely_of_threeLargest
#print axioms LRC.Spec.congruence_of_existence
#print axioms LRC.Spec.exists_lonely_of_congruence

-- THE TARGET (2026-09-18 amendment) and the arrangement obligation
#print axioms LRC.Spec.lonelyRunnerAt8_of_existence
#print axioms LRC.Spec.exists_lonely_of_card_le_three
#print axioms LRC.Spec.lonelyRunnerAt8_iff_arrangement
#print axioms LRC.Spec.lonelyRunnerAt8_iff_existenceOnArrangements
#print axioms LRC.Spec.lonelyRunnerAt8_of_arrangement
