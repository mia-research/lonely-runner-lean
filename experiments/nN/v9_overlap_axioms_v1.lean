import LonelyRunner.LRC.Spec.OverlapFlankN

#print axioms LRC.Resonance.flankWorks_of_free_shift
#print axioms LRC.Resonance.card_pair_erase_le
#print axioms LRC.Resonance.flankWorks_of_overlap
example : LRC.Resonance.shiftPairs 5 5 [1, 4, 6] = {(1,0),(1,1),(1,2),(4,0),(4,1)} := by decide
