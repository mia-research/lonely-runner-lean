import LonelyRunner.LRC.Spec.DoorsN
open LRC.SpecN

instance : Fact (2 ≤ 5) := ⟨by norm_num⟩
instance : Fact (2 ≤ 6) := ⟨by norm_num⟩
instance : Fact (2 ≤ 7) := ⟨by norm_num⟩

-- headline instantiations at each small order
theorem doors_five  {v : Fin 5 → ℝ} (hv : Function.Injective v) (k : Fin 5) :
    (DoorFlank v k ↔ LonelyForSubject v k) ∧ (DoorArrives v k ↔ LonelyForSubject v k) ∧
    (DoorCapped v k ↔ LonelyForSubject v k) ∧ (DoorFAM v k ↔ LonelyForSubject v k) := doors_agree hv k
theorem doors_six   {v : Fin 6 → ℝ} (hv : Function.Injective v) (k : Fin 6) :
    (DoorFlank v k ↔ LonelyForSubject v k) ∧ (DoorArrives v k ↔ LonelyForSubject v k) ∧
    (DoorCapped v k ↔ LonelyForSubject v k) ∧ (DoorFAM v k ↔ LonelyForSubject v k) := doors_agree hv k
theorem doors_seven {v : Fin 7 → ℝ} (hv : Function.Injective v) (k : Fin 7) :
    (DoorFlank v k ↔ LonelyForSubject v k) ∧ (DoorArrives v k ↔ LonelyForSubject v k) ∧
    (DoorCapped v k ↔ LonelyForSubject v k) ∧ (DoorFAM v k ↔ LonelyForSubject v k) := doors_agree hv k

-- the target-form equivalences at each small order
theorem forms_five  : ExistenceAtN 5 ↔ ExistenceAtN_cascade 5 := target_forms_agree
theorem forms_six   : ExistenceAtN 6 ↔ ExistenceAtN_cascade 6 := target_forms_agree
theorem forms_seven : ExistenceAtN 7 ↔ ExistenceAtN_cascade 7 := target_forms_agree
theorem flank_five  : ExistenceAtN 5 ↔ ExistenceAtN_flank 5 := target_flank_iff
theorem flank_six   : ExistenceAtN 6 ↔ ExistenceAtN_flank 6 := target_flank_iff
theorem flank_seven : ExistenceAtN 7 ↔ ExistenceAtN_flank 7 := target_flank_iff
theorem fam_five    : FiniteActiveMembership 5 ↔ ExistenceAtN 5 := FAM_iff_existence
theorem fam_six     : FiniteActiveMembership 6 ↔ ExistenceAtN 6 := FAM_iff_existence
theorem fam_seven   : FiniteActiveMembership 7 ↔ ExistenceAtN 7 := FAM_iff_existence
theorem capped_five : CascadeCapped 5 → ExistenceAtN 5 := existence_of_capped
theorem capped_six  : CascadeCapped 6 → ExistenceAtN 6 := existence_of_capped
theorem capped_sevn : CascadeCapped 7 → ExistenceAtN 7 := existence_of_capped
theorem arr_five    : LonelyRunnerAtN 5 ↔ ExistenceOnArrangements 5 := lonelyRunnerAtN_iff_existenceOnArrangements
theorem arr_six     : LonelyRunnerAtN 6 ↔ ExistenceOnArrangements 6 := lonelyRunnerAtN_iff_existenceOnArrangements
theorem arr_seven   : LonelyRunnerAtN 7 ↔ ExistenceOnArrangements 7 := lonelyRunnerAtN_iff_existenceOnArrangements
theorem iso_five    : ExistenceOnArrangements 5 ↔ ∀ v : Fin 5 → ℝ, Function.Injective v → ∀ k : Fin 5, ∃ t : ℝ, 0 < t ∧ blockDegree v t k = 0 := existenceOnArrangements_iff_isolated
theorem iso_seven   : ExistenceOnArrangements 7 ↔ ∀ v : Fin 7 → ℝ, Function.Injective v → ∀ k : Fin 7, ∃ t : ℝ, 0 < t ∧ blockDegree v t k = 0 := existenceOnArrangements_iff_isolated
#print axioms LRC.SpecN.CascadeCapped
#print axioms LRC.SpecN.DoorArrives
#print axioms LRC.SpecN.DoorCapped
#print axioms LRC.SpecN.DoorFAM
#print axioms LRC.SpecN.DoorFirstLap
#print axioms LRC.SpecN.DoorFlank
#print axioms LRC.SpecN.DoorLargestFlank
#print axioms LRC.SpecN.DoorThreeLargest
#print axioms LRC.SpecN.ExistenceAtN
#print axioms LRC.SpecN.ExistenceAtN_cascade
#print axioms LRC.SpecN.ExistenceAtN_congruence
#print axioms LRC.SpecN.ExistenceAtN_flank
#print axioms LRC.SpecN.ExistenceOnArrangements
#print axioms LRC.SpecN.FAM_iff_existence
#print axioms LRC.SpecN.FAM_of_existence
#print axioms LRC.SpecN.FiniteActiveMembership
#print axioms LRC.SpecN.InWay
#print axioms LRC.SpecN.LonelyAt
#print axioms LRC.SpecN.LonelyForSubject
#print axioms LRC.SpecN.LonelyRunnerAtN
#print axioms LRC.SpecN.ThreeLargestFlanks
#print axioms LRC.SpecN.blockDegree
#print axioms LRC.SpecN.blockDegree_symm_pairs
#print axioms LRC.SpecN.capped_of_existence
#print axioms LRC.SpecN.cascade_of_FAM
#print axioms LRC.SpecN.circDist_abs_mul
#print axioms LRC.SpecN.congruence_of_existence
#print axioms LRC.SpecN.diffSet
#print axioms LRC.SpecN.diffSet_card_le
#print axioms LRC.SpecN.diffSet_nonempty
#print axioms LRC.SpecN.diffSet_pos
#print axioms LRC.SpecN.disp
#print axioms LRC.SpecN.disp_ne_zero
#print axioms LRC.SpecN.doorArrives_iff
#print axioms LRC.SpecN.doorCapped_iff
#print axioms LRC.SpecN.doorCapped_of_doorFirstLap
#print axioms LRC.SpecN.doorFAM_iff
#print axioms LRC.SpecN.doorFlank_iff
#print axioms LRC.SpecN.doorThreeLargest_of_doorLargestFlank
#print axioms LRC.SpecN.doors_agree
#print axioms LRC.SpecN.existenceOnArrangements_iff_isolated
#print axioms LRC.SpecN.existenceOnArrangements_iff_subjects
#print axioms LRC.SpecN.existence_of_capped
#print axioms LRC.SpecN.exists_lonelyAt_iff_bounded
#print axioms LRC.SpecN.exists_lonelyAt_iff_flank
#print axioms LRC.SpecN.exists_lonelyAt_of_named_instant
#print axioms LRC.SpecN.exists_lonelyAt_of_not_dvd
#print axioms LRC.SpecN.exists_lonely_of_card_le_four
#print axioms LRC.SpecN.exists_lonely_of_card_le_three
#print axioms LRC.SpecN.exists_lonely_of_congruence
#print axioms LRC.SpecN.exists_lonely_of_threeLargest
#print axioms LRC.SpecN.firstReading
#print axioms LRC.SpecN.firstReading_pos
#print axioms LRC.SpecN.gapAhead
#print axioms LRC.SpecN.gapAhead_add_gapBehind_le_one
#print axioms LRC.SpecN.gapAhead_nonneg
#print axioms LRC.SpecN.gapBehind
#print axioms LRC.SpecN.gapBehind_nonneg
#print axioms LRC.SpecN.inWay_comm
#print axioms LRC.SpecN.leastDisp
#print axioms LRC.SpecN.leastDisp_le
#print axioms LRC.SpecN.leastDisp_mem
#print axioms LRC.SpecN.leastDisp_pos
#print axioms LRC.SpecN.lonelyAt_add_const
#print axioms LRC.SpecN.lonelyAt_const_mul
#print axioms LRC.SpecN.lonelyAt_iff_blockDegree_zero
#print axioms LRC.SpecN.lonelyAt_iff_gaps
#print axioms LRC.SpecN.lonelyAt_iff_lonely_diffSet
#print axioms LRC.SpecN.lonelyAt_iff_neighbours
#print axioms LRC.SpecN.lonelyAt_iff_no_inWay
#print axioms LRC.SpecN.lonelyAt_iff_two_sided
#print axioms LRC.SpecN.lonelyAt_inv_of_not_dvd
#print axioms LRC.SpecN.lonelyAt_named_instant
#print axioms LRC.SpecN.lonelyForSubject_iff_diffSet
#print axioms LRC.SpecN.lonelyForSubject_of_threeLargest
#print axioms LRC.SpecN.lonelyRunnerAtN_iff_arrangement
#print axioms LRC.SpecN.lonelyRunnerAtN_iff_existenceOnArrangements
#print axioms LRC.SpecN.lonelyRunnerAtN_of_arrangement
#print axioms LRC.SpecN.lonelyRunnerAtN_of_doorArrives
#print axioms LRC.SpecN.lonelyRunnerAtN_of_doorCapped
#print axioms LRC.SpecN.lonelyRunnerAtN_of_doorFAM
#print axioms LRC.SpecN.lonelyRunnerAtN_of_doorFirstLap
#print axioms LRC.SpecN.lonelyRunnerAtN_of_doorFlank
#print axioms LRC.SpecN.lonelyRunnerAtN_of_existence
#print axioms LRC.SpecN.mem_diffSet
#print axioms LRC.SpecN.others_nonempty
#print axioms LRC.SpecN.sep
#print axioms LRC.SpecN.sep_add_const
#print axioms LRC.SpecN.sep_const_mul
#print axioms LRC.SpecN.sep_eq
#print axioms LRC.SpecN.sep_eq_disp_mul
#print axioms LRC.SpecN.sum_blockDegree
#print axioms LRC.SpecN.target_flank_agrees
#print axioms LRC.SpecN.target_flank_iff
#print axioms LRC.SpecN.target_forms_agree
#print axioms doors_five
#print axioms doors_six
#print axioms doors_seven
#print axioms forms_five
#print axioms flank_seven
#print axioms fam_six
#print axioms iso_five
#print axioms iso_seven
#print axioms capped_sevn
#print axioms arr_six
