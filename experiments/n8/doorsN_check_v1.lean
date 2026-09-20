import LonelyRunner.LRC.Spec.DoorsN

open LRC.SpecN

-- the four doors, instantiated at each small order
instance : Fact (2 ≤ 5) := ⟨by norm_num⟩
instance : Fact (2 ≤ 6) := ⟨by norm_num⟩
instance : Fact (2 ≤ 7) := ⟨by norm_num⟩

theorem doors_agree_five {v : Fin 5 → ℝ} (hv : Function.Injective v) (k : Fin 5) :
    (DoorFlank v k ↔ LonelyForSubject v k) ∧ (DoorArrives v k ↔ LonelyForSubject v k) ∧
    (DoorCapped v k ↔ LonelyForSubject v k) ∧ (DoorFAM v k ↔ LonelyForSubject v k) :=
  doors_agree hv k

theorem doors_agree_six {v : Fin 6 → ℝ} (hv : Function.Injective v) (k : Fin 6) :
    (DoorFlank v k ↔ LonelyForSubject v k) ∧ (DoorArrives v k ↔ LonelyForSubject v k) ∧
    (DoorCapped v k ↔ LonelyForSubject v k) ∧ (DoorFAM v k ↔ LonelyForSubject v k) :=
  doors_agree hv k

theorem doors_agree_seven {v : Fin 7 → ℝ} (hv : Function.Injective v) (k : Fin 7) :
    (DoorFlank v k ↔ LonelyForSubject v k) ∧ (DoorArrives v k ↔ LonelyForSubject v k) ∧
    (DoorCapped v k ↔ LonelyForSubject v k) ∧ (DoorFAM v k ↔ LonelyForSubject v k) :=
  doors_agree hv k

#print axioms LRC.SpecN.doors_agree
#print axioms doors_agree_five
#print axioms doors_agree_six
#print axioms doors_agree_seven
#print axioms LRC.SpecN.doorFlank_iff
#print axioms LRC.SpecN.doorArrives_iff
#print axioms LRC.SpecN.doorCapped_iff
#print axioms LRC.SpecN.doorFAM_iff
#print axioms LRC.SpecN.lonelyRunnerAtN_of_doorArrives
