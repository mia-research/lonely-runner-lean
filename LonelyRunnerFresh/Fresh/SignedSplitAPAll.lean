import Fresh.SignedSplitAP
import Fresh.SignedSplitMiddle

/-! Both signed packet directions and all middle offsets are now supplied.
This law includes interleaved two-AP readings for every noninteger offset.
[PROVISIONAL: counting tool] inherited integer grid placement.
[PROVISIONAL: covering] explicit finite middle parameter splits.
-/
namespace Fresh.SplitAPBands
open Fresh

theorem signed_split_train_noninteger (r : ℕ) (hr1 : 1 ≤ r) (hr5 : r ≤ 5)
    (B : ℝ) (hnot : ∀ m : ℤ, B ≠ (m : ℝ)) :
    ∃ t : ℝ, 0<t ∧ ∀ d ∈ splitTrain r B, (1/8 : ℝ) ≤ distInt (d*t) := by
  apply signed_split_noninteger_of_middle ?_ r hr1 hr5 B hnot
  intro r hr1 hr3 m B hmlo hmhi hlo hhi
  apply signed_split_middle r hr1 hr3 m ?_ hmhi B hlo hhi
  omega

#print axioms signed_split_train_noninteger
end Fresh.SplitAPBands
