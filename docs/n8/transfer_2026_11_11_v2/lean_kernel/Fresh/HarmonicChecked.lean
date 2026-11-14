import Lean
import HarmonicCompute

namespace Fresh.Harmonic

theorem five_checked : fiveCheck = true := by native_decide
theorem six_checked : sixCheck = true := by native_decide

#print axioms five_checked
#print axioms six_checked
end Fresh.Harmonic
