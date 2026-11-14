import Lean.Elab.Tactic.Decide
import HarmonicCompute

namespace Fresh.Harmonic

theorem four_catalogue_checked : fourCatalogueCheck = true := by native_decide
theorem five_frontier_checked : fiveFrontierCheck = true := by native_decide
theorem append_slopes_checked : appendSlopeCheck = true := by native_decide

#print axioms four_catalogue_checked
#print axioms five_frontier_checked
#print axioms append_slopes_checked
end Fresh.Harmonic
