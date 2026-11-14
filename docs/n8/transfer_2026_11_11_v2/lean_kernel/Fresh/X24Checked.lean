import Lean
import X24Compute

namespace Fresh.X24Replay

/-- Closed arithmetic replay for the complete wider X24 band. -/
theorem wideCheck : (List.range' 1 25).all checkFirst = true := by
  native_decide

#print axioms wideCheck

end Fresh.X24Replay
