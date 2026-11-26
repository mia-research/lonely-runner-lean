-- PORTED 2026-10-25 (imports renamed only) from LonelyRunner/LonelyRunner/LRC/Spec/OrderSevenHalfCP2N.lean
import Fresh.Nv_OrderSevenHalfCoreN

/-! Order seven half-unit certificate C2, part 2: failing tuples 14..14. -/

namespace LRC.O7L3

theorem chunkC2_14 : chunkC2 14 = true := by decide +kernel

end LRC.O7L3
