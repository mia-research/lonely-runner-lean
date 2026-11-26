-- PORTED 2026-10-25 (imports renamed only) from LonelyRunner/LonelyRunner/LRC/Spec/OrderSevenHalfBP2N.lean
import Fresh.Nv_OrderSevenHalfCoreN

/-! Order seven half-unit certificate B, part 2: 1 pieces, 222285 checks. -/

namespace LRC.O7L3

theorem chunkBH_2_2 : chunkBH 2 2 147 = true := by decide +kernel

end LRC.O7L3
