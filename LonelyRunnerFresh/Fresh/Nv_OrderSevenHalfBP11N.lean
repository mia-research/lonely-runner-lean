-- PORTED 2026-10-25 (imports renamed only) from LonelyRunner/LonelyRunner/LRC/Spec/OrderSevenHalfBP11N.lean
import Fresh.Nv_OrderSevenHalfCoreN

/-! Order seven half-unit certificate B, part 11: 2 pieces, 377076 checks. -/

namespace LRC.O7L3

theorem chunkBH_13_13 : chunkBH 13 13 147 = true := by decide +kernel
theorem chunkBH_14_14 : chunkBH 14 14 147 = true := by decide +kernel

end LRC.O7L3
