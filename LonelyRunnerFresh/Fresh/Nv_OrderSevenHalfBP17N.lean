-- PORTED 2026-10-25 (imports renamed only) from LonelyRunner/LonelyRunner/LRC/Spec/OrderSevenHalfBP17N.lean
import Fresh.Nv_OrderSevenHalfCoreN

/-! Order seven half-unit certificate B, part 17: 2 pieces, 312564 checks. -/

namespace LRC.O7L3

theorem chunkBH_25_25 : chunkBH 25 25 147 = true := by decide +kernel
theorem chunkBH_26_26 : chunkBH 26 26 147 = true := by decide +kernel

end LRC.O7L3
