-- PORTED 2026-10-25 (imports renamed only) from LonelyRunner/LonelyRunner/LRC/Spec/OrderSevenHalfBP12N.lean
import Fresh.Nv_OrderSevenHalfCoreN

/-! Order seven half-unit certificate B, part 12: 2 pieces, 365904 checks. -/

namespace LRC.O7L3

theorem chunkBH_15_15 : chunkBH 15 15 147 = true := by decide +kernel
theorem chunkBH_16_16 : chunkBH 16 16 147 = true := by decide +kernel

end LRC.O7L3
