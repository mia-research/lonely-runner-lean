-- PORTED 2026-10-25 (imports renamed only) from LonelyRunner/LonelyRunner/LRC/Spec/OrderSevenHalfBP20N.lean
import Fresh.Nv_OrderSevenHalfCoreN

/-! Order seven half-unit certificate B, part 20: 2 pieces, 282576 checks. -/

namespace LRC.O7L3

theorem chunkBH_31_31 : chunkBH 31 31 147 = true := by decide +kernel
theorem chunkBH_32_32 : chunkBH 32 32 147 = true := by decide +kernel

end LRC.O7L3
