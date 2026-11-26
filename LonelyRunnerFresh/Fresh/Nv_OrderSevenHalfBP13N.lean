-- PORTED 2026-10-25 (imports renamed only) from LonelyRunner/LonelyRunner/LRC/Spec/OrderSevenHalfBP13N.lean
import Fresh.Nv_OrderSevenHalfCoreN

/-! Order seven half-unit certificate B, part 13: 2 pieces, 354900 checks. -/

namespace LRC.O7L3

theorem chunkBH_17_17 : chunkBH 17 17 147 = true := by decide +kernel
theorem chunkBH_18_18 : chunkBH 18 18 147 = true := by decide +kernel

end LRC.O7L3
