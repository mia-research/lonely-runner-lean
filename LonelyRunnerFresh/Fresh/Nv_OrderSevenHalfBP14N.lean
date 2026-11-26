-- PORTED 2026-10-25 (imports renamed only) from LonelyRunner/LonelyRunner/LRC/Spec/OrderSevenHalfBP14N.lean
import Fresh.Nv_OrderSevenHalfCoreN

/-! Order seven half-unit certificate B, part 14: 2 pieces, 344064 checks. -/

namespace LRC.O7L3

theorem chunkBH_19_19 : chunkBH 19 19 147 = true := by decide +kernel
theorem chunkBH_20_20 : chunkBH 20 20 147 = true := by decide +kernel

end LRC.O7L3
