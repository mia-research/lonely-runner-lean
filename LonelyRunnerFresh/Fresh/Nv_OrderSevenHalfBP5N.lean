-- PORTED 2026-10-25 (imports renamed only) from LonelyRunner/LonelyRunner/LRC/Spec/OrderSevenHalfBP5N.lean
import Fresh.Nv_OrderSevenHalfCoreN

/-! Order seven half-unit certificate B, part 5: 1 pieces, 213213 checks. -/

namespace LRC.O7L3

theorem chunkBH_5_5 : chunkBH 5 5 147 = true := by decide +kernel

end LRC.O7L3
