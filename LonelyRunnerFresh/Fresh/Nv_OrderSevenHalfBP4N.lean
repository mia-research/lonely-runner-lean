-- PORTED 2026-10-25 (imports renamed only) from LonelyRunner/LonelyRunner/LRC/Spec/OrderSevenHalfBP4N.lean
import Fresh.Nv_OrderSevenHalfCoreN

/-! Order seven half-unit certificate B, part 4: 1 pieces, 216216 checks. -/

namespace LRC.O7L3

theorem chunkBH_4_4 : chunkBH 4 4 147 = true := by decide +kernel

end LRC.O7L3
