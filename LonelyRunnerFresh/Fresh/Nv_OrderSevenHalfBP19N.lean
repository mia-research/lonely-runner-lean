-- PORTED 2026-10-25 (imports renamed only) from LonelyRunner/LonelyRunner/LRC/Spec/OrderSevenHalfBP19N.lean
import Fresh.Nv_OrderSevenHalfCoreN

/-! Order seven half-unit certificate B, part 19: 2 pieces, 292404 checks. -/

namespace LRC.O7L3

theorem chunkBH_29_29 : chunkBH 29 29 147 = true := by decide +kernel
theorem chunkBH_30_30 : chunkBH 30 30 147 = true := by decide +kernel

end LRC.O7L3
