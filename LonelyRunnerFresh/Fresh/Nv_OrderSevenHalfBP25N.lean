-- PORTED 2026-10-25 (imports renamed only) from LonelyRunner/LonelyRunner/LRC/Spec/OrderSevenHalfBP25N.lean
import Fresh.Nv_OrderSevenHalfCoreN

/-! Order seven half-unit certificate B, part 25: 3 pieces, 330960 checks. -/

namespace LRC.O7L3

theorem chunkBH_44_44 : chunkBH 44 44 147 = true := by decide +kernel
theorem chunkBH_45_45 : chunkBH 45 45 147 = true := by decide +kernel
theorem chunkBH_46_46 : chunkBH 46 46 147 = true := by decide +kernel

end LRC.O7L3
