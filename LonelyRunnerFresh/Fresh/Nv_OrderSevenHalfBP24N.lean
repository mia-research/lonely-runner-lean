-- PORTED 2026-10-25 (imports renamed only) from LonelyRunner/LonelyRunner/LRC/Spec/OrderSevenHalfBP24N.lean
import Fresh.Nv_OrderSevenHalfCoreN

/-! Order seven half-unit certificate B, part 24: 3 pieces, 350616 checks. -/

namespace LRC.O7L3

theorem chunkBH_41_41 : chunkBH 41 41 147 = true := by decide +kernel
theorem chunkBH_42_42 : chunkBH 42 42 147 = true := by decide +kernel
theorem chunkBH_43_43 : chunkBH 43 43 147 = true := by decide +kernel

end LRC.O7L3
