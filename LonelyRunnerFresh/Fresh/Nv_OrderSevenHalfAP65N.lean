-- PORTED 2026-10-25 (imports renamed only) from LonelyRunner/LonelyRunner/LRC/Spec/OrderSevenHalfAP65N.lean
import Fresh.Nv_OrderSevenHalfCoreN

/-! Order seven half-unit certificate A, part 65: 3 pieces, 307105 checks. -/

namespace LRC.O7L3

theorem chunkAH_62_62 : chunkAH 62 62 147 = true := by decide +kernel
theorem chunkAH_63_63 : chunkAH 63 63 147 = true := by decide +kernel
theorem chunkAH_64_64 : chunkAH 64 64 147 = true := by decide +kernel

end LRC.O7L3
