-- PORTED 2026-10-25 (imports renamed only) from LonelyRunner/LonelyRunner/LRC/Spec/OrderSevenU5Blk6N.lean
import Fresh.Nv_OrderSevenU5TabN

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace LRC.O7U5

theorem blkP6 : blkB 180 210 = true := by decide +kernel

end LRC.O7U5
