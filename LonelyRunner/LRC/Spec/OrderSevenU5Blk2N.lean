import LonelyRunner.LRC.Spec.OrderSevenU5TabN

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace LRC.O7U5

theorem blkP2 : blkB 60 90 = true := by decide +kernel

end LRC.O7U5
