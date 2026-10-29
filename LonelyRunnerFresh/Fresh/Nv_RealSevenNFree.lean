-- BS-free 2026-10-29: order seven real speeds from the native certificate proof.  Keeps the namespace of the original so dependent copies need no renaming.
import Fresh.Nv_OrderSevenNativeN
import Fresh.Nv_RealSixN

namespace LRC.OrderSevenN

open LRC.SpecN

theorem existenceAtN_seven : ExistenceAtN 7 := LRC.OrderSevenNative.existenceAtN_seven

theorem lonelyRunnerAtN_seven : LonelyRunnerAtN 7 := LRC.OrderSevenNative.lonelyRunnerAtN_seven

end LRC.OrderSevenN
