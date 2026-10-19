import LonelyRunner.LRC.Spec.OrderSevenU5TabN
import LonelyRunner.LRC.Spec.OrderSevenP1DataN

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace LRC.O7U5
open LRC.O7Abs

def zdomB (T : Nat) (zs : List Nat) : Bool := allB 12 0 (fun gi => allB 6 0 (fun ri =>
  decide (zs.getD (6 * gi + ri) 0 < 252) &&
    walk (UB (zs.getD (6 * gi + ri) 0)) T (fvecs.getD gi []) (7 * (ri + 1)) 0 instTab))

theorem zdom_of {T : Nat} {zs : List Nat} (h : zdomB T zs = true) {gi ri : Nat} (hg : gi < 12) (hr : ri < 6) :
    ∃ b, b < 252 ∧ ∀ x, x < 210 → (UB b).testBit x = true →
      ok T (fvecs.getD gi []) (7 * (ri + 1)) (inst x).1 (inst x).2 := by
  have := allB_spec2 h hg hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨_, this.1, fun x hx hm => ?_⟩
  have hw := walk_spec 0 instTab this.2 x (by rw [instTab_len]; exact hx) (by simpa using hm)
  rw [inst_eq hx]; exact hw

end LRC.O7U5
