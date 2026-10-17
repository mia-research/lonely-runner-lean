import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P0N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P1N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P2N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P3N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P4N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P5N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P6N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P7N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P8N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P9N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P10N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P11N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P12N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P13N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P14N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P15N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P16N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P17N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P18N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P19N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P20N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P21N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P22N
import LonelyRunner.LRC.Spec.OrderSevenKappaTree100P23N

/-!
# Order seven: `kappa ≥ 3/28` for `v1 ≥ v5 · 1/100` (kernel-checked box tree, 24 parts)

Skeleton and assembly; the subtrees are checked in `OrderSevenKappaTree100P*N`.  Tree from
`experiments/n7_native/o7_kbox_exact_v2.py` (50572 leaves, exact rationals, sevenths splitting).
-/

namespace LRC.O7KTree100
open LRC.O7KTree LRC.O7KTree.TS LRC.O7Split

noncomputable def all : List (T × Bx) := LRC.O7KTree100P0.subs ++ LRC.O7KTree100P1.subs ++ LRC.O7KTree100P2.subs ++ LRC.O7KTree100P3.subs ++ LRC.O7KTree100P4.subs ++ LRC.O7KTree100P5.subs ++ LRC.O7KTree100P6.subs ++ LRC.O7KTree100P7.subs ++ LRC.O7KTree100P8.subs ++ LRC.O7KTree100P9.subs ++ LRC.O7KTree100P10.subs ++ LRC.O7KTree100P11.subs ++ LRC.O7KTree100P12.subs ++ LRC.O7KTree100P13.subs ++ LRC.O7KTree100P14.subs ++ LRC.O7KTree100P15.subs ++ LRC.O7KTree100P16.subs ++ LRC.O7KTree100P17.subs ++ LRC.O7KTree100P18.subs ++ LRC.O7KTree100P19.subs ++ LRC.O7KTree100P20.subs ++ LRC.O7KTree100P21.subs ++ LRC.O7KTree100P22.subs ++ LRC.O7KTree100P23.subs

def skel : TS := (S 0 (S 1 (S 2 (S 3 (S 0 (S 1 (S 2 (S 3 (Sub 0) (S 3 (Sub 1) (Sub 2))) (S 3 (Sub 3) (S 2 (Sub 4) (Sub 5)))) (Sub 6)) (Sub 7)) (S 0 (S 1 (S 2 (S 3 (Sub 8) (S 3 (Sub 9) (Sub 10))) (S 3 (Sub 11) (S 2 (Sub 12) (Sub 13)))) (S 2 (Sub 14) (S 3 (Sub 15) (S 1 (Sub 16) (Sub 17))))) (Sub 18))) (S 3 (Sub 19) (S 0 (S 1 (S 2 (S 3 (Sub 20) (Sub 21)) (S 3 (Sub 22) (S 2 (Sub 23) (Sub 24)))) (S 2 (S 3 (Sub 25) (S 1 (Sub 26) (Sub 27))) (S 3 (Sub 28) (S 1 (Sub 29) (Sub 30))))) (Sub 31)))) (S 2 (Sub 32) (S 3 (Sub 33) (S 0 (S 1 (S 2 (Sub 34) (Sub 35)) (Sub 36)) (Sub 37))))) (Sub 38))

theorem skel_ok : skelOK skel (root (1 / 100)) all = true := by decide +kernel

theorem all_ok : all.all (fun p => check p.1 p.2) = true := by
  simp only [all, List.all_append, LRC.O7KTree100P0.subs_ok, LRC.O7KTree100P1.subs_ok, LRC.O7KTree100P2.subs_ok, LRC.O7KTree100P3.subs_ok, LRC.O7KTree100P4.subs_ok, LRC.O7KTree100P5.subs_ok, LRC.O7KTree100P6.subs_ok, LRC.O7KTree100P7.subs_ok, LRC.O7KTree100P8.subs_ok, LRC.O7KTree100P9.subs_ok, LRC.O7KTree100P10.subs_ok, LRC.O7KTree100P11.subs_ok, LRC.O7KTree100P12.subs_ok, LRC.O7KTree100P13.subs_ok, LRC.O7KTree100P14.subs_ok, LRC.O7KTree100P15.subs_ok, LRC.O7KTree100P16.subs_ok, LRC.O7KTree100P17.subs_ok, LRC.O7KTree100P18.subs_ok, LRC.O7KTree100P19.subs_ok, LRC.O7KTree100P20.subs_ok, LRC.O7KTree100P21.subs_ok, LRC.O7KTree100P22.subs_ok, LRC.O7KTree100P23.subs_ok, Bool.and_self]

theorem win : ∀ x, Mem (root (1 / 100)) x → Win x := split_sound skel_ok all_ok

/-- **`kappa ≥ 3/28` for `1/100 · v5 ≤ v1`.** -/
theorem kappa {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 < v5)
    (hX : ((1 / 100 : ℚ) : ℝ) * v5 ≤ v1) :
    ∃ s₀ : ℝ, InBandOn {v1, v2, v3, v4, v5} (Set.Icc s₀ (s₀ + 3 / (28 * v5))) :=
  kappa_of_win win h0 h12 h23 h34 h45 hX

end LRC.O7KTree100
