import LonelyRunner.LRC.Spec.OrderSevenBox6Tree12P0N
import LonelyRunner.LRC.Spec.OrderSevenBox6Tree12P1N
import LonelyRunner.LRC.Spec.OrderSevenBox6Tree12P2N

/-!
# Order seven on `v1 ≥ v6 · 1/12`, `v5 ≥ v6 · 1/6` (kernel-checked six-runner box tree, 3 parts)

Skeleton and assembly; the subtrees are checked in `OrderSevenBox6Tree12P*N`.  Tree from
`experiments/n7_native/o7_box6_exact_v2.py` (7572 nodes at leaf level, exact rationals, k/42 splitting).
-/

namespace LRC.O7Box6T12
open LRC.O7Box6 LRC.O7Box6.TS LRC.O7Split

noncomputable def all : List (T × Bx) := LRC.O7Box6T12P0.subs ++ LRC.O7Box6T12P1.subs ++ LRC.O7Box6T12P2.subs

def skel : TS := (S 0 23 42 (S 1 23 42 (S 2 23 42 (S 3 23 42 (Sub 0) (Sub 1)) (Sub 2)) (Sub 3)) (Sub 4))

theorem skel_ok : skelOK skel (root (1 / 12) (1 / 6)) all = true := by decide +kernel

theorem all_ok : all.all (fun p => check p.1 p.2) = true := by
  simp only [all, List.all_append, LRC.O7Box6T12P0.subs_ok, LRC.O7Box6T12P1.subs_ok, LRC.O7Box6T12P2.subs_ok, Bool.and_self]

theorem win : ∀ x, Mem (root (1 / 12) (1 / 6)) x → Inst x := split_sound skel_ok all_ok

/-- **Order seven on the box.** -/
theorem lonely {v1 v2 v3 v4 v5 v6 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4)
    (h45 : v4 < v5) (h56 : v5 < v6) (hX : ((1 / 12 : ℚ) : ℝ) * v6 ≤ v1) (hY : ((1 / 6 : ℚ) : ℝ) * v6 ≤ v5) :
    ∃ t : ℝ, ∀ d ∈ ({v1, v2, v3, v4, v5, v6} : Finset ℕ), (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * t) :=
  lonely_of_inst win h0 h12 h23 h34 h45 h56 hX hY

end LRC.O7Box6T12
