import LonelyRunner.LRC.Spec.OrderSevenU5RootN
import LonelyRunner.LRC.Spec.OrderSevenU5Blk0N
import LonelyRunner.LRC.Spec.OrderSevenU5Blk1N
import LonelyRunner.LRC.Spec.OrderSevenU5Blk2N
import LonelyRunner.LRC.Spec.OrderSevenU5Blk3N
import LonelyRunner.LRC.Spec.OrderSevenU5Blk4N
import LonelyRunner.LRC.Spec.OrderSevenU5Blk5N
import LonelyRunner.LRC.Spec.OrderSevenU5Blk6N
import LonelyRunner.LRC.Spec.OrderSevenU5Cap0N
import LonelyRunner.LRC.Spec.OrderSevenU5Cap1N
import LonelyRunner.LRC.Spec.OrderSevenU5Cap2N
import LonelyRunner.LRC.Spec.OrderSevenU5ClsN
import LonelyRunner.LRC.Spec.OrderSevenU5Dom0N
import LonelyRunner.LRC.Spec.OrderSevenU5Dom1N
import LonelyRunner.LRC.Spec.OrderSevenU5Dom2N
import LonelyRunner.LRC.Spec.OrderSevenU5Dom3N
import LonelyRunner.LRC.Spec.OrderSevenU5Dom4N
import LonelyRunner.LRC.Spec.OrderSevenU5Dom5N
import LonelyRunner.LRC.Spec.OrderSevenU5Dom6N

/-!
# AbsU5 proved

`absU5 : LRC.O7Abs.AbsU5`: runner 1 and any four unit abstract states share an instant `c (1 + 7^(a-2) s)`.
Proof: every abstract state contains a table state (`dom_all`); any four table states share a good instant
inside runner 1's 210 (`claim_full_four`, from the branch-and-bound certificate); runner 1 is in band at each of
its instants (`r1P`).  Table facts: `blkSpec`, `capSpec`, `clsSpec`.  No `sorry`, no `native_decide`.
-/

namespace LRC.O7U5
open LRC.O7Abs

theorem blkSpec : BlkSpec := by
  intro x hx k hk
  by_cases h0 : x < 30
  · exact blk_of blkP0 (by omega) h0 hk
  by_cases h1 : x < 60
  · exact blk_of blkP1 (by omega) h1 hk
  by_cases h2 : x < 90
  · exact blk_of blkP2 (by omega) h2 hk
  by_cases h3 : x < 120
  · exact blk_of blkP3 (by omega) h3 hk
  by_cases h4 : x < 150
  · exact blk_of blkP4 (by omega) h4 hk
  by_cases h5 : x < 180
  · exact blk_of blkP5 (by omega) h5 hk
  exact blk_of blkP6 (by omega) (by omega) hk

theorem capSpec : CapSpec := by
  intro c hc k hk
  have hNS : NS = 8014 := rfl
  have hj : k / 128 < 63 := by omega
  generalize hjv : k / 128 = j at hj
  interval_cases j
  · exact cap_of capJ0 (by omega) (by omega) hk hc
  · exact cap_of capJ1 (by omega) (by omega) hk hc
  · exact cap_of capJ2 (by omega) (by omega) hk hc
  · exact cap_of capJ3 (by omega) (by omega) hk hc
  · exact cap_of capJ4 (by omega) (by omega) hk hc
  · exact cap_of capJ5 (by omega) (by omega) hk hc
  · exact cap_of capJ6 (by omega) (by omega) hk hc
  · exact cap_of capJ7 (by omega) (by omega) hk hc
  · exact cap_of capJ8 (by omega) (by omega) hk hc
  · exact cap_of capJ9 (by omega) (by omega) hk hc
  · exact cap_of capJ10 (by omega) (by omega) hk hc
  · exact cap_of capJ11 (by omega) (by omega) hk hc
  · exact cap_of capJ12 (by omega) (by omega) hk hc
  · exact cap_of capJ13 (by omega) (by omega) hk hc
  · exact cap_of capJ14 (by omega) (by omega) hk hc
  · exact cap_of capJ15 (by omega) (by omega) hk hc
  · exact cap_of capJ16 (by omega) (by omega) hk hc
  · exact cap_of capJ17 (by omega) (by omega) hk hc
  · exact cap_of capJ18 (by omega) (by omega) hk hc
  · exact cap_of capJ19 (by omega) (by omega) hk hc
  · exact cap_of capJ20 (by omega) (by omega) hk hc
  · exact cap_of capJ21 (by omega) (by omega) hk hc
  · exact cap_of capJ22 (by omega) (by omega) hk hc
  · exact cap_of capJ23 (by omega) (by omega) hk hc
  · exact cap_of capJ24 (by omega) (by omega) hk hc
  · exact cap_of capJ25 (by omega) (by omega) hk hc
  · exact cap_of capJ26 (by omega) (by omega) hk hc
  · exact cap_of capJ27 (by omega) (by omega) hk hc
  · exact cap_of capJ28 (by omega) (by omega) hk hc
  · exact cap_of capJ29 (by omega) (by omega) hk hc
  · exact cap_of capJ30 (by omega) (by omega) hk hc
  · exact cap_of capJ31 (by omega) (by omega) hk hc
  · exact cap_of capJ32 (by omega) (by omega) hk hc
  · exact cap_of capJ33 (by omega) (by omega) hk hc
  · exact cap_of capJ34 (by omega) (by omega) hk hc
  · exact cap_of capJ35 (by omega) (by omega) hk hc
  · exact cap_of capJ36 (by omega) (by omega) hk hc
  · exact cap_of capJ37 (by omega) (by omega) hk hc
  · exact cap_of capJ38 (by omega) (by omega) hk hc
  · exact cap_of capJ39 (by omega) (by omega) hk hc
  · exact cap_of capJ40 (by omega) (by omega) hk hc
  · exact cap_of capJ41 (by omega) (by omega) hk hc
  · exact cap_of capJ42 (by omega) (by omega) hk hc
  · exact cap_of capJ43 (by omega) (by omega) hk hc
  · exact cap_of capJ44 (by omega) (by omega) hk hc
  · exact cap_of capJ45 (by omega) (by omega) hk hc
  · exact cap_of capJ46 (by omega) (by omega) hk hc
  · exact cap_of capJ47 (by omega) (by omega) hk hc
  · exact cap_of capJ48 (by omega) (by omega) hk hc
  · exact cap_of capJ49 (by omega) (by omega) hk hc
  · exact cap_of capJ50 (by omega) (by omega) hk hc
  · exact cap_of capJ51 (by omega) (by omega) hk hc
  · exact cap_of capJ52 (by omega) (by omega) hk hc
  · exact cap_of capJ53 (by omega) (by omega) hk hc
  · exact cap_of capJ54 (by omega) (by omega) hk hc
  · exact cap_of capJ55 (by omega) (by omega) hk hc
  · exact cap_of capJ56 (by omega) (by omega) hk hc
  · exact cap_of capJ57 (by omega) (by omega) hk hc
  · exact cap_of capJ58 (by omega) (by omega) hk hc
  · exact cap_of capJ59 (by omega) (by omega) hk hc
  · exact cap_of capJ60 (by omega) (by omega) hk hc
  · exact cap_of capJ61 (by omega) (by omega) hk hc
  · exact cap_of capJ62 (by omega) (by omega) hk hc


theorem clsSpec : ClassSpec ∧ CBSpec := cls_of clsP

theorem dom_all {T : Nat} (hT : T < 49) {gi ri : Nat} (hg : gi < 12) (hr : ri < 42) :
    ∃ k, k < NS ∧ ∀ x, x < 210 → (MT k).testBit x = true →
      ok T (fvecs.getD gi []) (units49L.getD ri 0) (inst x).1 (inst x).2 := by
  interval_cases T
  · exact dom_of domP0 hg hr
  · exact dom_of domP1 hg hr
  · exact dom_of domP2 hg hr
  · exact dom_of domP3 hg hr
  · exact dom_of domP4 hg hr
  · exact dom_of domP5 hg hr
  · exact dom_of domP6 hg hr
  · exact dom_of domP7 hg hr
  · exact dom_of domP8 hg hr
  · exact dom_of domP9 hg hr
  · exact dom_of domP10 hg hr
  · exact dom_of domP11 hg hr
  · exact dom_of domP12 hg hr
  · exact dom_of domP13 hg hr
  · exact dom_of domP14 hg hr
  · exact dom_of domP15 hg hr
  · exact dom_of domP16 hg hr
  · exact dom_of domP17 hg hr
  · exact dom_of domP18 hg hr
  · exact dom_of domP19 hg hr
  · exact dom_of domP20 hg hr
  · exact dom_of domP21 hg hr
  · exact dom_of domP22 hg hr
  · exact dom_of domP23 hg hr
  · exact dom_of domP24 hg hr
  · exact dom_of domP25 hg hr
  · exact dom_of domP26 hg hr
  · exact dom_of domP27 hg hr
  · exact dom_of domP28 hg hr
  · exact dom_of domP29 hg hr
  · exact dom_of domP30 hg hr
  · exact dom_of domP31 hg hr
  · exact dom_of domP32 hg hr
  · exact dom_of domP33 hg hr
  · exact dom_of domP34 hg hr
  · exact dom_of domP35 hg hr
  · exact dom_of domP36 hg hr
  · exact dom_of domP37 hg hr
  · exact dom_of domP38 hg hr
  · exact dom_of domP39 hg hr
  · exact dom_of domP40 hg hr
  · exact dom_of domP41 hg hr
  · exact dom_of domP42 hg hr
  · exact dom_of domP43 hg hr
  · exact dom_of domP44 hg hr
  · exact dom_of domP45 hg hr
  · exact dom_of domP46 hg hr
  · exact dom_of domP47 hg hr
  · exact dom_of domP48 hg hr

theorem wit_of {T : Nat} {g : List Nat} {ρ : Nat} (h : UnitSt T g ρ) :
    ∃ k, k < NS ∧ ∀ x, x < 210 → (MT k).testBit x = true → ok T g ρ (inst x).1 (inst x).2 := by
  obtain ⟨hT, hg, hρ, hρ7⟩ := h
  obtain ⟨gi, hgi, rfl⟩ := fvec_index hg
  obtain ⟨ri, hri, rfl⟩ := unit_index hρ hρ7
  exact dom_all hT hgi hri

/-- **AbsU5**, proved: five units share an instant of the depth-two fold at every level `a ≥ 3`
(with `LRC.O7Abs.units_all`). -/
theorem absU5 : AbsU5 := by
  intro T2 g2 ρ2 T3 g3 ρ3 T4 g4 ρ4 T5 g5 ρ5 h2 h3 h4 h5
  obtain ⟨k2, hk2, w2⟩ := wit_of h2
  obtain ⟨k3, hk3, w3⟩ := wit_of h3
  obtain ⟨k4, hk4, w4⟩ := wit_of h4
  obtain ⟨k5, hk5, w5⟩ := wit_of h5
  obtain ⟨x, hx, -, hks⟩ := claim_full_four blkSpec capSpec clsSpec.1 clsSpec.2 [k2, k3, k4, k5] rfl
    (by intro k hk; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> assumption)
  obtain ⟨r1, hc1, hc6⟩ := r1_of r1P hx
  exact ⟨(inst x).1, (inst x).2, hc1, hc6, r1, w2 x hx (hks k2 (by simp)), w3 x hx (hks k3 (by simp)),
    w4 x hx (hks k4 (by simp)), w5 x hx (hks k5 (by simp))⟩

end LRC.O7U5
