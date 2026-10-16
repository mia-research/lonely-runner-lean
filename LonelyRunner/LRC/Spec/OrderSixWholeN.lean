import LonelyRunner.LRC.Spec.OrderSixSecFiveEN
import LonelyRunner.LRC.Spec.OrderSixSixN
import LonelyRunner.LRC.Spec.OrderSixSecSevenCasesN
import LonelyRunner.LRC.Spec.OrderFiveResidualN
import LonelyRunner.LRC.Spec.OrderSixSecSevenNativeN
import LonelyRunner.LRC.Spec.OrderSixEightNativeN

/-!
# Order six on whole numbers: the four BHK cases, dispatched

2026-09-24.  Five whole-number speeds `v₁ < ⋯ < v₅`, `D = v₃ − v₂`:

* `v₃ ≤ 3v₁`                      — §8, `S8Native.lonely_8_native` (2026-10-16; slow-block windows, the
  four-runner fold and lap boxes, closed by a kernel-checked cell certificate). BHK's form `lonely_8` is kept.
* `3v₁ < v₃`, `D ∣ v₁`             — §5, `lonely_5` (Proposition 11 at named instants);
* `3v₁ < v₃`, `D ∣ v₃`, `D ∤ v₁`   — §6, `lonely_6`;
* `3v₁ < v₃`, `D ∤ v₃`, `D ∤ v₁`   — §7, `S7Native.lonely_7_native` (2026-10-16; the native route: 2D global
  isolation on the meeting-time orbit, the two-runner window lemma, `G₄`/`G₇` closed by boxes and windows).
  BHK's form `S7.lonely_7` is kept and still proved.

These cover every case, so every set of at most five positive whole numbers is lonely at `1/6`
(`lonely_six_nat`); four or fewer are lonely at `1/5` already (`lonely_five_nat`).  No primitivity.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.style.longLine false

namespace LRC.OrderSixN

open MomentIterationN LRC.SpecN ConstructionN

/-- **The four cases.**  Five increasing positive whole numbers are lonely at `1/6`. -/
theorem lonely6_of_lt {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3)
    (h34 : v3 < v4) (h45 : v4 < v5) : ∃ t : ℝ, 0 < t ∧ Lonely6 v1 v2 v3 v4 v5 t := by
  by_cases hlarge : v3 ≤ 3 * v1
  · exact LRC.S8Native.lonely_8_native h0 h12 h23 h34 h45 hlarge
  push_neg at hlarge
  by_cases hD1 : (v3 - v2) ∣ v1
  · exact S7.Named.lonely_5 h0 h12 h23 h34 h45 hlarge hD1
  by_cases hD3 : (v3 - v2) ∣ v3
  · exact lonely_6 h0 h12 h23 h34 h45 hlarge hD3 hD1
  · exact LRC.S7Native.lonely_7_native h0 h12 h23 h34 h45 hlarge hD3 hD1

/-- **Order six on whole numbers.**  At most five positive whole numbers are lonely at `1/6`. -/
theorem lonely_six_nat (S : Finset ℕ) (hpos : ∀ d ∈ S, 0 < d) (hcard : S.card ≤ 5) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (6 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  rcases Nat.lt_or_ge S.card 5 with h4 | h5
  · obtain ⟨t, ht, hl⟩ := LRC.OrderFiveN.lonely_five_nat S hpos (by omega)
    exact ⟨t, ht, fun d hd => le_trans (by norm_num) (hl d hd)⟩
  have h5 : S.card = 5 := le_antisymm hcard h5
  set f := S.orderEmbOfFin h5 with hf
  have hmem : ∀ i, f i ∈ S := fun i => S.orderEmbOfFin_mem h5 i
  have hlt : ∀ i j : Fin 5, i < j → f i < f j := fun i j h => f.strictMono h
  obtain ⟨t, ht, c1, c2, c3, c4, c5⟩ := lonely6_of_lt (hpos _ (hmem 0))
    (hlt 0 1 (by decide)) (hlt 1 2 (by decide)) (hlt 2 3 (by decide)) (hlt 3 4 (by decide))
  refine ⟨t, ht, fun d hd => ?_⟩
  have hrange : d ∈ Set.range f := by
    rw [Finset.range_orderEmbOfFin]; exact hd
  obtain ⟨i, rfl⟩ := hrange
  rw [inv_eq_one_div]
  fin_cases i
  · exact c1
  · exact c2
  · exact c3
  · exact c4
  · exact c5

end LRC.OrderSixN
