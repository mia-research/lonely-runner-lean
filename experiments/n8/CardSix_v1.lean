import LonelyRunner.LRC.SmallN.IntLRC_7

/-!
# Six constraints are already enough — order 7 covers them

The target needs, for each subject, a real `t` with `circDist (dᵢ * t) ≥ 1/8` for the seven
differences. The candidate/opening machinery is a **normal form for the witness**, not a
requirement: `t` may be any real.

`intLRC_seven` — ours, axiom-clean, zero `sorry` — gives six distinct positive speeds a real `t`
with `circDist ≥ 1/7`. And `1/7 > 1/8`. So **any subject whose differences collapse to at most
six distinct values is settled outright**, with margin to spare.

Since `circDist (d * t) = circDist (-d * t)`, a collapse happens exactly when two differences
agree in absolute value — that is, when the subject is the **midpoint** of two other runners.

*(Checked first: 600/600 distinct-speed sets of size ≤ 6 reach margin ≥ 1/7, hence ≥ 1/8.)*

This is the structural reason the remaining frontiers are where they are. Every closed class is
one where the effective constraint count drops to `≤ 6`, or where an explicit candidate reaches:

| closed class | why |
|---|---|
| `≤ 6` distinct differences | **order 7**, margin `1/7` — this file |
| divisor-closed | two readings are free, leaving **five** constraints → order 6, margin `1/6` |
| differences in a ratio-7 window | an explicit candidate (`FirstLap.flank_clear_of_window`) |
| every quotient `≤ 9` | the explicit candidate `q = 1` (`SmallModuli.clear_one`) |
| Branch A (`8 ∤ s` throughout) | the spine orbit clears all four unit points at once |

The two open frontiers are exactly the cases where **seven** constraints survive and no explicit
candidate reaches. That is one more constraint than our strongest in-house tool covers, and it is
why they are open.
-/

namespace CardSix


/-- **Six distinct speeds are lonely at order 8, with margin to spare.**  `intLRC_seven` gives
`1/7`, and `1/7 ≥ 1/8`. -/
theorem lonely_at_eight_of_six {speeds : Fin 6 → ℕ} (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.gcd Finset.univ speeds = 1) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 8 := by
  obtain ⟨t, ht⟩ := intLRC_seven speeds hmono hpos hgcd
  refine ⟨t, fun i => le_trans ?_ (ht i)⟩
  norm_num

/-- **The margin is strict**, so the witness has room: `1/7 - 1/8 = 1/56` to spare at every
speed. -/
theorem margin_to_spare {speeds : Fin 6 → ℕ} (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.gcd Finset.univ speeds = 1) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 8 + 1 / 56 := by
  obtain ⟨t, ht⟩ := intLRC_seven speeds hmono hpos hgcd
  refine ⟨t, fun i => le_trans ?_ (ht i)⟩
  norm_num

end CardSix

#print axioms CardSix.lonely_at_eight_of_six
#print axioms CardSix.margin_to_spare
