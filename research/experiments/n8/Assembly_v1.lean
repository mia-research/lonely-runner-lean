import LonelyRunner.LRC.Spec.Doors

/-! # The assembly: every proved link chained, and what is left

This file puts the chain together in Lean rather than in prose, so the compiler adjudicates what the
parts do and do not reach.  It imports only the tree; it invents nothing.

The chain, each link a theorem already in the artefacts:

```
LonelyRunnerAt8
  ← lonelyRunnerAt8_of_doorFlank        (Spec/Doors.lean)
  ← doorFlank_iff                       DoorFlank v k ↔ LonelyForSubject v k
  ← lonelyForSubject_iff_diffSet        ↔ ∃ s > 0, Lonely 8 (diffSet v k) s
  ← Flanks.lonely_iff_exists_flank      ↔ ∃ e ∈ ds, ∃ j, Lonely 8 ds (flankOpening 8 e j)
```

Composing them leaves `SomeFlankFree` below: for every arrangement and every subject, some flank of
that subject has a lonely opening — ROUTE_A_VERDICT_v1 §3's "no difference set has every flank
shadowed at once".

`someFlankFree_iff` proves the reduction is an **equivalence**, both directions, unconditional.  That
is the honest reading of the assembly: `SomeFlankFree` is not a weaker statement left over, it is
`LonelyRunnerAt8` in the flank vocabulary.  Nothing in this file discharges it.

What is discharged elsewhere, unconditionally, and therefore is not part of what remains:

* `Spec.exists_lonely_of_card_le_three`            — at most three distinct disparities
* `CardFour.exists_lonely_of_card_le_four`         — at most four (experiments/n8/CardFour_v1.lean)
* `ManyDifferences.stops_when_twice_card_lt`       — `2·card < n`; at `n = 8` this needs `card ≤ 3`
* `Flanks.lonely_opening_of_one_fractional`        — one non-integer ratio at a live flank
* `Flanks.essential_ratio_int`                     — a cover cannot be rationals plus exactly one
                                                     ratio of non-integer period product
* the census families (`EighthFamily`, `NearAP`, `CensusFamilies`, `PinnedBatch1–4`)

The residue those leave is the case ROUTE_A §1 names and `exists_clear_step` cannot see: **two or
more ratios of non-integer period product sharing a residue class.**
-/

namespace LRC.Spec

open Arrangement MomentIterationN Flanks

/-- **Some flank is always free.**  For every arrangement and every subject, one of that subject's
disparities hosts an opening at which the subject is lonely. -/
def SomeFlankFree : Prop :=
  ∀ v : Fin 8 → ℝ, Function.Injective v → ∀ k : Fin 8,
    ∃ e ∈ diffSet v k, ∃ j : ℕ, Lonely 8 (diffSet v k) (flankOpening 8 e j)

/-- **The assembly.**  Some flank always free gives the conjecture, through the chain above. -/
theorem lonelyRunnerAt8_of_someFlankFree (h : SomeFlankFree) : LonelyRunnerAt8 := by
  refine lonelyRunnerAt8_of_doorFlank ?_
  intro v hv k
  refine (doorFlank_iff hv k).mpr (lonelyForSubject_iff_diffSet.mpr ?_)
  obtain ⟨e, he, j, hj⟩ := h v hv k
  exact ⟨flankOpening 8 e j, flankOpening_pos (diffSet_pos hv k e he) j, hj⟩

/-- **And the converse**, so the reduction is not a weakening. -/
theorem someFlankFree_of_lonelyRunnerAt8 (h : LonelyRunnerAt8) : SomeFlankFree := by
  intro v hv k
  obtain ⟨s, hs, hl⟩ := lonelyForSubject_iff_diffSet.mp (h v hv k)
  exact (lonely_iff_exists_flank (n := 8) (diffSet_pos hv k)
    ⟨_, leastDisp_mem v k⟩).mp ⟨s, hs, hl⟩

/-- **The assembly, stated as what it is.**  `SomeFlankFree` is the conjecture in flank vocabulary —
equivalent to it, unconditionally, in both directions.  So the remaining work is to prove
`SomeFlankFree`, and no rearrangement of the proved links can do that. -/
theorem someFlankFree_iff : SomeFlankFree ↔ LonelyRunnerAt8 :=
  ⟨lonelyRunnerAt8_of_someFlankFree, someFlankFree_of_lonelyRunnerAt8⟩

end LRC.Spec
