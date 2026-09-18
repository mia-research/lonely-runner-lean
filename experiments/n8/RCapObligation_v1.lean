import LonelyRunner.LRC.Spec.Doors

/-! # The `R`-cap obligation, stated honestly

A parallel session proposed closing `DoorCapped` with a "piecewise analytical bound"

```
    R ≤ 89/S ≤ 11.946   if S ≥ 7.45        (from s₇·R = 89)
    R ≤ 10.6            if S < 7.45        ("6-runner comb capacity")
    ⟹ R < 12 universally ⟹ DoorCapped ⟹ LonelyRunnerAt8
```

**Neither branch is proved.**

* The `89` is *empirical*. It is the value of `8k+1` observed to bind at the maximiser, with `k = 11`.
  Nothing establishes that `k = 11` rather than `12` or `13` is the binding lap for every profile with
  `S ≥ 7.45`; the search found it, which is not a proof.
* The "`6-runner comb capacity ≤ 10.6`" is *the open problem*. There is no such theorem. Bounding how
  long six readings can collectively avoid their bad bands **is** the covering question, and
  `doorCapped_iff` is an `↔` — `DoorCapped` is equivalent to loneliness, not weaker than it. So a
  proof of that branch would be a proof of the conjecture, and it cannot come from the observation
  that searches stop at 11.97.

What *can* be stated now is the implication, with the cap as an explicit hypothesis. That makes the
remaining obligation visible in Lean instead of assumed.

Measured, for the record: `max R = 11.965675` over 12.2 million profile evaluations; `R mod 8 ∈ [1,7]`
(`RBand.R_avoids_bad_bands`) over 148,892 cascades with zero violations; band 2 never observed. All
of that is evidence, none of it is a bound. -/

namespace RCapObligation

open LRC.Spec Arrangement MomentIterationN Flanks

/-- **The obligation.**  Every cascade iterate stays within a universal factor `B` of the subject's
first reading.  Since `t_final = R · firstReading`, this is exactly "`R ≤ B` for every subject". -/
def RCapped (B : ℝ) : Prop :=
  ∀ v : Fin 8 → ℝ, Function.Injective v → ∀ k : Fin 8, ∀ N : ℕ,
    (move 8 (diffSet v k))^[N] (firstReading v k) ≤ B * firstReading v k

/-- **The implication, proved.**  A universal `R`-cap gives `DoorCapped` at every subject. -/
theorem doorCapped_of_RCapped {B : ℝ} (h : RCapped B)
    (v : Fin 8 → ℝ) (hv : Function.Injective v) (k : Fin 8) :
    DoorCapped v k :=
  ⟨B * firstReading v k, fun N => h v hv k N⟩

/-- **The chain to the target.**  Composing with `lonelyRunnerAt8_of_doorCapped`: a universal
`R`-cap proves the conjecture at eight runners.  The hypothesis is the whole of what is owed. -/
theorem lonelyRunnerAt8_of_RCapped {B : ℝ} (h : RCapped B) : LonelyRunnerAt8 :=
  lonelyRunnerAt8_of_doorCapped fun v hv k => doorCapped_of_RCapped h v hv k

end RCapObligation
