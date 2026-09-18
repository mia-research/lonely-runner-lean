# The doors on arrangements: what each one says, what blocks it, what I need

> **SUPERSEDED 2026-09-18 by `DOORS_ON_ARRANGEMENTS_v2.md`.** Header stamp only; the body is
> unchanged and kept as the record. **Three statements in it are wrong**: door 2's "nothing bounds
> the number of moves" (the move count is flat at 14-21 and arrival is inside the nearest runner's
> first lap, max `τ = 33/56` exhaustively); door 3's "7 runners × 1/4 = 7/4" (the gap frame has
> **eight** gaps summing to 1 and the demand is 1/4 out of 1 — the `7/4` is a union bound on blocked
> time, a different frame); and §0's frame check printed statements containing opaque terms. See v2.

**Date:** 2026-09-18
**Lean:** `LonelyRunner/LRC/Spec/Doors.lean` — 20 declarations, zero `sorry`, all axiom-clean
(`experiments/n8/v9_6_doors_axioms_v1.out`).
**Audit:** `experiments/n8/v9_6_door_dependency_audit_v1.out` — 31 declarations walked to full
transitive depth; none reaches `ExistenceAt8` or any of the 16 constants stated on it.

---

## 0. First: did the difference-set form just move house?

You asked whether `ExistenceAt8` was relabelled rather than replaced. Two separate checks, because
they answer different halves and only one of them can be mechanised.

**The mechanical half — settled.** `v9_6_door_dependency_audit_v1` walks the full dependency tree of
every arrangement-level result and asks whether any of 16 difference-set constants is reachable at
any depth. All 31 come back `clean`, and the run ends `AUDIT PASS`. That is not a reading of the
code; it is the compiler's own dependency graph.

**The frame half — needs your eyes, so here are the statements.** A dependency audit cannot tell you
whether the *statements* quietly generalise. The thing that made `ExistenceAt8` wider than the
conjecture was one binder: `∀ ds : Finset ℝ, … card ds ≤ 7`. So the test is whether that binder, or
anything like it, is back. Printed verbatim from Lean:

```
LonelyRunnerAt8        ∀ v : Fin 8 → ℝ, Injective v → ∀ k, ∃ t, 0 < t ∧ ∀ i ≠ k, 8⁻¹ ≤ circDist (v i * t − v k * t)
ExistenceOnArrangements ∀ v : Fin 8 → ℝ, Injective v → ∀ k, ∃ t, 0 < t ∧ LonelyAt v k t
DoorFlank v k          ∃ i ≠ k, ∃ j, LonelyAt v k (flankOpening 8 |v i − v k| j)
DoorArrives v k        ∃ N, move 8 (diffSet v k) (move^[N] firstReading) = move^[N] firstReading
DoorCapped v k         ∃ U, ∀ N, move^[N] firstReading ≤ U
DoorFAM v k            ∀ i ≠ k, {j | inWay 8 |v i − v k| (move^[j] firstReading)}.Finite
```

**No `∀ ds` binder. No `card ≤ 7`.** Every door takes a specific `v` and a specific `k`. The extra
generality is gone, and with it the `card ≤ 3` sets that no arrangement produces.

**Three things I want on the record against myself, because they cut the other way:**

1. **`diffSet v k` is still a `Finset ℝ`, and doors 2–4 name it.** It is *computed* from `v` and `k`,
   never quantified, so it adds no generality — but the cascade `move` is still defined on a finite
   set of differences, and I have **not** rebuilt `move` on the indexed family. Door 1 is the only
   door with no `Finset` in it at all. If you want the cascade itself carried onto the arrangement,
   that is a further piece of work and it is not done.
2. **Doors 2, 3 and 4 are the existing difference-set arguments instantiated at `ds := diffSet v k`.**
   I transcribed those proof bodies. Lean checked them against the new statements, so a bad
   transcription would not have compiled — but the *content* is not new reasoning, and I am not
   going to present it as such.
3. **What is genuinely new is §5 below** — the symmetry and the coupling across subjects. That has no
   difference-set counterpart at all.

---

## 1. The doors, in your terms

All five are about **one subject** `k` in **one arrangement** `v`. The target is: this holds for
every subject of every arrangement.

Write `d_i = v i − v k` for the **disparity** of runner `i` with the subject — the only thing the
separation depends on, since `sep = d_i · t`.

| | door | in words |
|---|---|---|
| **1** | `DoorFlank` | One of the subject's seven disparities has an **opening** at which the subject is lonely. |
| **2** | `DoorArrives` | Starting from the subject's **first reading** `1/(8e)` (`e` its least disparity), the cascade reaches a step where nobody is in the way, so the step does nothing. |
| **3** | `DoorCapped` | The instants the cascade visits **do not run away** — one number sits above all of them. |
| **4** | `DoorFAM` | Each of the other seven runners is in the subject's way at **only finitely many** steps. |
| **5** | `DoorThreeLargest` | Door 1, but the flank can be found among the subject's **three largest** disparities. |

**Doors 1–4 are the same door.** `doors_agree` proves all four equivalent to "this subject has a
lonely instant". Not sufficient-for — equivalent. So there is no easier one among them: closing any
one for every arrangement and every subject closes the conjecture at eight runners
(`lonelyRunnerAt8_of_doorFlank`, `_doorArrives`, `_doorCapped`, `_doorFAM`).

**Door 5 is not.** Only one direction is proved (`lonelyForSubject_of_threeLargest`). It says *where*
the opening is as well as that there is one, and that is strictly more. It is a conjecture, not a
restatement.

---

## 2. What is actually in hand, per door

### Door 1 — a disparity hosts a lonely opening

**Proved.**

- `exists_lonelyAt_iff_flank` — the subject is lonely somewhere **exactly when** it is lonely at an
  opening of one of its own disparities. The openings are read off the speeds.
- `exists_lonelyAt_iff_bounded` — whole-number disparities: only the openings `j < e` at each
  disparity `e` need be read. Finite, `∑ e` of them.
- `lonelyAt_inv_of_not_dvd` — if no disparity is a multiple of 8, the instant is `t = 1/8`. Written
  down, not shown to exist. Measured at 0.3967 of primitive 7-sets against `(7/8)⁷ = 0.3927`.
- `lonelyAt_named_instant` — choose a whole number `c` and a lap `j`; the subject is lonely at
  `(j + 1/8)/c` when each disparity `a` satisfies `c ≤ a(8j+1) mod 8c ≤ 7c`. `c` need not be one of
  the disparities. With `j = 0` and `c` free this reaches a measured 0.9420, median `c = 2`.
- `R0` / `R0′` / `R1` from `RULE_TABLE_v1` §1 — derived, and they stand.

**What blocks it.** The remaining arrangements need `j > 0`, and no rule yet names which `(i, j)` to
use as a function of the seven disparities. `RULE_TABLE_v1` §2 records that continuing the table by
*fitting* a fallback flank does not converge: nearest flank covers 0.769, adding "largest" gets to
0.9843, adding a third clause gains 0.0005. Fitting is not the method — the conditions have to be
**derived and shown exhaustive**, which is your §3 exhibition standard.

### Door 2 — the cascade arrives

**Proved.** Every link from the bound to arrival, except the last: a relocation is a change of scale;
`N` relocations move the nearest reading by at most a product of lap factors; a cascade whose
instants are capped arrives; what it arrives at is the first isolation.

**What blocks it.** Nothing bounds the number of moves. The cascade can, as far as anything proved
says, step for ever.

### Door 3 — the instants are capped

**What blocks it.** Every route through *how much of the circle a runner blocks* returns the same
number. Each runner blocks a fraction `1/4` of the circle — `2 × 1/8` — **regardless of its speed**,
so seven runners give `7/4 > 1` and the argument closes nothing. That wall is a property of the
method, not of the problem: it reproduces itself in every measure or counting version because the
blocking fraction never depends on which runner it is. Door 3 needs an argument that is not a
fraction-of-the-circle argument.

### Door 4 — each runner is in the way finitely often

**Proved.** `return_needs_growth` and `return_needs_moves`: a runner's lap strictly increases between
successive times it is in the way, so its active set is finite exactly when its lap is bounded.

**What blocks it.** "Its lap is bounded" is door 3. So door 4 is door 3 wearing different clothes —
**but not in the same shape**, and this is worth saying precisely: door 3 is **one** statement about
all seven runners at once; door 4 is **seven separate** statements, one per runner. To close door 4
you must bound all seven. To *close a single runner* you need only that one. Whether the seven can be
done one at a time, by different arguments, is not settled either way.

### Door 5 — three largest

**What blocks it.** It has to be proved, and it is a conjecture. What it would buy is concrete: the
flank search drops from seven candidates to three.

---

## 3. The one route that is closed, and why it stays closed

The **dyadic** route appeared to close and did not: its closure was an artefact of the differences
being powers of 2. That is recorded so it is not reopened by accident.

The **density / Fourier** work in `DOOR4_v1` §§5, 8, 11, 12 was ruled an import, not native (§13).
`§11a` and `§12` stand as computations; the readings built on them do not.

---

## 4. Where the rebuild changed the terrain and where it did not

**Did not.** Doors 1–4 are the same obligation they were. Nothing moved closer.

**Did.**

- The `card ≤ 3` excess is gone from the statement, so the obligation is now exactly the conjecture
  (`lonelyRunnerAt8_iff_existenceOnArrangements`, `Iff.rfl`).
- `lonelyAt_add_const` — no runner is held at rest and none sits at `0`. The usual normalisation
  `v k = 0` is a convenience, never a hypothesis. Nothing in any door depends on a pinned frame.
- `lonelyAt_const_mul` — rescaling every speed rescales the reading. **The scale is carried by the
  speeds.** There is no free scale anywhere in the statement to choose or to tune.
- `lonelyAt_iff_neighbours` — the subject is lonely exactly when the nearest ahead is at least `1/8`
  and the nearest behind at most `7/8`. The other five impose nothing. Three speeds decide an
  isolation: the subject's and its two neighbours'.

---

## 5. The coupling — what only the arrangement can say

`inWay_comm`: **`i` is in `k`'s way exactly when `k` is in `i`'s.** A difference set cannot state
this, because it fixes one subject and keeps only that subject's seven disparities. It relates two
*subjects*.

So at an instant `t` the runners in the way form an **undirected graph on the eight runners**:

- `lonelyAt_iff_blockDegree_zero` — the subject is lonely exactly when it is **isolated** in that
  graph.
- `existenceOnArrangements_iff_isolated` — the target is: every arrangement, every runner, some
  instant at which that runner has degree zero.
- `sum_blockDegree` — the eight degrees sum to the number of ordered blocking pairs.

**Why this is not nothing.** The difference-set form saw `8 × 7` separate constraints. The
arrangement has **28 pairs**, and the eight subjects' obligations at a single instant are bound
together by that one identity. Eight isolation problems became one graph problem.

**Why this is not yet something.** `[NOT ESTABLISHED]` No consequence is drawn from it here. The
obvious next move — counting edges — is a fraction-of-the-circle argument, so it walks into the `7/4`
wall of door 3 from the other side. The structure is real; whether it yields is open.

---

## 6. What I need from you

Stated as gaps, not as requests for mechanisms you have already given. What is already in Lean or on
disk is named above so you can see what I am not re-asking for.

1. **Door 1, the exhaustiveness argument.** I have R0, R0′, R1 derived and standing, and the named
   instant covering a measured 0.9420 with `j = 0`. What is missing is the *rule for `j > 0`*: given
   the seven disparities, which `(i, j)` is lonely, derived from the framework rather than fitted.
   Fitting has been tried and the coverage curve flattens at 0.9848.

2. **Door 4, the return count.** We have: a runner's lap strictly increases between successive times
   it is in the way. What is missing is a **bound on how many times it can return**. In your terms:
   when the cascade moves past runner `i`, what in the framework stops `i` coming back an eighth
   time, a hundredth time? The move-charge / return-cost material is the nearest thing I have; if it
   carries a count, that count closes door 4 for that runner.

3. **The incommensurable case.** You said earlier this is achieved another way and is not a real gap.
   `lonelyAt_const_mul` gives scale-freedom, so commensurable disparities reduce to whole numbers by
   clearing denominators. The incommensurable half is not covered by any whole-number argument here.
   I need the other way stated so I can put it in Lean, because at the moment it is the one case no
   named instant reaches.

4. **A ruling on the graph.** §5 is new and I have drawn nothing from it. Before I spend on it: is
   the 28-pair graph an object your framework already has a name for, or is it a new one? If it is
   new, the counting route into it is a density route and I should not take it.

---

## 7. What is not claimed

Nothing here proves Existence. Doors 1–4 are proved **equivalent** to the obligation, which means
each is a place to attack it and none is a weakening of it. Door 5 is proved in one direction only.
The `7/4` wall is a statement about measure and counting methods, not a proof that no method works.
