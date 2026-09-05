# O1/O2 Closure Draft Review Memo (v1)
**Date:** 2026-03-07  
**Purpose:** assess `lrc_o1_o2_formal_closure_v1.md` against the live G4B and GAP-2 theorem tracks, isolate any theorem-grade salvage, and record why the draft does not canonically close either branch.

## 0) Verdict
The draft should **not** be promoted as a closure of:
- O1 (`G4B-COMP-CAP` Case C), or
- O2 composite B2.

It does contain one clean arithmetic salvage:
- an exact per-runner count of interior unit `z=0` events in `B_div`.

That salvage is recorded separately in:
- `lrc_g4b_unit_z0_event_count_lemma_v1.md`

## 1) O1 review (`G4B-COMP-CAP` Case C)

### What the draft tries to prove
The O1 section tries to derive

`B_safe >= n`

by counting interior unit `z=0` events runner-by-runner, then converting that count into a run-cap bound

`max_obstr_run <= |B_div| - n`.

### Why this is not canonizable

#### O1-A. Scope jump
The key lower bound is stated only under the extra assumption:

`E_non contains all phi(n) units of {1,...,n-1}`.

That is **not** the general O1 / G4B scope.
The live G4B theorem target covers composite Case-2 tuples in the declared branch without such a full-unit-content hypothesis.

So even before counting issues, the theorem is not the branch-local closure statement that O1 is supposed to prove.

#### O1-B. Event-sum to safe-fibre-sum is unproved
The draft uses the sum of per-runner unit `z=0` event counts as a lower bound for distinct safe fibres:

`B_safe >= sum_e Z(e) + 2`.

This step is not proved.
Multiple unit runners can have coincident `z=0` events, so runner-wise event counts do **not** automatically add to a distinct-fibre count.

The draft's "Non-Coincidence note" explicitly admits overcounting and does not supply a valid collision correction strong enough to preserve the claimed `>= n` bound.

So `Z0S.2`, `Z0S.3`, and therefore `Z0S.4` do not go through as theorem-grade deductions.

#### O1-C. Final theorem inherits the counting gap
Because the fallback bound in Theorem O1 depends on `Z0S.4`, the O1 closure claim is not proved.

The case split may still contain useful heuristics, but the theorem-grade branch status remains:

`G4B-COMP-CAP = OPEN-TARGET`.

## 2) O2 review (GAP-2 composite B2)

### What the draft tries to prove
The O2 section introduces:

`U-FORCE`

claiming that for any gcd-1 tuple with `|E_div| >= 2`, all unit elements of `{1,...,n-1}` must lie in `E_non`,
then imports the O1 event count to conclude

`x0 >= phi(n)`.

### Why this is not canonizable

#### O2-A. `U-FORCE` is false/off-scope
GAP-2 tuples are arbitrary speed tuples.
They are **not** assumed to contain each residue class `1,...,n-1` exactly once.

So from

`|E_div| >= 2`

one cannot conclude that all unit elements of `{1,...,n-1}` are present in `E_non`.
At most one can say: if a unit speed is present, then it is not in `E_div`.

That is much weaker than the draft needs.

#### O2-B. O2 inherits the O1 counting gap
Even if `U-FORCE` were repaired, the proof still imports the invalid O1 lower bound

`B_safe >= phi(n)(n-2)/2 + 2`.

So the composite B2 closure does not follow.

### Current canonical consequence
The live analytic status for composite GAP-2 B2 remains open in the pack.
This draft does not close it.

## 3) Theorem-grade salvage
One lemma from the draft is clean and useful:

### Salvage S1
For a fixed unit runner `e` with `2 <= e <= n-1`, the number of interior `z=0` event positions inside open `B_div` is exactly

`e - 1`.

This is packaged separately in:
- `lrc_g4b_unit_z0_event_count_lemma_v1.md`

### Limitation of the salvage
S1 is a **per-runner** count only.
It does **not** imply:
- distinct safe-fibre count,
- `B_safe >= n`,
- O1 closure,
- or any GAP-2 closure.

Any use of S1 must add a separate collision-control or occupancy argument.

## 4) Program consequence
The correct update from this draft is narrow:
- keep O1 / `G4B-COMP-CAP` open,
- keep composite GAP-2 B2 open,
- retain only the exact per-runner interior event count as a support lemma.

The next analytic target for O1 remains collision/occupancy control, not raw event counting.
The next analytic target for O2 remains a genuine delayed-miss theorem in the composite B2 regime, not a forced-all-units assumption.

## 5) Status
`CANONICAL-REVIEW-MEMO`.
