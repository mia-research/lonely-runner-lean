# Multi-11 Dynamic Branch Collapse v1

**Date:** 2026-03-24  
**Status:** Corrected late-branch analysis for the multi-`11` dynamic case.

---

## 1. Executive summary

The original next-step target was:

> prove that with at least two multiples of `11`, the best substitute branch is
> the `16`-branch, and hence every such orbit witnesses by `23/66` (or at least
> by `4/11`).

The current analysis shows that this needs one precise correction.

There are two different notions:

1. **local blocker maximizer** at a checkpoint `t`;
2. **globally compatible late branch** that can actually occur in an extremal
   multi-`11` ILE orbit.

These are not the same.

Locally, the `16`-branch is not always the unique strongest continuation.
For example, once the orbit has reached `7/22`, the best local blocker after
excluding `3` and `16` is actually `25`, not `22` or `19`.

But globally, the exhaustive searches strongly indicate that these alternative
local branches are **anti-extremal**: their presence earlier in the orbit forces
smaller ILE advances and prevents the branch from ever becoming the true late
envelope.

So the corrected mechanism is:

> **The multi-`11` late dynamics are controlled by a compatibility filter.**
> Many large local blockers are only *mirage branches*; the only branch that
> survives global compatibility in the tested extremal families is the
> `16`-endgame, terminating at `23/66`.

---

## 2. Local late-branch facts

These are facts about the set of all blocking runners at a fixed checkpoint.
They do **not** yet incorporate global compatibility with the earlier orbit.

### 2.1 At `17/55`, excluding `3`, the best substitute is `16`

Among all blocking runners at

```text
t = 17/55,
```

with runner `3` excluded, the largest next-entry time is

```text
tau_max = 7/22,
```

attained by runner `16`.

The leading blockers up to `p <= 500` are:

```text
16 -> 7/22
13 -> 45/143
29 -> 100/319
58 -> 199/638
42 -> 24/77
```

So the first substitute step really is the `16`-step.

### 2.2 At `7/22`, the strongest local continuation is not the old `22`-branch

At

```text
t = 7/22,
```

excluding `3` and `16`, the largest next-entry time up to `p <= 500` is

```text
25 -> 89/275,
```

ahead of

```text
22 -> 39/121,
19 -> 67/209.
```

So the statement

> "the best substitute branch is the `16`-branch"

is **false if interpreted purely locally**.

### 2.3 Other late local maximizers

Some additional local blocker maxima:

```text
at 39/121, excluding 3 and 16:   6  -> 23/66
at 23/66,  excluding 3:          17 -> 67/187
at 67/187, excluding 3:          11 -> 45/121
```

If one looks only at local blocker tables, this suggests a much larger branch
tree than the original `16`-endgame.

That is the source of the apparent branching.

---

## 3. Why the apparent branching is misleading

The local blocker table ignores an essential fact:

> a runner that gives a large local next-entry at a late checkpoint may be
> impossible to carry along the orbit without forcing a smaller advance earlier.

This is the key distinction between:

- **available late blocker**, and
- **compatible late blocker**.

The strong local substitutes `17`, `18`, `20`, `25`, ... appear in blocker
tables, but they tend to be globally harmful:

- they introduce earlier blocking zones,
- or they consume one of the scarce non-multiple slots without reproducing the
  exact late-ladder roles,
- or both.

This is exactly why the multi-`11` regime still witnesses early despite having
more multiples of `11`.

### 3.1 The real obstruction: earliest intervention, not late potential

The reason the current "late-branch" program does not automatically close is
that it is optimizing the wrong object.

What matters in an ILE orbit is **not**

```text
how far a runner can push the orbit once a late checkpoint is reached,
```

but rather

```text
the earliest checkpoint at which that runner becomes active.
```

A runner is helpful only if it stays dormant until the orbit actually needs the
replacement role. If it fires earlier, it drags the orbit onto a smaller branch
before the late checkpoint is ever reached.

This is exactly what the forced-runner traces show:

- `20` looks strong locally at `23/77`, where it gives

```text
23/77 -> 67/220,
```

but in its extremal forced configuration it acts much earlier:

```text
12/121 -> 23/220   by 20,
```

so its real effect is to flatten the orbit long before the late endgame.

- `25` looks strong locally at `7/22`, where it gives

```text
7/22 -> 89/275,
```

but in its best forced configuration it intervenes already at

```text
4/33 -> 34/275   by 25,
```

which is dramatically earlier than the `16`-endgame and kills the orbit by
`23/99`.

- `17` looks dangerous locally at `23/66`, where it gives

```text
23/66 -> 67/187,
```

but in the best forced `17`-configuration it is already active at

```text
23/198 -> 23/187   by 17,
17/99  -> 2/11     by 17,
28/121 -> 45/187   by 17,
23/77  -> 56/187   by 17,
```

and the orbit never reaches `23/66` at all.

So the true reason the local branch tables do not close the theorem is:

> **late potential is irrelevant unless the runner is silent on all earlier
> checkpoints where it could intervene.**

That is the missing mechanism behind the apparent branching.

### 3.2 Not all early branches are destructive

There is one more correction needed.

It is **not** true that every runner whose first action is earlier than the
`16`-endgame is automatically anti-extremal.

The runner `19` is the clean counterexample.

In the best forced-`19` configuration

```text
(1,4,6,7,9,10,11,16,19,22),
```

the witness time is still

```text
23/66,
```

even though `19` branches earlier than the `16`-endgame:

```text
6/55   -> 23/209   by 19,
12/77  -> 34/209   by 19,
23/110 -> 45/209   by 19,
7/22   -> 67/209   by 19.
```

Why is `19` harmless while `17,18,20,25` are not?

Because `19` only creates **refinement branches**: it inserts an extra
sub-checkpoint but still returns to the same main staircase.

For example:

```text
6/55   -> 23/209 -> 4/33,
12/77  -> 34/209 -> 2/11,
23/110 -> 45/209 -> 23/99,
7/22   -> 67/209 -> 39/121.
```

Each `19`-step is followed by the original staircase owner, and the orbit
rejoins the same late envelope.

By contrast, `17,18,20,25` create **destructive branches**: their first
intervention skips one of the main staircase checkpoints altogether.

- `20`:

```text
12/121 -> 23/220 -> 4/33,
```

skipping the checkpoint `6/55`.

- `18`:

```text
6/55 -> 23/198 -> 3/22,
```

skipping the `4/33 -> 23/176 -> 12/77` segment.

- `25`:

```text
4/33 -> 34/275 -> 3/22,
```

again skipping the `16`/`7` segment.

- `17`:

```text
4/33 -> 23/187 -> 3/22,
```

and similarly destroys the late `16`-repair path.

So the correct dichotomy is not

```text
early branch vs. late branch,
```

but

```text
refinement branch vs. destructive branch.
```

This is much closer to the actual closure mechanism.

---

## 4. Exhaustive evidence for actual branch collapse

The following families were checked exhaustively with seven additional
non-multiples chosen from `2..20`:

```text
(1,11,22),
(1,22,33),
(1,33,44).
```

In all three families:

```text
T_ILE <= 23/66,
```

and the best witness found is exactly

```text
23/66
```

for the staircase-deficit configuration

```text
(1,4,5,6,7,9,10,16,11q,11r)
```

with the relevant pair of multiples of `11`.

### 4.1 Reachable late states in the exhaustive families

For base `(1,11,22)`, the only late checkpoints reached by any orbit with
maximal witness are:

```text
17/55, 7/22, 39/121, 23/66.
```

The following locally available states are **never reached**:

```text
67/187, 89/253, 45/121, 4/11.
```

The same non-reachability pattern holds for bases `(1,22,33)` and `(1,33,44)`,
except that the intermediate checkpoint `39/121` is absent when `22` itself is
not present.

So the late state machine collapses empirically to the short chain

```text
17/55 -> 7/22 -> 39/121 -> 23/66,
```

or the shortened variant that skips `39/121` when `22` is not available.

---

## 5. Forced-substitute tests: which large runners are actually helpful?

For the exhaustive base `(1,11,22)` with seven more non-multiples from `2..20`,
forcing the presence of a given substitute runner yields:

```text
force 16  -> best witness 23/66
force 17  -> best witness 17/55
force 18  -> best witness 17/55
force 19  -> best witness 23/66
force 20  -> best witness 67/220
force 25  -> best witness 23/99
```

Interpretation:

- `16` is the unique runner that supports the proven late endgame.
- `19` can coexist with the late endgame, but does not improve on it.
- `17`, `18`, `20`, and especially `25` are globally anti-extremal.

So the local maxima `17 -> 67/187` and `25 -> 89/275` are not true competitors
to the late envelope. They are only **mirage branches**.

---

## 6. Stronger compatibility check on the `17`-branch

The most dangerous local mirage is

```text
23/66 -> 67/187   by 17.
```

To test whether this can actually occur in a late two-`11` orbit, we performed
an exhaustive search over all configurations of the form

```text
(1,11,22,17,*,*,*,*,*,*)
```

with the remaining six non-multiples drawn from `2..30`, excluding `3`.

Result:

```text
max witness = 17/55,
```

and **no trace reaches `67/187`**.

This is strong evidence that the `17`-branch is not globally compatible with
the late multi-`11` envelope.

---

## 7. Corrected theorem target

The corrected dynamic theorem is therefore not:

> "the best substitute branch is locally the `16`-branch."

It is:

> **Branch-collapse theorem (corrected target).**
> In the multi-`11` regime, every local substitute branch other than the
> `16`-endgame is globally anti-extremal. Consequently the only compatible late
> envelope is the `16`-endgame, and
>
> ```text
> T_ILE <= 23/66
> ```
>
> (hence certainly `T_ILE < 4/11`).

This is the formulation that turns the mechanism into the theorem.

---

## 8. What still needs an analytic proof

The remaining analytic step is now very specific:

1. Prove the local maximizer lemma

```text
17/55 -> 7/22  by 16
```

rigorously.  

2. Prove a **compatibility elimination lemma** for the dangerous mirage
branches:

```text
17, 18, 20, 25, ...
```

showing that if such a runner is present, then some earlier checkpoint forces a
strictly smaller ILE advance than the `16`-endgame.

3. Conclude that only the `16`-endgame survives as the extremal branch.

At that point the dynamic multi-`11` bridge is complete.

Equivalently, one can formulate the missing theorem as an
**Earliest-Intervention Principle**:

> among candidate substitute runners, the extremal orbit is determined by the
> runner whose first active checkpoint is latest subject to preserving the
> largest advance there.

Under this principle, `16` is special not merely because it has a large late
step, but because it is the best runner whose first interventions occur exactly
at the checkpoints where the staircase deficit needs to be repaired.
