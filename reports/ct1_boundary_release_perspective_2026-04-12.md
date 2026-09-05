# CT.1 Boundary-Release Perspective

Date: 2026-04-12
Status: conceptual correction + exact local lemma

## 1. Main point

Yes: the current evidence says the **boundary** is a more fundamental
object than LOW-thin status by itself.

LOW-thin residues were a useful intermediate guide, because they helped us
see where fragile coverage tends to live after transfer.
But the recent counterexamples show that the real theorem object is not

> “which residue is thin at the transfer fibre?”

It is

> “which residue becomes unrepaired at a later boundary event?”

So the right primitive is **boundary release**, not static transfer-fibre
thinness.

## 2. Why the LOW-thin route was not enough

Two opposite failures already show this.

### Failure A

In

`E = (26,35,49,89,104,124,130,143,182,190)` with `n=11`,

the first safe fibre comes from the transferred HIGH residue itself.
So LOW-thin is not the right universal carrier.

### Failure B

In

`E = (2,58,68,86,92,93,110,117,181,188,240,243)` with `n=13`,

there is an earlier LOW-thin candidate at the transfer fibre, but by the
time its owner drops it, another runner already covers that residue.
So transfer-fibre LOW-thin status does not guarantee boundary release.

These two failures point in the same direction:

> what matters is not being thin at some earlier snapshot, but being
> unrepaired exactly at the boundary where departure occurs.

## 3. Exact local lemma

We can say this cleanly.

Let `b` be an event boundary and let `b^-` denote the immediately previous
fully covered state, i.e. just before the runners resetting at `b` change
their bad sets.

For a runner `e` resetting at `b`, define its departure set

`Dep_e(b) := bad_e(b^-) \ bad_e(b)`,

and arrival set

`Arr_e(b) := bad_e(b) \ bad_e(b^-)`.

Let

`Dep(b) := union_e Dep_e(b)`

over runners resetting at `b`.

**Lemma B.1 (boundary-release lemma).**
Suppose `b` is the first safe fibre after an interval of full coverage.
Then there exists a residue `r` such that:

1. `r` is covered at `b^-`,
2. `r` is uncovered at `b`,
3. every runner covering `r` at `b^-` resets at `b`,
4. and each such runner drops `r` at `b`.

Equivalently, the first safe fibre is always created by a residue whose
entire pre-boundary support is lost at that boundary.

**Proof.**
Since `b` is the first safe fibre, all earlier event boundaries preserve full
coverage.
At `b`, pick any residue `r` that is uncovered after the event.
Because the state just before `b` was fully covered, `r` was covered at
`b^-`.
Only runners resetting at `b` can change their bad sets between `b^-` and
`b`, so any runner that covered `r` at `b^-` and still covered `r` after
the event would keep `r` covered at `b`, contradiction.
Hence every pre-boundary blocker of `r` must be among the resetting
runners and must drop `r` at `b`. `square`

## 4. Consequence for single-runner safe events

Most of the rare large-runner depth-`1` examples found so far have their
first safe fibre created by a single reset event.

In that case Lemma `B.1` simplifies immediately:

**Corollary B.2.**
If the first safe fibre `b` is created by a single resetting runner `e`,
then the missing residue `r` had multiplicity `1` at `b^-` and belongs to
`Dep_e(b)`.

So for single-reset safe events, the decisive object is indeed a
boundary-thin departure.

This explains why the LOW-thin heuristic worked so often:
it was often predicting a future boundary-thin departure.
But it also explains why it could fail:
future arrivals can change multiplicity before the relevant boundary.

## 5. Why this perspective is better

This boundary view absorbs all the current phenomena.

### It absorbs the old LOW-thin successes

If a transfer-fibre LOW-thin residue stays multiplicity `1` until its drop,
then it becomes exactly the boundary-release object of Corollary `B.2`.

### It absorbs Failure A

The transferred HIGH residue itself can be the boundary-release object.
So there is no need to force LOW-thin status.

### It absorbs Failure B

A residue can be LOW-thin at transfer but no longer boundary-thin by the
time it drops.
That is exactly why the transfer-fibre formulation overreached.

## 6. Suggested reformulation of the target

The current target should therefore be reformulated like this:

**Candidate theorem `B-TR`.**
In the prime dropped-unit selected-HIGH branch, once the process enters the
post-transfer regime, there is a short chain of boundary threats, and one
of those threats is eventually unrepaired, producing the first safe fibre.

Here a **boundary threat** means:

- a boundary `b`,
- a residue `r`,
- and the fact that `r` is in the departure set of one or more resetting
  runners at `b`.

The theorem we actually need is then not

- “the earliest LOW-thin residue wins,”

but rather

- “the post-transfer boundary-threat chain cannot repair itself forever.”

That feels much closer to the original transport-instability narrative.

## 7. Practical implication

So the answer to the question

> “Do we need to look at the boundary rather than low thin?”

is:

> yes, probably.

More precisely:

- LOW-thin is still a useful heuristic and sub-lemma generator,
- but boundary release is the better overarching language,
- because safe fibres are created at boundaries, not at static snapshots,
- and the real missing theorem is about non-permanent repair across a short
  chain of boundary events.
