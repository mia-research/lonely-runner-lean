# CT.1 Critical Boundary Scan

Date: 2026-04-12
Status: empirical branch-specific invariant

## 1. Purpose

This note records the next sharpening of the post-transfer repair target.

After switching from static LOW-thin language to the boundary viewpoint,
the natural next object is a **critical boundary event**.

The main finding is:

> in all currently harvested selected-HIGH depth-`1` cases, the first safe
> fibre is the first critical boundary after transfer, and that safe
> boundary has a unique critical residue with singleton pre-boundary
> support.

At the same time, this is **not** a generic combinatorial truth for
arbitrary tuples.
Outside the selected-HIGH branch, repaired singleton-critical events are
common.

So this looks like a genuine branch invariant, not a tautology.

## 2. Definition

Let `b` be an event boundary and `b^-` the immediately previous covered
state.

Let `Reset(b)` be the set of runners resetting at `b`.

For a residue `r`, let

`Supp^-(r;b) := { e : r in bad_e(b^-) }`

be its pre-boundary support.

We call `(b,r)` a **critical boundary event** if:

1. `Supp^-(r;b) subseteq Reset(b)`, and
2. at least one runner in `Supp^-(r;b)` drops `r` at `b`.

So `r` is critical at `b` when its entire existing support is exposed to
that boundary.

If after the event the residue is still covered, the critical event is
**repaired**.
If after the event the residue is uncovered, the critical event is
**unrepaired** and contributes to a safe fibre.

## 3. Harvested depth-1 dataset

The currently checked selected-HIGH depth-`1` dataset consists of:

- the four exhaustive `n=7` prototypes,
- twelve harvested large-runner `n=11` depth-`1` examples,
- and eight harvested large-runner `n=13` depth-`1` examples.

So the dataset size is:

- `24` selected-HIGH depth-`1` cases.

## 4. Main scan result

Across all `24` harvested cases:

- repaired critical boundaries after the first transfer: `0`,
- safe boundaries with exactly one critical residue: `24`,
- safe critical residues with singleton pre-support: `24`.

More explicitly, the shape count was:

- `22` cases with
  - one critical residue,
  - singleton pre-support,
  - and a single resetting runner at the safe boundary;
- `2` cases with
  - one critical residue,
  - singleton pre-support,
  - and two resetting runners at the safe boundary.

So in every currently harvested selected-HIGH depth-`1` case:

1. no repaired critical boundary appears between transfer and the first safe
   fibre;
2. the first safe fibre is the first critical boundary after transfer;
3. that safe boundary has a unique critical residue `r_safe`;
4. and `r_safe` has exactly one pre-boundary supporter.

This is much sharper than the earlier LOW-thin formulation.

## 5. Why this matters

This almost collapses the post-transfer chain.

The earlier target was:

- a short thin-release chain.

The current data suggest a stronger selected-HIGH branch statement:

- after transfer, there are no repaired critical boundaries at all before
  the safe event.

So the real theorem target may be:

**Candidate theorem `CB.1`.**
In the prime dropped-unit selected-HIGH depth-`1` regime, the first
critical boundary after transfer is already the first safe fibre, and it
has a unique critical residue with singleton pre-boundary support.

If `CB.1` were proved, the remaining analytic burden would be:

- prove that a critical boundary must occur soon enough after transfer.

That is a much cleaner target than the earlier LOW-thin chain language.

## 6. Important caveat: this is not a generic lemma

I also tested whether singleton-critical repaired events are absent in
general.
They are **not**.

In random ambient tuples, repaired singleton-critical events occur often.
Examples were found for:

- `n=7`,
- `n=11`,
- `n=13`.

So statements like

> “if a residue has singleton support and its sole supporter resets, then
> the boundary is automatically safe”

are false in general.

That is actually useful information.
It means any proof of `CB.1` must use the specific selected-HIGH /
dropped-unit geometry, not just abstract event combinatorics.

## 7. Interpretation

This strengthens the boundary perspective in exactly the right way.

The boundary view was already better than transfer-fibre LOW-thin status.
Now the data say something stronger:

- not only is the safe fibre created at a boundary,
- but the post-transfer selected-HIGH branch appears to avoid repaired
  critical boundaries altogether.

So the real missing theorem may be closer to:

> the selected-HIGH post-transfer regime cannot sustain a repaired critical
> boundary before a genuine uncovered one appears.

That feels like a theorem with a realistic analytic shape.

## 8. Current best next step

The next best analytic move is:

1. define the first critical boundary after transfer,
2. try to prove it cannot be repaired in the selected-HIGH branch,
3. then separately prove that such a critical boundary must occur after at
   most a bounded number of post-transfer events.

That would turn the current empirical picture into a referee-grade closure
route for the remaining gap.
