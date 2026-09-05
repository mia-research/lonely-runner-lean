# Odd Period-3 Pairwise-Symmetry Reduction

## Purpose

The current sharp odd-cycle theorem debt is:

> prove that every odd period-3 attractor is affine-`delta`.

This note does not close that globally. But it isolates the cleanest remaining
reduction:

> if odd period-3 attractors satisfy
> 1. phase-sum fixedpoint, and
> 2. phasewise asymmetry constancy,
> then pairwise symmetry is forced.

Once that is in hand, the affine-`delta` normal form is no longer a speculative
fit. It becomes the natural next normal form.

## Setup

Let

- `C0 -> C1 -> C2 -> C0`

be an odd period-3 cycle in base 10, written in count space.

Define the asymmetry vector

- `A(C) = (c9-c0, c8-c1, c7-c2, c6-c3, c5-c4)`.

Let the phase-sum vector be

- `S = C0 + C1 + C2`.

Assume:

1. **phase-sum fixedpoint**: `K(S)=S`
2. **phasewise asymmetry constancy**:
   `A(C0)=A(C1)=A(C2)=(delta,a,b,c,d)`.

The goal is to show that this already forces

- `a=b=c=d=0`

on the inner complementary pairs, i.e.

- `c1=c8`
- `c2=c7`
- `c3=c6`
- `c4=c5`

phasewise.

## Lemma 1 — asymmetry triples on the phase sum

Because asymmetry is linear in the digit counts,

- `A(S) = A(C0)+A(C1)+A(C2)`.

Under phasewise asymmetry constancy this becomes

- `A(S) = (3*delta, 3*a, 3*b, 3*c, 3*d)`.

So the inner asymmetry of the phase-sum fixed point is divisible by `3`
coordinatewise.

## Lemma 2 — fixed points admit only two inner asymmetry types

By the already closed fixed-point theorem stack, every nontrivial base-10 fixed
point lies on one of the four lead/tail branches

- `(5,5)`
- `(6,2)`
- `(8,2)`
- `(9,1)`.

And by the inner-asymmetry lemma, the inner asymmetry vector

- `(c1-c8, c2-c7, c3-c6, c4-c5)`

for a fixed point is exactly one of:

- `(0,0,0,0)` on the `P`, `O`, and `E` branches
- `(1,-1,-1,1)` on the unique classical `C` branch.

So there are only two possible inner asymmetry types for base-10 fixed points:

- the zero type
- the classical `6174` type.

## The reduction theorem

Under the two assumptions above, the phase-sum fixed point `S` cannot lie on
the classical `C` branch.

Reason:

- if `S` were classical, its inner asymmetry would be `(1,-1,-1,1)`
- but by Lemma 1 its inner asymmetry is `(3*a, 3*b, 3*c, 3*d)`
- no coordinate of `(1,-1,-1,1)` is divisible by `3`

So the classical branch is impossible.

Therefore `S` must lie on the symmetric side of the fixed-point grammar, and
its inner asymmetry must be

- `(0,0,0,0)`.

Hence

- `3*a = 3*b = 3*c = 3*d = 0`

and therefore

- `a=b=c=d=0`.

So each phase satisfies

- `c1=c8`
- `c2=c7`
- `c3=c6`
- `c4=c5`

and the only surviving phasewise asymmetry is the outer odd defect

- `delta = c9-c0`.

This proves the reduction.

## Corollary — pairwise-symmetric odd-defect form

Every odd period-3 cycle satisfying the two assumptions above has phases of the
form

- `[u0,v0,w0,x0,y0,y0,x0,w0,v0,u0+delta]`
- `[u1,v1,w1,x1,y1,y1,x1,w1,v1,u1+delta]`
- `[u2,v2,w2,x2,y2,y2,x2,w2,v2,u2+delta]`

with one common odd defect `delta`.

Since the total digit count is odd,

- `d = 2(u_i+v_i+w_i+x_i+y_i) + delta`,

so `delta` is automatically odd.

This is not yet the full affine-`delta` theorem, because it does not yet force
the phase-rotation law on `(v,w,y)` or the common `u,x` structure. But it does
remove the main conceptual obstacle:

> once the two invariants are proved globally, the odd period-3 side is forced
> into the pairwise-symmetric odd-defect regime.

## Why this helps the global theorem

Before this note, the odd period-3 theorem debt still looked like a direct
normal-form completeness problem.

After this note, the debt is cleaner:

1. prove phase-sum fixedpoint globally
2. prove phasewise asymmetry constancy globally
3. then pairwise symmetry follows automatically by the fixed-point theorem

So the odd period-3 proof is now tied directly back into the fixed-point
`d=all` theorem rather than drifting away from it.

## Verified support

The reduction hypotheses were checked on all currently exposed odd period-3
sectors using

- `kaprekar_odd_period3_reduction_audit.py`

with output

- `kaprekar_odd_period3_reduction_audit_2026-05-20.json`.

Results:

- exact reduced odd census at `d=23,25,27,29`: `136/136` period-3 attractors
  satisfy both hypotheses
- boundary-tail slice `Z_r`, `r=5..24`: `20/20` satisfy both hypotheses
- sampled global odd states at
  `d=19,21,23,25,27,29,31,33,39,45,55`:
  zero sampled period-3 violations

So the reduction is not yet a full theorem, but it is already aligned with
every currently exposed odd period-3 sector.
