# Odd Period-3 Phase-Sum Bridge to the Fixed-Point Grammar

## Purpose

The current sharp theorem gap is:

> prove that every odd period-3 attractor is affine-`delta`.

This note does not close that. But it gives the first direct bridge from the
odd period-3 affine hierarchy back into the already closed fixed-point
`d=all` grammar.

## Exact bridge on the affine side

For an odd affine period-3 cycle

- `R0_delta(u,v,w,x,y) = [u,v,w,x,y,y,x,w,v,u+delta]`
- `R1_delta(u,v,w,x,y) = [u,y,v,x,w,w,x,v,y,u+delta]`
- `R2_delta(u,v,w,x,y) = [u,w,y,x,v,v,x,y,w,u+delta]`

let

- `S = R0_delta + R1_delta + R2_delta`

be the phase-sum vector.

Then exactly

- `S = [3u, M, M, 3x, M, M, 3x, M, M, 3u+3delta]`

with

- `M = v+w+y`.

And, crucially,

- `K(S) = S`.

So every affine odd period-3 cycle comes with a canonical fixed-point shadow.

## Meaning

This is the right kind of bridge for the eventual unified paper:

- cycle side: odd period-3 affine hierarchy
- fixed-point side: already closed base-10 `d=all` theorem

The phase-sum vector sits exactly on the fixed-point side.

So the current global strategy becomes much cleaner:

1. prove every odd period-3 attractor is affine-`delta`
2. then its phase-sum automatically lands on the fixed-point grammar

That makes the cycle theorem path converge back into something already
internal, rather than continuing to drift away from the fixed-point proof.

## Fixed-point grammar interpretation

The phase-sum vector has the form

- `[z,A,A,C,A,A,C,A,A,z+q]`

with

- `z = 3u`
- `A = M`
- `C = 3x`
- `q = 3delta`

So the bridge lands on the symmetric branch of the fixed-point grammar, not on
an ad hoc auxiliary object.

In other words:

> odd period-3 affine cycles project naturally onto a fixed-point family.

That is a strong reason to believe the affine-`delta` normal form is not just
a convenient fit but the correct theorem language.

## Verified support

The bridge was checked on three layers:

1. random exact affine period-3 parameter checks: `1000`, zero failures
2. exact reduced odd period-3 census rows at
   - `d=23`
   - `d=25`
   - `d=27`
   - `d=29`
   all with zero failures
3. boundary-thread tail `Z_r` for `r=5..24`, zero failures

So the bridge already covers both currently exposed affine sectors:

- reduced `delta=1`
- boundary `delta=3`

## Honest status

What this proves:

- every currently verified affine odd period-3 family has a fixed-point
  phase-sum shadow

What it does not prove:

- that every odd period-3 attractor is affine-`delta`

So this is a bridge note, not the missing completeness theorem.

But it is now the most natural route to finish the proof:

> force odd period-3 attractors into affine-`delta`, then inherit fixed-point
> structure from the phase-sum shadow.

## Computational support

The script

- `kaprekar_odd_period3_phase_sum_bridge.py`

produces

- `kaprekar_odd_period3_phase_sum_bridge_2026-05-20.json`.
