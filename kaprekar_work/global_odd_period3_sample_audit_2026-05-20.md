# Global Odd Period-3 Sample Audit

## Purpose

The sharp unresolved theorem claim is:

> every odd period-3 attractor is affine-`delta`.

This note does **not** prove that claim.
Its role is narrower:

> audit the full odd count-state universe across a broad sampled window and
> check whether any sampled period-3 attractor violates affine-`delta`.

That is the right non-drifting empirical check for the current theorem path.

## Sample window

I sampled `5000` random full odd count states at each dimension

- `d=19`
- `d=21`
- `d=23`
- `d=25`
- `d=27`
- `d=29`
- `d=31`
- `d=33`
- `d=39`
- `d=45`
- `d=55`

For each sample:

1. iterate to its eventual attractor in count space
2. if the attractor period is `3`, canonicalize the 3-cycle
3. test whether all three phases fit affine-`delta`

## Result

There were **zero** sampled non-affine odd period-3 attractors.

Exact sample summary:

- `d=19`: `1` distinct sampled period-3 attractor, all affine, `delta={1}`
- `d=21`: `4`, all affine, `delta={1}`
- `d=23`: `10`, all affine, `delta={1}`
- `d=25`: `21`, all affine, `delta={1}`
- `d=27`: `39`, all affine, `delta={1}`
- `d=29`: `66`, all affine, `delta={1}`
- `d=31`: `105`, all affine, `delta={1}`
- `d=33`: `159`, all affine, `delta={1}`
- `d=39`: `416`, all affine, `delta={1,3}`
- `d=45`: `812`, all affine, `delta={1,3}`
- `d=55`: `1658`, all affine, `delta={1,3,5}`

So the full-state samples support both parts of the current grammar picture:

1. no sampled odd period-3 attractor fell outside affine-`delta`
2. the higher `delta` levels appear exactly in the order predicted by the
   affine hierarchy

## Meaning

This does not close the theorem.
But it does remove one important practical worry:

- the affine hierarchy is not merely fitting the reduced sector and the
  explicit boundary thread while missing obvious global counterexamples

Within the current sampled full odd universe, no such counterexample appeared.

## Honest status

What this supports:

- affine-`delta` is the right global odd period-3 candidate normal form
- `delta=1,3,5` already appear in the full odd universe, not just in isolated
  constructed families

What it does not prove:

- that every odd period-3 attractor globally is affine-`delta`
- that no higher odd `delta` level fails to occur in the full universe

So this is an audit note, not a theorem note.

## Computational support

The script

- `kaprekar_global_odd_period3_sample_audit.py`

produces

- `kaprekar_global_odd_period3_sample_audit_2026-05-20.json`.
