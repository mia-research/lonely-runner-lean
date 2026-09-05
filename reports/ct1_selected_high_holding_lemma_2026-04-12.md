# CT.1 Selected-HIGH Holding Lemma

Date: 2026-04-12
Status: proved local lemma + corrected reduced-gap note

## 1. Purpose

This note formalizes the part of the new `CT.1` direction that is already theorem-grade:

- the exact persistence of a selected HIGH thin residue,
- the exact first-arrival formula for a possible challenger,
- and the resulting reduction of the prime dropped-unit gap.

It does **not** yet prove the full selected-HIGH theorem.
But it turns the current gap into a much sharper object.

## Correction (later on 2026-04-12)

The earlier version of this note pointed toward a large-runner
non-arrival theorem:

`b_f(r^*) >= b_2` for all challengers `f`.

That statement is **false** in general.
Later scans and explicit examples show rare large-runner depth-`1`
cases in which challengers reach `r^*` before or around `b_2`, so the
selected-HIGH branch must be handled by a short post-transfer dynamic
rather than by pure non-arrival.

What survives from this note is still theorem-grade:

- Lemma `S-B`,
- the exact challenger formula,
- and the reduction from vague narrative to explicit arithmetic data.

But the analytic target has changed.
The current repair route is not non-arrival; it is a
post-transfer release theorem, now recorded separately in
`ct1_large_runner_low_thin_release_2026-04-12.md`.

## 2. Setup

Assume:

- `n` is prime,
- `E` is in the prime dropped-unit branch,
- the base fibre `b_0 = L/n` is fully covered,
- and `r^*` is a multiplicity-`1` residue at `b_0` carried by a unit runner
  `e^* = n q^* + rho^*`, with `1 <= rho^* <= n-1`.

At `b_0`, the blocked residues of `e^*` are

- `a_low(e^*) = -q^* (rho^*)^{-1} mod n`,
- `a_high(e^*) = -(q^*+1) (rho^*)^{-1} mod n`.

In this note we assume

`r^* = a_high(e^*)`,

so `r^*` is a HIGH thin residue.

## 3. Lemma S-B (proved)

**Lemma S-B (selected HIGH holding window).**
Let `r^* = a_high(e^*)` as above. Then:

1. `r^*` remains in the bad set of `e^*` for every fibre
   `b` with
   `b_0 <= b < b_2`,
   where
   `b_2 := ((q^*+2)L)/e^*`.
2. `r^*` is dropped from the bad set of `e^*` exactly at the reset fibre `b_2`.
3. The protected holding window length is
   `Delta_high(e^*) = b_2 - b_0 = L(2n-rho^*)/(n e^*)`.

**Proof.**
At the base fibre `b_0 = L/n` one has

`floor(e^* b_0 / L) = floor(e^* / n) = q^*`.

For every `b` with

`(q^*+1)L/e^* <= b < (q^*+2)L/e^*`,

the floor state of `e^*` is `q^*+1`, so

`bad(e^*, floor(e^* b/L), n) = {a_low', a_high'}`

with

- `a_low' = -(q^*+1)(rho^*)^{-1} = r^*`,
- `a_high' = -(q^*+2)(rho^*)^{-1}`.

Hence `r^*` survives the first reset of `e^*`.

At the second reset fibre `b_2 = ((q^*+2)L)/e^*`, the floor state becomes `q^*+2`, so the bad set changes to

- `-(q^*+2)(rho^*)^{-1}`,
- `-(q^*+3)(rho^*)^{-1}`,

and `r^* = -(q^*+1)(rho^*)^{-1}` is dropped.

Finally,

`Delta_high(e^*) = ((q^*+2)L)/e^* - L/n`

and since `e^* = n q^* + rho^*`,

`Delta_high(e^*) = L(n(q^*+2)-e^*)/(n e^*) = L(2n-rho^*)/(n e^*)`.

`square`

## 4. Exact challenger formula

The next step is not heuristic either. It has an exact arithmetic form.

Let another retained runner be

`f = n q_f + rho_f`

with `f != e^*`.

Define

`u_f(r^*) := -rho_f r^* mod n`.

Runner `f` blocks `r^*` at a floor state `t` iff

`t equiv u_f(r^*) mod n`
or
`t equiv u_f(r^*) - 1 mod n`.

So the first future time at which `f` can begin to challenge `r^*` after `b_0` is determined by the smallest positive integer

`lambda_f(r^*)`

such that

`q_f + lambda_f(r^*) equiv u_f(r^*)`
or
`q_f + lambda_f(r^*) equiv u_f(r^*) - 1 mod n`.

The corresponding first challenger fibre is

`b_f(r^*) = ((q_f + lambda_f(r^*))L)/f`.

This gives an exact reduction:

> `r^*` is untouched before its release time `b_2`
> iff `b_f(r^*) >= b_2` for every `f != e^*`.

## 5. Corollary S-B.1 (proved reduction)

**Corollary.**
If `b_f(r^*) >= b_2` for all retained `f != e^*`, then the fibre `b_2` is safe.

**Proof.**
By Lemma S-B, `e^*` is the unique blocker of `r^*` at `b_0` and keeps blocking `r^*` until `b_2`.
If no other retained runner blocks `r^*` before `b_2`, then immediately after the second reset of `e^*` the residue `r^*` is blocked by no runner.
Hence the fibre is safe. `square`

So the prime dropped-unit gap has been reduced to a single exact object:

> control the challenger fibres `b_f(r^*)` for a well-chosen HIGH thin residue.

## 6. Computational sharpening of the reduction

Using the current selected-HIGH rule

- choose the HIGH thin residue with smallest `e`,
- falling back only if no HIGH thin residue exists,

the current data say:

- exhaustive:
  - `n=5`, speeds `<= 15`: `147/147` successes, all depth `0`
  - `n=7`, speeds `<= 14`: `420/420` successes, with exactly `4` depth-`1` cases
- targeted full-cover prime samples:
  - `n=11`, max speed `220`: `500/500` successes, all depth `0`
  - `n=13`, max speed `260`: `250/250` successes, all depth `0`
  - `n=17`, max speed `340`: `150/150` successes, all depth `0`
  - `n=19`, max speed `380`: `100/100` successes, all depth `0`

An earlier bounded scan suggested that the only currently seen depth-`1`
starts under the selected-HIGH rule were the four exhaustive `n=7`
tuples:

- `(2,6,7,8,9,10)`
- `(2,6,7,8,10,11)`
- `(2,6,8,9,10,14)`
- `(2,6,8,10,11,14)`

and in all four the selected HIGH start is exactly

- `e^* = 6 = n-1`,
- `q^* = 0`,
- `rho^* = 6 = n-1`,
- `r^* = 1`.

So the first observed selected-HIGH depth-`1` behavior lay in the same
extremal family:

> `q^* = 0` and `e^* = n-1`.

Later larger-speed searches found rare large-runner depth-`1` cases as
well, so the extremal family is not the whole story.
Those later examples do, however, preserve the same broader dynamic
shape: rapid post-transfer destabilization after the selected HIGH
residue loses privileged control.

## 7. Practical consequence

This gives the cleanest current split of the prime gap:

### Large / non-extremal selected-HIGH regime

If the selected HIGH thin residue has

- `q^* >= 1`, equivalently `e^* > n`,

then depth `0` is overwhelmingly dominant in the current scans, but it
is not universal.
So the large-runner target is **not** a universal challenger
non-arrival theorem.

The corrected target is:

> once the selected-HIGH start enters a genuine post-transfer phase, the
> resulting thin-release dynamic forces a safe fibre soon afterwards.

### Extremal selected-HIGH regime

If

- `q^* = 0`,
- `e^* = n-1`,

then the only currently known nontrivial behavior is the `n=7` prototype family, where a single transfer occurs before the safe fibre.

So the full selected-HIGH theorem has reduced to:

1. a post-transfer release theorem in the large-runner regime, and
2. an extremal prototype family which now appears to follow the same
   release pattern.

## 8. Current closure status

What is now genuinely proved:

- Lemma S-B itself,
- the exact challenger-arrival formula,
- and the reduction of the prime branch to challenger control for a selected HIGH thin residue.

What remains open:

- a theorem identifying the earliest forced low-thin release after a
  selected-HIGH transfer,
- and the clean unification of the large-runner and extremal
  depth-`1` families under that release mechanism.

So the gap is not fully closed yet.
But it is now sharply localized in a way that was not available before this selected-HIGH formulation.
