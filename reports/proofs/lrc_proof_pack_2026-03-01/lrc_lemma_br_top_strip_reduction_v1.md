# Lemma BR: Top-Strip Reduction for Window Maintenance (v1)

**Date:** 2026-03-06
**Status:** Reduction proved; existential avoidance step open
**Scope:** unit-runner branch, prime `n`, `1 in E_non`, Case B (`A_{b_lo} = emptyset`)

---

## 1. Purpose

The `S_0` pigeonhole argument in [lrc_lemma_br_minimax_proof_v1.md] only proves condition 1 for a
candidate witness `r*`:

1. the unique large excluder `e* > n` satisfies `arr(e*, r*) <= budget`.

It does **not** prove condition 2:

2. every co-covering runner `e != e*` keeps covering `r*` for at least `arr(e*, r*)` steps.

This note reduces condition 2 to a finite forbidden-set problem on an affine phase index
`tau_e(r) in Z_n`.

---

## 2. Unit Phase Coordinates at `b_lo`

Write a unit runner as

`e = q_e n + s_e`, with `1 <= s_e <= n-1`, `gcd(s_e, n) = 1`.

For a residue `r in Z_n`, define

`tau_e(r) := (q_e + s_e r) mod n`.

At `b_lo = L/n`, the exact boundary value is

`x0(e, r) = (e (rL + b_lo)) mod nL = L ( tau_e(r) + s_e / n )`.

Therefore:

- `tau_e(r) = 0` iff `r = a_low(e)` is the lower exclusion of `e`.
- `tau_e(r) = n-1` iff `r = a_high(e)` is the upper exclusion of `e`.
- `1 <= tau_e(r) <= n-2` iff `e` covers `r` at `b_lo`.

So the safe/interior phase window for a co-covering runner is exactly the strip

`tau in {1, ..., n-2}`.

---

## 3. Arrival of the Candidate Excluder

Let `r*` be a candidate witness with unique excluder `e* = q_* n + s_*`.

Define

- `A_low(e*) := n - s_*`
- `A_high(e*) := 2n - s_*`

Then:

- if `tau_{e*}(r*) = 0` (lower exclusion), `arr(e*, r*) = L A_low(e*) / (n e*)`
- if `tau_{e*}(r*) = n-1` (upper exclusion), `arr(e*, r*) = L A_high(e*) / (n e*)`

Call the relevant numerator `A_zone(e*, r*)`, so

`arr(e*, r*) = L A_zone(e*, r*) / (n e*)`.

---

## 4. Exact Window Formula for a Co-Covering Runner

Assume `e != e*` covers `r*` at `b_lo`, so `1 <= tau_e(r*) <= n-2`.

Its remaining window from `b_lo` is

`window_from_blo(e, r*) = floor(((n-1)L - x0(e, r*)) / e)`.

Using the formula for `x0`, this becomes

`window_from_blo(e, r*) = floor( L ( n (n-1-tau_e(r*)) - s_e ) / (n e) )`.

Since `arr(e*, r*)` is an integer, the window condition

`window_from_blo(e, r*) >= arr(e*, r*)`

is equivalent to the **exact affine inequality**

`e* ( n (n-1-tau_e(r*)) - s_e ) >= e A_zone(e*, r*)`.

No asymptotic estimate is used here.

---

## 5. Top-Strip Forbidden Set

For a fixed candidate branch `(e*, zone)`, define

`c_e(e*, zone) := ceil( ( e A_zone(e*) + e* s_e ) / (n e*) )`.

Then the previous inequality is equivalent to

`n - 1 - tau_e(r*) >= c_e(e*, zone)`.

So the runner `e` fails window maintenance exactly when

`tau_e(r*) in F_tau(e ; e*, zone) := { n - c_e(e*, zone), ..., n - 2 }`,

where the set is interpreted as empty if `c_e(e*, zone) = 1`.

Thus:

- the forbidden phase strip is always a **top strip** of the safe interval `{1, ..., n-2}`
- its size is `c_e(e*, zone) - 1`
- the strip is usually short

Because `tau_e(r) = q_e + s_e r` is an affine bijection on `Z_n` in the unit regime, each
forbidden phase strip pulls back to a concrete forbidden residue set

`F_r(e ; e*, zone) := tau_e^{-1}(F_tau(e ; e*, zone))`.

Hence window maintenance for a fixed candidate `(r*, e*)` is equivalent to

`r* notin union_{e != e*, e covers r* at b_lo} F_r(e ; e*, zone(r*))`.

This is the reduction.

---

## 6. Relation to the `S_0` Pigeonhole

In the proved `1 in E_non` prime-unit branch:

- small runners define `A_small subseteq {1, ..., n-2}`
- `S_0 = {1, ..., n-2} \\ A_small`
- some `r* in S_0` has exactly one large-runner exclusion
- its unique excluder `e* > n` satisfies `arr(e*, r*) <= budget`

So the remaining `S_0` route becomes a purely finite question:

> Show that among the `S_0` residues with unique large excluder, at least one residue avoids all
> pulled-back top strips `F_r(e ; e*, zone)`.

Equivalently, for at least one such branch `(r*, e*)`, every co-covering runner lies below its
top-strip threshold in `tau`-space.

This is strictly stronger than the previous arrival-only statement and is exactly what is needed
to convert condition 1 into a valid witness **if the `S_0` route is sufficient**.

---

## 6a. Important Negative Result from the Harness

The harness shows that the pure `S_0` unique-large-excluder route is **not** universally enough.

Example:

- `n = 5`
- `E_non = {1, 9, 17}`
- `L = 765`
- `S_0 = {1, 2, 3}`

The `S_0` residues with unique large excluder are:

- `r = 2`, unique excluder `e* = 9`, `arr = 102 <= budget = 228`, but blocked by runner `17`
- `r = 3`, unique excluder `e* = 17`, `arr = 72 <= budget = 228`, but blocked by runner `9`

So every `S_0` unique-large candidate fails condition 2.

However, the tuple still has a valid witness: `r = 1`.
At `b_lo`, residue `1` is excluded by **two** large runners:

- `arr(9, 1) = 17`
- `arr(17, 1) = 27`

Runner `1` keeps covering long enough (`window = 2142`), so the first simultaneous coverage is
at `b = b_lo + 27`, hence `start_run = 27 <= budget`.

Conclusion:

- the top-strip reduction is correct,
- but the existential target cannot be restricted to `S_0` residues with a **unique** large excluder.

Any final proof has to allow at least a wider low-multiplicity candidate class.

---

## 7. W1 Sanity Check

Take

- `n = 7`
- `E_non = {1, 2, 6, 8, 10}`
- `L = 840`

### Bad candidate: `r = 2`

The unique excluder is `e* = 10 = 1 * 7 + 3`, in the lower zone, so

- `A_zone = n - s_* = 4`
- `arr(e*, 2) = 48`

Runner `e = 6` is a co-coverer. Here

- `s_e = 6`
- `tau_6(2) = 5`
- `c_6 = ceil((6 * 4 + 10 * 6) / (7 * 10)) = 2`

So the forbidden strip is `F_tau = {5}`. Since `tau_6(2) = 5`, runner `6` is exactly in the top
strip and fails window maintenance:

`window_from_blo(6, 2) = 20 < 48`.

### Actual witness: `r = 5`

The unique excluder is `e* = 8 = 1 * 7 + 1`, in the upper zone, so

- `A_zone = 2n - s_* = 13`
- `arr(e*, 5) = 195`

For the co-covering runners:

- `tau_1(5) = 5`
- `tau_2(5) = 3`
- `tau_6(5) = 2`
- `tau_10(5) = 2`

Each of these lies below its corresponding top-strip threshold, so no blocker occurs and the
candidate is valid.

This matches the observed `W1` behavior exactly.

---

## 8. Concrete Next Lemma

The proof gap is now one of the following stronger finite statements:

**Option A. Low-multiplicity avoidance lemma.**
In the prime-unit `1 in E_non` branch, there exists a residue `r* in {1, ..., n-2}` whose
excluding-runner set has size `1` or `2`, and whose co-covering runners avoid all relevant
top strips up to the last required arrival time.

**Option B. Two-large-runner synchronization lemma.**
When all `S_0` unique-large candidates are blocked, there exists a residue with exactly two
large excluders whose two arrival times are still below budget and whose co-coverers avoid the
top strips determined by the larger of the two arrivals.

A proof of either statement would move the BR window-maintenance step materially closer to
closure. The harness is designed to search both regimes.

---

## 9. Supporting Script

The accompanying harness

`lrc_lemma_br_top_strip_harness_v1.py`

computes:

- `S_0`
- unique large-excluder candidates
- exact arrival and budget data
- per-runner top-strip thresholds
- exact blocker lists for window failures

It is intended as a search and sanity-check tool for the remaining existential step.
Besides the `S_0` unique-large branch, it also scans residues with one or two excluders so that
counterexamples to the narrow `S_0` route are not missed.
