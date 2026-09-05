# Master Problem 1 SF3 Unit Permanent-Cover Note (v1)
**Date:** 2026-03-07  
**Purpose:** isolate the unit half of `SF3.2-R2`, the bounded-lifetime claim for permanent-cover chains.

## 0) Position in the program
In the SF3 route, overlap collapse is now modeled as a permanent-cover chain:

- a run end exposes a residue,
- the residue is quickly re-covered,
- the path returns to obstruction without creating a new disjoint safe block.

The first theorem target is the unit side of that mechanism.
This note proves that a **single unit runner cannot cover a fixed residue for an arbitrarily long stretch**.

## 1) Unit bad-set algebra
Let `e` be a unit runner, so `gcd(e,n)=1`, and let `r in Z_n` be fixed.

For integer floor state `t`, we have

`bad_set(e,t,n) = { (-t)e^{-1}, (-(t+1))e^{-1} } (mod n)`.

Define

`T_e(r) := { t in Z : r in bad_set(e,t,n) }`.

### Lemma UPC.1 (exact covering states for a fixed residue)
For unit `e` and fixed residue `r`,

`r in bad_set(e,t,n)`

iff

`t == -e r (mod n)`  or  `t == -e r - 1 (mod n)`.

Equivalently, if

`s_e(r) := -e r - 1 (mod n)`,

then

`T_e(r) = { s_e(r) + qn, s_e(r) + 1 + qn : q in Z }`.

So the covering floor states are exactly **two consecutive states modulo `n`**.

### Proof
Because `e` is a unit, multiplication by `e` is invertible mod `n`.
Thus

`r in bad_set(e,t,n)`

iff

`e r == -t (mod n)` or `e r == -(t+1) (mod n)`,

which is exactly

`t == -e r (mod n)` or `t == -e r - 1 (mod n)`.

The two congruence classes differ by `1`, so they are consecutive. ∎

## 2) Coverage geometry in `alpha`
For fixed `r`, define

`Cov_e(r) := union_{t in T_e(r)} ( [t/e, (t+1)/e) intersect I_div )`.

### Corollary UPC.2 (two-state interval blocks)
Each connected component of `Cov_e(r)` is contained in an interval of the form

`[ (s_e(r)+qn)/e, (s_e(r)+2+qn)/e )`

for some `q in Z`.

Hence every connected component of `Cov_e(r)` has `alpha`-length at most

`2/e`,

and consecutive components are separated by a gap of length

`(n-2)/e`.

### Proof
By Lemma UPC.1, the only `t` values contributing to `Cov_e(r)` in one period are

`s_e(r)+qn` and `s_e(r)+1+qn`.

These correspond to two adjacent floor intervals:

`[ (s_e(r)+qn)/e, (s_e(r)+1+qn)/e )`

and

`[ (s_e(r)+1+qn)/e, (s_e(r)+2+qn)/e )`.

Their union has length `2/e`.
The next covering block starts only after `n-2` non-covering states, so the gap is `(n-2)/e`. ∎

## 3) Event-path consequence
Call a **unit `e`-episode for residue `r`** a maximal connected portion of the event path on which

`r in S_e(alpha)`.

### Theorem UPC.3 (unit permanent-cover bound)
Let `e` be a unit runner and `r` a fixed residue.
Then every unit `e`-episode for `r` meets at most two consecutive `e`-floor states.

Equivalently:
- once `e` starts covering `r`, the next `e`-event can preserve coverage at most once,
- the following `e`-event must drop `r` from `S_e`.

So a single unit runner cannot sustain a permanent-cover chain for a fixed residue across three of its own consecutive states.

### Proof
By Lemma UPC.1, the only `e`-floor states that cover `r` are two consecutive classes modulo `n`.
Along the monotone event path, the realized `e`-floor state increases by `1` at each `e`-event.
Therefore, once the path enters a covering state for `r`, it can remain in a covering state for at most one further `e`-state before leaving the two-state block.
After the next `e`-event, the `e`-state is outside `T_e(r)`, so `r notin S_e(alpha)`. ∎

## 4) Consequence for SF3.2
This proves the first local obstruction bound needed for `SF3.2-R2`:

> if overlap collapse inside a short safe block is being sustained by a single unit runner covering a fixed residue, that mechanism has bounded lifetime.

More precisely:
- one unit runner can absorb at most one immediate continuation after the residue first becomes covered,
- after that, either a new safe opening appears or the burden must transfer to another runner.

This does **not** yet close `SF3.2`, because two further steps remain:
- bound how many transfers can occur among different unit runners inside one short safe block,
- prove the analogous bounded-lifetime theorem for non-unit coverers.

## 5) Program status
What is now theorem-grade:
- exact residue-state classification for unit cover of a fixed residue,
- two-state lifetime bound for any single unit cover episode.

What remains open:
- chain-level transfer control,
- non-unit permanent-cover bound,
- final bounded-overlap constant for full `SF3.2`.

## 6) Status
`PROVED` for the unit single-runner bound; `OPEN-PROGRAM-TARGET` for full `SF3.2`.
