# G4B Unit `z=0` Event Count Lemma (v1)
**Date:** 2026-03-07  
**Purpose:** salvage the clean per-runner counting fact from the later O1/O2 closure draft without over-promoting it to a safe-fibre theorem.

## 0) Scope
Let `n >= 3`.
Let `e` be a unit runner with

`gcd(e,n)=1`,
`2 <= e <= n-1`,

and let `L` be divisible by `e`.

Write the open interior of the divisible band as

`I_div^o := (L/n, (n-1)L/n)`.

This note counts the positions

`b = mL/e`

of runner-`e` `z=0` events that fall in `I_div^o`.

## 1) Exact count

### Lemma UZ0.1
The number of integers `m` with

`L/n < mL/e < (n-1)L/n`

is exactly

`e - 1`.

Equivalently, the interior `z=0` events of runner `e` are precisely

`b_m = mL/e`,  `m = 1,2,...,e-1`.

### Proof
Divide the inequality by `L/e` to obtain

`e/n < m < e(n-1)/n`.

Because `2 <= e <= n-1`, we have

`0 < e/n < 1`,

so the smallest admissible integer is `m=1`.

Also,

`e(n-1)/n = e - e/n`,

and again `0 < e/n < 1`, so this upper bound lies strictly between `e-1` and `e`.
Hence the largest admissible integer is `m=e-1`.

Therefore the admissible integers are exactly

`1,2,...,e-1`,

which gives `e-1` interior events. ∎

### Corollary UZ0.1a
For `e=1`, there are no interior `z=0` events in `I_div^o`.

## 2) Limitation
This lemma is **only** a per-runner event count.

It does **not** imply a lower bound on distinct safe fibres, because:
- different runners can have coincident `z=0` events,
- multiple runner events may collapse onto the same fibre,
- counting runner-events is not the same as counting distinct safe fibres.

So UZ0.1 may be used as a local input to a later collision/occupancy theorem, but it is not by itself a proof that

`B_safe >= n`.

## 3) Status
`PROVED` as a support lemma; no branch status changes.
