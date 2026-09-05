# G4.OPEN `alpha = 1/a` Separation Observation (v1)
**Date:** 2026-03-07  
**Purpose:** package the clean arithmetic fact recovered from the later `G4.OT` draft without overstating its consequence.

## 0) Scope
Work in the near-complete one-div Case-B / Case-iiib setup:
- composite `n >= 10`,
- `E_fix = {1,...,n-1} \ {a,b}`,
- dropped `a` is non-unit: `gcd(a,n) > 1`.

This note is a support observation only.
It does **not** prove a miss interval and does **not** close Case-B.

## 1) Unit/non-unit floor-change separation at `alpha = 1/a`

### Lemma AO.1
Let `a` be a non-unit with `2 <= a <= n-2` and let `e` be a unit runner (`gcd(e,n)=1`).
Then `alpha = 1/a` is a floor-change position of runner `a`, but not of runner `e`.

Equivalently:
- `1/a in {k/a : 1 <= k <= a-1}`,
- `1/a notin {k/e : 1 <= k <= e-1}` for every unit `e`.

### Proof
The first statement is immediate: `1/a` is the `k=1` floor-change point of runner `a`.

For the second, suppose

`1/a = k/e`

for some integer `k` with `1 <= k <= e-1`.
Then

`e = ka`,

so `e` is a multiple of the non-unit `a`.
Because `gcd(a,n) > 1`, every multiple of `a` is also non-unit modulo `n`.
That contradicts `gcd(e,n)=1`.

Hence `1/a` is not a floor-change position of any unit runner. ∎

### Corollary AO.1a
Across the two adjacent open `alpha`-intervals immediately to the left and right of `1/a`,
all unit floor values

`t_e(alpha) = floor(e alpha)`

are constant.

So the entire unit-side coverage union

`U_unit(alpha) := union_{e in E_fix, gcd(e,n)=1} bad_set(e,t_e(alpha),n)`

is locally constant across `alpha = 1/a`.

## 2) Limitation
This observation freezes only the **unit** part of the fixed-side union.

It does **not** freeze the full fixed-side coverage

`U_fix(alpha)`.

Reason:
- fixed non-unit runners whose speeds are divisible by the same prime factors as `a`
  may also have a floor change at `alpha = 1/a`,
- so a band-comparison argument across `alpha = 1/a` cannot treat the non-unit background as constant without further work.

Therefore AO.1 is useful as a support fact for a future constructive-`alpha` route, but it is not by itself a Case-B existence proof.

## 3) Program use
AO.1 should be cited only in the following form:
- "`alpha = 1/a` isolates a unit-frozen comparison point."

It should **not** be cited as:
- a proof that the full fixed-side union is frozen there,
- or a proof that a residue missed by unit runners is missed by all of `U_fix`.

## 4) Status
`PROVED` as a scoped support observation; Case-B existence remains `OPEN`.
