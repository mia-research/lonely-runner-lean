# Two reductions of Rosenfeld's Lemma 7 search

2026-09-07. Both are elementary and both are proved. Together they shrink the
search that Rosenfeld reports as ~32 hours at `p = 163`.
Script: `experiments/n8/normalised_search_v1.py` (validated, see §3).

Notation as in `COLLAPSE_Z163_v1.md`: `n = k+1`, `N = np`, `H = N/2`, targets
`j ∈ {1,…,H}`, speeds `v ∈ {1,…,H}` with `p ∤ v`, and `v` covers `j` iff
`jv mod N < p` or `> N−p`.

---

## 1. Unit scaling — WLOG `1 ∈ T`  [PROVED]

For a unit `c` mod `N`, the map `v ↦ cv`, `j ↦ c^{-1}j` permutes `ℤ/N` and fixes
`‖jv/N‖`, so it preserves "T covers every target". It also fixes the `q`-adic
valuation of every speed for each prime `q | N`, so it preserves the gcd side
condition. Composed with the folding `v ↔ N−v` already used to halve the speed
range, the group acting is `(ℤ/N)^* / {±1}`, of order `φ(N)/2`.

The gcd condition says: **for every prime `q | N`, at least two speeds of `T` are
not divisible by `q`.** (A `(k−1)`-subset omits one element, so a subset entirely
inside `qℤ` exists iff at most one speed escapes `q`.) When `n` is a prime power —
`n = 7` and `n = 8`, the two cases in play — the only prime of `N` other than `p`
is that one prime, and `p ∤ v` always, so some speed of `T` is coprime to `N`.
Scaling by its inverse:

> **WLOG `1 ∈ T`.** The search space drops by a factor `φ(N)/2`
> (`= 324` for `N = 1304`).

The speed `v = 1` covers exactly `{1,…,p−1}`, so the search restarts at target `p`
with `k−1` speeds and `H − p + 1` targets left.

*Caveat on scope.* The step "some speed is coprime to `N`" uses `n` a prime power.
For `n` with two distinct prime factors the group still acts, but the normalisation
needs a different representative; do not transcribe it to general `n` unchecked.

## 2. A coarse speed is forced  [PROVED]

For the target `j = p`,

    p·v mod N = p·(v mod n),

which is `< p` only when `v ≡ 0 (mod n)`, and can never exceed `N − p = p(n−1)`.
So

> **`j = p` is covered only by speeds divisible by `n`.**
> Every bad cover contains at least one speed with `n | v`.

The same holds at `j = tp` for every `t` coprime to `n` with `tp ≤ H`
(`t = 1, 3` when `n = 8`). In the notation of `COLLAPSE_Z163_v1` §3 this says
`x ≥ 1`, so with §5 there and the `x = 4` run, the surviving sectors at `p = 163`
are `x ∈ {1,2,3}`.

## 3. Validation  [VERIFIED against the paper]

`normalised_search_v1.py` reproduces the exact `k = 6` pattern Rosenfeld states
in his §7 — Lemma 7 applies at 13, 19, 31, 37, 41 and fails at 17, 23, 29 —
and finds no bad cover for `k = 3` at 7, 11, 13. This is the same pattern the
independent unnormalised implementation (`lemma7_criterion_v1.py`) reproduces, so
the normalisation does not change any answer on the cases where both run.

## 4. Status of the `k = 7` run

`run_k7_primes_v1.py` runs the normalised search over Rosenfeld's 27 primes.
`p = 31` completes in 43 s. Whether `p = 163` completes in a useful time is
**not yet known** — it is running; larger `p` grows both the target count and the
speed count, and the branch factor with them. Nothing here claims the 32-hour
search has been replaced. What is established is a factor-`φ(N)/2` reduction of
the space and a forced first speed, in a pure-Python implementation that has
reproduced every published data point it has been tested against.
