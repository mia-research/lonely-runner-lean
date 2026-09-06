# D7 — iterating the block recursion, and what the φ(n) law contributes

2026-09-07. Continues `D7_ATTACK_v3.md`. Two questions asked and answered; both
negative, both with exact reasons.

## 1. The φ(n) law: same points, no new leverage

`lrc_ap_phi_n_law_v1` (Zenodo 10.5281/zenodo.18158886) proves, for **arithmetic
progressions with common start**, that perfect isolation (gap exactly `1/n`)
occurs precisely at times `{δt} = r/n` with `gcd(r,n) = 1`, and that there are
`φ(n)` such instants per phase period.

Translated into the covering coordinates (`n = k+1`, `N = (k+1)p`, time `j/N`):
those isolation times are `j = rp` with `gcd(r, k+1) = 1` — **exactly the
`d_t = k+1` targets** already isolated by the `j = tp` chain in `v2`. The two
analyses meet on the same points, which is a consistency check and nothing more.

Why it cannot extend:

- Its scope is **arithmetic progressions**, which the paper itself calls "an
  infinitesimally small fraction of the space of all speed assignments" and
  explicitly *not* a general-`n` result. Our obstruction tuples are not APs —
  `{1,6,7,8,9,15}`, `{1,4,12,13,14,16,20}`, `{1,5,53,54,55}`.
- What it does give is that **an AP can never be a bad cover** (it always leaves
  the `φ(k+1)` isolation times uncovered). True, but a measure-zero exclusion.
- Its §6 "n = 8 anomaly" is about floating-point fragility in AP tests, unrelated
  to Rosenfeld's `n = 8`.

**Verdict: consistency check, no leverage.** Recorded so it is not revisited.

## 2. Iterating the recursion inside a block — the exclusive zone does not exist

`v3` §3 established, exactly: if `(k+1) | t·v` then `v` covers `tp + s` iff `v`
covers `s`. The proposed continuation was to iterate — treat the block around
`tp` as a scaled copy of the problem at the origin, delegated to
`T_t = {v : d_t | v}`, and recurse.

**That fails, and the reason is sharp.** For general `v`, write
`r = t·v mod (k+1)`. Then `v` covers `tp+s` iff

    ‖ r/(k+1)  +  s·v/N ‖  <  1/(k+1).

Three regimes:

| `r` | condition | cost |
|---|---|---|
| `0` | `‖s·v/N‖ < 1/(k+1)` — i.e. `v` covers `s` | the clean recursive case |
| `k` (`≡ −1`) | `0 < s·v < 2p` | **almost free** |
| `1` | `s·v` near `N` | expensive |

The values `r = 0` and `r = k` sit at distance **exactly** `1/(k+1)` from an
integer — on the boundary — so an arbitrarily small nudge `s·v` pulls the `r = k`
speeds inside. The block therefore is **not** the exclusive responsibility of
`T_t`; every speed with `t·v ≡ −1 (mod k+1)` joins immediately.

**Verified on the `k=5, p=19` obstruction** `T = (1,5,53,54,55)`, whose only
`6`-divisible speed is `54`:

```
  j = p+0 = 19  covered by [54]          r=0
  j = p+1 = 20  covered by [5]           r=5=k     <-- not in T_t
  j = p+2 = 21  covered by [5,54,55]     r=5,0,1
  j = p+3 = 22  covered by [5]           r=5
```

`j = p+1` is covered by `v = 5`, and `6 ∤ 5`. The exclusive zone is empty at
`s = 1`. Consequently the recursion has no base to iterate on, and the corollary
I had drawn from it — "`T` contains a speed divisible by `k+1` **and** less than
`p`" — is **false**: here the only `6`-divisible speed is `54 > 19 = p`.

## 3. Running tally of closed routes

| route | why it fails |
|---|---|
| counting | slack factor `≈ 2`, independent of `p` |
| window width | `kill(T)` unbounded (2862 vs true death at 23) |
| `j = tp` chain | is Lemma 4 |
| block counting | sub-tuples nest rather than compete |
| **block recursion** | **no exclusive zone: `r ≡ −1` speeds enter at `s·v < 2p`** |
| **φ(n) law** | **same points; AP-only, measure zero** |

## 4. What survives

Only one positive statement from this line, and it stands unaltered:

> If `(k+1) | t·v` then `v` covers `tp + s` **iff** `v` covers `s` — exactly, no
> approximation. (Zero counterexamples over `k ∈ {5,6,7}`, `p ∈ {11,…,41}`, all
> valid `t`, all admissible `v`, `s < 40`.)

It is a true self-similarity; it simply does not isolate a block, because the
`r ≡ −1` speeds are not excluded.

The boundary phenomenon is itself the finding worth carrying: **`1/(k+1)` is
attained exactly at `r ∈ {0, k}`**, so the covering problem has no strict
separation between "the speeds that serve a block" and the rest. Any future
argument that tries to localise responsibility for a region of times will hit
this same degeneracy, and should be designed knowing it.

D7 remains open.
