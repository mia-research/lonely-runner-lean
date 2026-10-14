# Why 13 and 19 work at `k = 6` — the mechanism, exactly

2026-09-07. Artifacts: `experiments/n8/lemma7_criterion_v1.py`,
`experiments/n8/enumerate_bad_covers_v1.py`.

## Summary

Rosenfeld's Lemma 7 criterion is a question about **a fixed real interval being
hit or missed by an arithmetic grid**. For `k = 6` the whole exception pattern is
produced by a single 6-tuple, and the answer is exact and elementary.

## 1. The obstruction is one small, `p`-independent tuple

Enumerating bad covers for the failing primes `p = 11, 17, 23, 29` shows the same
short tuples recurring, with entries far below the `⌊7p/2⌋` cap and independent
of `p`. One appears for **every** failing prime:

    T = {1, 6, 7, 8, 9, 15}

Tested directly, `T` covers `{1,…,⌊7p/2⌋}` for exactly
`p = 11, 17, 23, 29` and fails to cover for `p = 13, 19, 31, 37, 41, 43`.
That is precisely the `k = 6` pattern — Rosenfeld's "true for all prime `p`
larger than 31 and for 13 and 19 (it is not true for 17, 23 and 29)".

*(Other bad covers exist at those primes; the claim is that `T`'s own pass/fail
set coincides with the observed one over the tested range, so nothing else
obstructs later than `T` does.)*

## 2. What `T` actually is: a runner set with one narrow lonely window

Computed exactly over the rationals, the set of `x ∈ (0,1/2)` with
`‖xv‖ ≥ 1/7` for all `v ∈ T` — the times at which all six runners are lonely —
is a **single interval**:

    [15/49, 13/42]        length 1/294 ≈ 0.003401

LRC for `k = 6` (Barajas–Serra) guarantees this set is nonempty. It happens to be
narrow.

## 3. The criterion is whether the grid lands in that window

Lemma 7 asks about candidate times on the grid `{j/N : 1 ≤ j ≤ N/2}`, `N = 7p`.
`T` covers everything exactly when the grid **misses** the lonely window. Scaling
by `N = 7p`, the window in `j`-space is

    [15p/7,  13p/6]       length  p·(13/6 − 15/7) = p/42

so:

| `p` | `[15p/7, 13p/6]` | integer inside | Lemma 7 |
|---|---|---|---|
| 11 | 23.57 – 23.83 | no | fails |
| 13 | 27.86 – 28.17 | **28** | applies |
| 17 | 36.43 – 36.83 | no | fails |
| 19 | 40.71 – 41.17 | **41** | applies |
| 23 | 49.29 – 49.83 | no | fails |
| 29 | 62.14 – 62.83 | no | fails |
| 31 | 66.43 – 67.17 | **67** | applies |
| 37 | 79.29 – 80.17 | **80** | applies |

The integers `28, 41, 67, 80` are exactly the uncovered times the search reports
at `p = 13, 19, 31, 37`. **13 and 19 work because `28/91` and `41/133` land
inside `[15/49, 13/42]`; 17, 23, 29 fail because no grid point does.**

Independent confirmation: the exhaustive search finds `p = 31` and `p = 37` clean
(300 s and 909 s respectively), agreeing with the prediction.

## 4. Why the exceptions stop

The `j`-space window has length `p/42`, so it **must** contain an integer once
`p ≥ 42`. Past that this obstruction can never recur — which is exactly why "all
large `p` work" for `k = 6`, and it is not a coincidence or a numerical accident.

## 5. The general reformulation, and where the difficulty actually sits

Lemma 7 fails for `(k, p)` **iff** some admissible `k`-tuple `T` has *all* of its
lonely intervals missed by the grid `{j/N}`, `N = (k+1)p`. A lonely interval
`[a,b]` is missed iff no integer lies in `[Na, Nb]`, an interval of length
`N(b−a)`. LRC for `k` guarantees the lonely set is nonempty, so **each fixed
tuple dies once `N·(width) ≥ 1`.**

That gives Rosenfeld's conjecture ("Lemma 6 holds for all large `p`") a precise
shape — and shows precisely what is missing. As `p` grows the admissible tuples
grow with it (entries up to `N/2`), and tuples with larger entries can have
narrower lonely windows. So a proof needs a **uniform lower bound on the widest
lonely interval, over all admissible `k`-tuples**:

> **Target.** For each `k`, find `c_k > 0` and an exponent such that every
> `k`-tuple of distinct positive integers with entries `≤ M` admits a lonely
> interval (all `‖xv‖ ≥ 1/(k+1)`) of length at least `c_k / M^{?}` — strong
> enough that `N(b−a) ≥ 1` for all admissible tuples once `p` exceeds a bound.

This is a **quantitative strengthening of LRC**: not merely "a lonely time
exists", but "a lonely time exists with room around it". That is the real content
of the conjecture Rosenfeld floats, and it is stated here in a form that can be
attacked or refuted.

Adjacent known work worth pulling: Giri–Kravitz, *The structure of Lonely Runner
spectra* (arXiv:2304.01462**v4**; MPCPS, doi:10.1017/S0305004125101497) studies
the achievable values of maximum loneliness. Window *width* is not the same
object as spectrum, but it is close enough that their machinery is the first
place to look.

## 6. Status

- The `k = 6` mechanism above: **verified computationally**, exactly, over
  `p ≤ 37`, with the arithmetic criterion matching the exhaustive search.
- The general reformulation in §5: a **restatement**, not a theorem. No bound on
  window width is proved here, and the uniformity over growing tuple families is
  exactly the open part.
- Not yet checked: whether the same single-tuple analysis explains `k = 7`'s lone
  exception at `p = 41`. That is the sharpest available test of the mechanism and
  is running.
