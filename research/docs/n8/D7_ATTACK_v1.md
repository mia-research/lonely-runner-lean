# Attacking D7 in the n=8 setting — the width route, and why it does not close

2026-09-07. Artifacts: `experiments/n8/window_width_v1.py`,
`enumerate_bad_covers_v1.py`, `lemma7_criterion_v1.py`.

D7 = Conjecture 5.2-H / 5.2-SR-H ("the union of blocked sets is not everything")
= Rosenfeld's Lemma 6 for all large `p`. Attacked here in the n=8 setting, where
`p` is a free parameter.

## 1. An exact width formula (established)

A lonely interval of a tuple `T` has endpoints `a = (m + 1/(k+1))/vᵢ` and
`b = (m' − 1/(k+1))/vⱼ` for some `vᵢ, vⱼ ∈ T`. Hence

    b − a  =  [ (k+1)(vᵢ m' − vⱼ m) − (vᵢ + vⱼ) ] / [ (k+1)·vᵢ·vⱼ ]

The numerator is a **positive integer**, so

    width  ≥  1 / ( (k+1)·vᵢ·vⱼ ).

The grid `{j/N}`, `N = (k+1)p`, must hit any interval of width `≥ 1/N`. Therefore

> **`T` cannot obstruct once `p ≥ kill(T) := min over lonely intervals of vᵢvⱼ`.**

**Verified, and tight in one case.** For the `k = 6` obstruction
`T = {1,6,7,8,9,15}`: its single lonely interval `[15/49, 13/42]` has width
exactly `1/294 = 1/(7·42)`, endpoints from `v = 7` and `v = 6`, product `42`.
`kill(T) = 42` — matching exactly the empirical finding that the `k=6`
exceptions stop at `p ≥ 42`. For the `k = 7` obstruction `{1,4,12,13,14,16,20}`,
`kill = 192` (it in fact dies at `p = 43` by alignment, so the bound is
sufficient, not necessary).

## 2. The route does NOT uniformize — refuted

The hope was: bound `kill(T)` by some `f(k)` over all tuples; then `p > f(k)`
kills every obstruction and Rosenfeld's conjecture follows. **That fails.**

Enumerating bad covers at `k = 5` (where the truth is: obstructions exist for
`p ≤ 19`, none for `p ≥ 23`):

| `p` | example bad cover | `kill(T)` | max speed | cap `N/2` |
|---|---|---|---|---|
| 11 | `(1,6,13,14,15)` | 182 | 15 | 33 |
| 13 | `(1,6,18,19,24)` | 144 | 24 | 39 |
| 17 | `(1,21,24,40,41)` | **840** | 41 | 51 |
| 19 | `(1,5,53,54,55)` | **2862** | 55 | 57 |
| 23 | *none* | — | — | 69 |

`kill(T)` grows with `p` and reaches 2862 while the true death occurs at
`p = 23`. Bad covers do **not** have to use small speeds — at `p = 19` the
obstruction uses speeds up to 55 against a cap of 57. So the width bound is far
from tight, and **no uniform bound on `kill(T)` exists to be proved.** The
obstruction dies for a reason the width alone does not see.

## 3. Why counting cannot close it either — now quantified

Each speed `v` covers a set of density `2/(k+1)` in `{1,…,N}`, so about `p`
values of `j` in `{1,…,N/2}`. Then `k` speeds cover at most `kp`, and the target
has `(k+1)p/2` elements. Coverage is numerically possible whenever

    kp ≥ (k+1)p/2   ⟺   k ≥ 1,

with a slack factor `2k/(k+1) ≈ 2` that is **independent of `p`**. So counting
never rules out a cover, at any `p`. That is exactly the failure recorded in
`lrc_v11_9_srh_analysis_session_2026_05_28b.md` (`2(n−2) > n`, "averaging
fails"), now with its scaling made explicit: the deficit is a constant factor,
not something that improves with the parameter.

## 4. Where the content actually is

Both the counting route (§3) and the width route (§2) fail, and they fail for
complementary reasons: counting ignores *where* the covered sets sit, and the
width bound ignores *that the tuple must cover at all*. What kills an obstruction
is neither its window width nor a cardinality deficit but the **arrangement** —
the covered sets of `k` speeds cannot be positioned to leave no gap once `N` is
large, despite having ample total measure.

The one structural constraint found, recorded because it is exact and may seed a
real argument: since `N − p = kp > N/2` for `k ≥ 2`, no speed `v ≤ N/2` can cover
`j = 1` via the upper arc. So **every bad cover must contain a speed `v < p`.**
Iterating on `j = 2, 3, …` gives a chain of such conditions (`j = 2` forces some
`v < p/2` or `v > kp/2`, and so on). Whether that chain can be pushed to a
contradiction is untested.

## 5. Status

- §1 width formula and the per-tuple `kill(T)` bound: **proved and verified**.
  They explain the observed exception patterns exactly and are reusable.
- §2: the natural uniformization is **refuted** by explicit counterexample
  tuples, not merely unproven.
- §3: the counting route's failure is now quantified as a `p`-independent
  constant-factor deficit.
- §4: the arrangement question is untouched. **D7 remains open**, and this
  document narrows rather than closes it.

No claim here is that D7 is unreachable — two specific routes are closed, with
reasons, and a third (the `j = 1, 2, 3, …` chain) is identified and untested.
