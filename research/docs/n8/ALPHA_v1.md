# What reads the deficit: `α`, the concentration of a bad set on the grid's good set

2026-09-10. Follows `RESONANCE_FACTOR_v1.md`. Script `experiments/n8/ok_alpha_v1.py`.
Exact `Fraction` throughout; floats appear only in correlation summaries and are never the
source of a claim.

---

## 1. The decomposition  `[PROVED]`

With `grid = {2,6,8,10,14}`, `G = G(grid)`, and off-grid speeds `x, y`:

    |G(grid ∪ {x,y})| = |G| · (1 − α_x − α_y + α_xy),     α_x = |A_x ∩ G| / |G|

`α_x` is the **concentration** of `x`'s bad set on the grid's good set; the generic value is
`1/4`, giving the familiar `(3/4)² = 9/16`.

## 2. `α` reads it, where height and count do not  `[EMPIRICAL — 490 pairs, exact inputs]`

| predictor | Spearman vs actual survival |
|---|---|
| 3-term relation count | **non-monotonic** — fails (`RESONANCE_FACTOR_v1` §2) |
| minimum height | vacuous — `h = 1` at 98.1% (`WHERE_THE_PROOF_IS_v2` §4a) |
| lowest-height Fourier families | **wrong sign** at `E*` (`RESONANCE_FACTOR_v1` §4) |
| `α_x + α_y` | **0.9371** |
| `(1 − α_x)(1 − α_y)` | **0.9419** |

## 3. At the extremum it is exact  `[PROVED]`

    α_7 = 18/41,   α_13 = 505/1066,   α_{7,13} = 0 exactly
    1 − α_7 − α_13 = 93/1066 = the actual survival

The two off-grid runners delete `α_7 + α_13 = 973/1066 = 91.3%` of the grid's good set —
against a generic `43.75%` — **with zero overlap**. Maximum concentration, no waste.

**Disjointness alone is not the story.** Exact disjointness (`α_xy = 0`) holds for 219 of
490 pairs (44%), and **10 of the 10 largest** survivals are disjoint against only **3 of
the 10 smallest**. It is disjointness *combined with* large individual concentration that
makes the extremum.

## 4. Why height and count could not read it  `[the mechanism]`

Height and relation count measure whether a resonance **exists**. `α` measures whether the
resulting alignment of `A_x` **lands on the grid's good set**. Only the second affects
`|G|`: a resonance that aligns `A_x` with the grid's *bad* set is free. That is not
hypothetical — `α_x = 0` **exactly** for `x ∈ {3, 16, 20, 28, 32}`: those speeds can be
added to the grid at no cost at all, despite having relations to it.

**Self-similarity.** `grid = 2·{1,3,4,5,7}`, so by dilation `α_x` equals the concentration
of `x/2` on `G({1,3,4,5,7})`: `α_16` is that of speed 8, `α_4` that of speed 2 — and `α_4 =
0.6098` is the largest of all, because `2` is exactly what the base tuple lacks from the AP.
`α` at one level is the same object one level down.

## 5. Grades and limits

`[PROVED — exact]` §1 identity; §3 all four values and the exactness of the disjoint model
at `E*`; the `α_x = 0` list.
`[EMPIRICAL]` §2 correlations — one grid, `x,y ≤ 40`, 490 pairs; one-sided.

`α_x` is a **one-runner-against-a-6-tuple** quantity where `|G|` is a 7-tuple quantity, and
by §4 it is recursive, so it is a genuine reduction. It is **not yet a proof tool**: it must
still be computed, and `0.94` is a correlation on one grid, not a theorem. What it settles
is the question it was built to answer — the deficit is read by geometric alignment of bad
set to good set, not by the arithmetic existence of resonances.
