# LRC(7) does not help — and what the hard tuples actually are

2026-09-10. Follows `CASE2_ATTACK_v2.md`. Scripts
`experiments/n8/ok_{window,lowG_structure,relthresh}_v1.py`. Exact rationals.

---

## 1. The `LRC(7)` step is worthless here  `[PROVED — measurement]`

`CASE2_ATTACK_v2` §4 proposed closing the Slack Lemma's window with `LRC(d+1)`, which for
`d ≤ 6` gives `‖m_iσ‖ ≥ 1/7 > 1/8` and hence an open set of admissible `σ`. **That open set
is in the wrong place.**

LRC supplies existence *somewhere on the circle*. The window is a specific interval around
`σ = 0` — and `σ = 0` is exactly where every divisible runner sits at `‖m·0‖ = 0`,
maximally unsafe. The first admissible `σ` for one divisible runner is `1/(8m)`, while the
window's half-width is `≈ 1/V`, `V = max` non-divisible speed. So the window can only fire
when the divisible speeds are **large relative to** the non-divisible ones — a **ratio**
condition, which no existence theorem provides.

The first failure in the enumeration makes it plain:

> `E = (1,2,4,6,8,10,14)`, `a = 3`: divisible `m = 1`, so `σ ≥ 1/8` is needed, but the
> window half-width is `1/14`.

Here `LRC(2)` trivially gives good `σ` — all of `[1/8, 7/8]` — and every bit of it misses the
window. **Existence is free; localisation is the entire problem.**

## 2. The Slack Lemma's true reach  `[EMPIRICAL — exhaustive]`

Over all 411 040 Case-2 tuples in `[1..26]`:

| | count | share |
|---|---|---|
| Slack Lemma **hypothesis** holds | 93 828 | 22.8% of Case 2 |
| …and the window **actually fires** | 61 341 | 65.4% of those, **14.9% of Case 2** |

`CASE2_ATTACK_v2` quoted 40.6%; that was the hypothesis over residue *multisets*, a
different population, and it measured the hypothesis, not the conclusion. As a
witness-producing tool the lemma reaches **14.9%** of Case-2 tuples. v2 hedged this
correctly ("a window, not a witness") but had no number; this is the number.

## 3. What the hard tuples are  `[EMPIRICAL — exhaustive]`

Sorting all 229 061 Case-2 tuples in `[1..24]` by `|G|`, the smallest are

    (2,6,7,8,10,13,14)  0.006387      (1,3,4,5,7,11,24)  0.007170
    (1,2,3,4,5,7,24)    0.007738      (1,4,5,6,7,11,16)  0.007914

— perturbations of the **Case-1 tight instances** and of `{1,3,4,5,7}`, the `(H′)` extremal
set. That is the mechanism: the tight instances have `∫X = 0`, and nearby Case-2 tuples
inherit a small lonely set.

The measurable signal is **three-term additive relations** `e_i + e_j = e_k`:

| | mean `#(a+b=c)` | mean longest AP |
|---|---|---|
| bottom 200 by `|G|` | **4.76** | 4.21 |
| top 200 by `|G|` | **0.77** | 2.77 |

## 4. The dichotomy  `[EMPIRICAL — exhaustive over `[1..24]`]`

`min |G|` by relation count, all Case-2 tuples in `[1..24]`:

| `#(a+b=c)` | tuples | `min |G|` | vs target `93/14560` |
|---|---|---|---|
| 0 | 14 236 | `157/2184 = 0.071886` | **11.3×** |
| 1 | 46 166 | `3275/66976 = 0.048898` | 7.7× |
| 2 | 77 389 | `851/25536 = 0.033326` | 5.2× |
| 3 | 62 143 | `1/60 = 0.016667` | 2.6× |
| 4 | 23 064 | `93/14560 = 0.006387` | **1× — the global minimum** |
| 5 | 5 177 | `29/2464 = 0.011769` | 1.8× |
| 6 | 750 | `13/1680 = 0.007738` | 1.2× |
| 7 | 133 | `5/336 = 0.014881` | 2.3× |
| 8 | 3 | `13/560 = 0.023214` | 3.6× |

`min |G|` falls monotonically from 0 to 4 relations and the global minimum sits at exactly
4. **A tuple with no additive relation at all has `|G| ≥ 0.0719`, eleven times the target.**

> **Proposed architecture.**
> **(A) `≤ 2` relations** — 137 791 tuples, 60% of Case 2 — `min |G| = 0.0333`, a **5× margin**
> over the target. This is the regime where decorrelation should be provable, because the
> relations *are* the correlation: `∫S_7 = 1/7` at the extremum is what additive relations buy.
> **(B) `≥ 3` relations** — 40% — the relations are strong Diophantine constraints and are
> the handle; this is where the tight-instance perturbations live.

The split is honest about its own weakness: (B) is 40%, not a small remainder, and three
linear relations among seven speeds leave four free parameters, so (B) is **not** finite as
stated. Cutting it down is the next question.

## 5. Grades

§1: **PROVED** — the window's failure mode is exhibited with an explicit tuple, and the
reason (localisation vs existence) is structural, not statistical. §2, §3, §4: **EMPIRICAL**,
exhaustive over the stated boxes (`[1..26]`, `[1..24]`), no sampling. The architecture in §4
is a **PROPOSAL** supported by those tables, not a theorem; neither branch is proved, and
(B)'s finiteness is explicitly *not* claimed.
