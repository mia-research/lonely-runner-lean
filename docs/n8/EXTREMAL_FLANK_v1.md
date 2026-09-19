# The extremal flank exception, and what it hands us

Method: go at the worst case exhaustively, read the mechanism off it in the framework's own
objects, then state the lead. No imported instrument.

Lean: `experiments/n8/Openings_v1.lean` (4 theorems), `experiments/n8/FirstLap_v1.lean`
(5 theorems). Zero errors; the `Openings` file needs only `[propext, Quot.sound]`.
Scripts: `max_shadowed_flanks_v1.py`, `survivor_v1.py`, `L_equals_e_v1.py`,
`window_reach_v1.py`.

---

## 0. A correction to carry forward

The previous round measured "union coverage" and "summed density" per flank. Both came back
**flat** — `0.81` and `1.2–1.5` across every rank — and explained nothing. Density is not a
framework object, and the flat reading is the tell. Every result below is stated in openings,
readings, gcds and residue classes.

## 1. The extremal exception

**[VERIFIED — exhaustive]** Over all 645,482 multisets of seven positive differences drawn
from `[1,20]` with `gcd = 1`:

* the maximum number of shadowed flanks is **6 of 7**;
* it is attained by exactly **one** multiset, `(2,3,4,5,6,7,16)`;
* multisets with **zero** clear flanks: **none**.

Differences may be taken positive because `dist(-x, ℤ) = dist(x, ℤ)`, and as a multiset
because a pair `d, -d` in an arrangement repeats.

## 2. A flank has exactly `e` openings

**[PROVED — `Openings.lcm_div_eq`]** Put `g_j = gcd(d_j, e)` and `q_j = e/g_j`. When the
multiset has `gcd = 1`, `gcd_j g_j = gcd(gcd_j d_j, e) = 1`, and then

```
    L = lcm_j (e / g_j) = e .
```

Elementary, no factorisation: `L ∣ e`, and with `m = e/L` every `e/g_j ∣ e/m` forces `m ∣ g_j`,
so `m ∣ 1`. **[VERIFIED]** on 1,331,924 flanks before proving.

Two consequences. Flank `e` carries **exactly `e` openings**; and `d_max` is the flank with the
most openings, so "the surviving flank is `d_max`" and "the surviving flank has the largest `L`"
are the **same statement**, not two competing explanations. In the extremal set the openings run
`2, 3, 4, 5, 6, 7, 16` — exactly the differences.

## 3. The native covering count

**[VERIFIED — 9,323,468 movers]** Mover `d` covers exactly `c · gcd(d,e)` of the `e` openings,
`c` being its blocked classes mod `q`. So shadowing needs

```
    Σ_j c_j · gcd(d_j, e)  ≥  e .
```

**This is necessary and not sufficient**, and the extremal set is the proof: at `e = 16` the
count is `24 ≥ 16` with slack 8, and the flank is clear anyway. Overlap decides. (An earlier
draft of the script labelled that row "shadowed" off the count alone — the label was wrong.)
**[VERIFIED]** the inequality holds on all 58,809 shadowed flanks sampled, tight at slack 0.

## 4. Why the survivor survives: first-lap clearance

Read directly off `e = 16`, which is clear at `A = 9`: the products `9·d` for `d = 2,…,7` are
`18, 27, 36, 45, 54, 63`. Every one lies in `[16, 112] = [e, 7e]`, and none reaches `8e = 128`.
**There is no modular reduction at all** — the residue is the product.

**[PROVED — `FirstLap.flank_clear_of_window`]**

> If every other difference satisfies `e ≤ d·A ≤ 7e` for some `A = 8k+1 > 0`, the flank is
> clear at `A`, so the subject is lonely at `t = A/(8e)`.

No hypothesis on denominators, on sizes, or on which flank it is. The flank itself is exempt,
since a flank never blocks its own openings.

**[PROVED — `FirstLap.extremal_survivor`]** The extremal exception is closed in Lean: every
`d ∈ [2,3,4,5,6,7]` has `¬ inWay d 9 16`.

An admissible `A` exists iff `e/d_min' ≤ A ≤ 7e/d_max'` contains an `A ≡ 1 (mod 8)`, which
needs the other differences inside a ratio-7 window. For `e = 16` that window is `[8, 16]` and
`A = 9` is the **unique** admissible opening.

## 5. Reach, and what it does not do

**[VERIFIED]** Frequencies under uniform sampling of multisets, stable with range:

| range | some flank has a window | `d_max` has a window | `max ≤ 7·min` (earlier theorem) |
|---|---|---|---|
| ±20 | 53.01% | 14.30% | 49.60% |
| ±200 | 43.15% | 9.23% | 40.66% |
| ±2000 | 42.56% | 8.80% | 40.39% |

Soundness **[VERIFIED]**: all 30,537 windows found genuinely clear their flank. On the extremal
set the criterion separates perfectly — a window at the one clear flank, none at the six
shadowed ones.

The negative reading matters as much: `d_max` admits a window only ~9% of the time. So
first-lap clearance identifies the survivor in the extremal case but does **not** explain any
general "`d_max` is protected" principle, and must not be cited as one.

## 6. The lead

The exception says a flank survives when its openings outrun the cover. Two proved handles now
exist on that: `L = e` fixes the opening count exactly, and first-lap clearance settles the
no-wrap regime outright. What is owed is the wrapping regime — where `d·A` exceeds `8e` and the
residue genuinely reduces. That is where the remaining ~57% sits, and it is the next thing to
attack at its own worst case rather than in aggregate.

Existence at order 8 remains open.
