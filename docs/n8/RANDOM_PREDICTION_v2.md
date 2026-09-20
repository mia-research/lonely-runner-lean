# Predicting the moment for randomly chosen non-integer speeds (v2)

2026-09-13. n = 8, individual isolation, threshold 1/8. AP base, **all eight runners displaced at
once**, each to a random non-integer speed in `(i−1, i+1)`. Can the outcome be predicted from the
speeds alone?

**Change in v2**: **C4** of `SKETCH_DEBTS_v2` §4 — the disturbed-runner attainment rate is a step-size artefact, not a constant near one half. Recorded inline where the figures appear; no other claim is altered and no grade moves.

Artifact: `experiments/n8/ok_predict_random_v1.py`.

---

## 1. The prediction is decidable in `O(n)`, and it is exact  `[PROVED — arithmetic]`

For each runner, predict `t* = 1/(8·d_min)`.

For `t < 1/(8·d_min)` we have `d_min·t < 1/8`, so `‖d_min·t‖ = d_min·t < 1/8` and the runner
**cannot** be lonely. Nothing precedes the bound. Therefore a single BSM evaluation at
`t = 1/(8·d_min)` — seven comparisons — settles the matter outright:

- passes ⟹ the moment **is** `1/(8·d_min)`, exactly;
- fails ⟹ the moment is strictly later.

This is a decision procedure, not a heuristic. Verified on two independent populations:

| control | result |
|---|---|
| 1–3 movers, denominators to 1000 | **9,304 of 9,304** |
| **all eight displaced**, `O(n)` check vs **full window construction** | **960 of 960** |

The second is the load-bearing one: the true moment was computed the expensive way, by building
every isolation window over the full period, and compared against the seven-comparison check. The
two routes agree exactly — the cheap predictor is not an approximation of the expensive one, it
returns the same answer. It also puts the at-the-bound rate at 0.5042, against 0.4972 measured on
a larger population with higher denominators.

## 2. How much it decides  `[VERIFIED — exact]`

With all eight displaced, 400 random configurations, 3,200 runner-instances, denominators to 101:

| | count | rate |
|---|---|---|
| moment confirmed **at** the bound | 1,591 | **0.497** |

**C4 — the rate is a step-size artefact.**  `[CORRECTED 2026-09-15]` The attainment rate for
disturbed runners is not a constant near one half. It falls monotonically as the displacement step
is refined:

| step | 1/10 | 1/100 | 1/1000 | 1/10000 |
|---|---|---|---|---|
| rate | 0.4641 | 0.4135 | 0.3800 | 0.3735 |

The figures reported in this file are the two coarsest points of that curve. The cause is the
small-denominator bias recorded at handover 2026-09-12 §2 item 12: a coarse step lands
disproportionately on displacements with small denominators, which are exactly the ones that keep
the spine instant. **The "near one half" reading, and any question asking why the rate sits near
one half, are withdrawn** — the rate has no limit near one half and the question is about the
sampling grid, not about the runners.

| moment known to be **later** | 1,609 | 0.503 |

**About half of a random configuration is settled with no search at all.** The rate falls with the
number of runners displaced — 0.76 with one to three movers, 0.50 with all eight — because each
extra displaced runner adds a difference that can block the bound.

## 3. The other half is cheap, and closely bounded  `[VERIFIED — 1,200 runners]`

When the bound is not attained, merging each constraint's boundary times in increasing order and
stopping at the first hit gives the exact moment:

| | |
|---|---|
| candidates tried, median | **23** |
| candidates tried, max | 6,442 |
| **moment / bound**, median | **1.23** |
| **moment / bound**, max | **2.9** |

So even when the closed form misses, `1/(8·d_min)` is within a factor of about three, and the
median case is within a quarter. The whole run — 1,200 runners including every search — took
1.17 s.

## 4. A note on method

An earlier attempt at this measurement built every isolation window over the full period for each
runner and did not finish in two minutes. The same measurement, done by evaluating BSM at the one
predicted time, took **0.08 s** for 3,200 runners. The cost was entirely in constructing
information the prediction never needed.

## 5. Status and scope

`[PROVED — arithmetic]` §1's decision procedure and the reason nothing precedes the bound.
`[VERIFIED — 9,304 of 9,304]` the check's agreement with the true moment (1–3 movers, denominators
to 1000).
`[VERIFIED — exact]` §2's rates over 3,200 runner-instances; §3's search statistics over 1,200.

**Scope.** AP base only; speeds confined to `(i−1, i+1)` so the ordering never changes;
denominators up to 101 in §2 and 13 in §3. The factor-of-3 bound in §3 is an observed maximum over
that population, **not** a proved bound — nothing here rules out a configuration where the moment
is far beyond `3/(8·d_min)`.

**Not established.** A closed form for the half that misses the bound. Whether the `moment/bound`
ratio is bounded at all.

**n = 8 is not proved here, and is not the target here.**
