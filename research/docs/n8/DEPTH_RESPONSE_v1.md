# Perturbing the deep cases: what changes, when, and by how much

**Owner:** *"they don't change if you retest them... alter parameters to see what changes when and
by what degree."*

Correct — correlating depth over a random sample was the wrong instrument for a deterministic
object. The deep cases are fixed; the question is what they are sensitive to. Response map below.

Baseline: subject `1` of `(1,31,75,97,128,160,176,225)`, disparities `{30,74,96,127,159,175,224}`,
**depth 23**.

---

## 1. Control: scaling invariance ✅

`×1, ×2, ×3, ×5, ×7` all give depth **23**. Readings are unchanged by global scaling, so depth must
be — and is. The measurement instrument is sound.

## 2. One-at-a-time response: piecewise constant, with cliffs

```
      d |   -6   -5   -4   -3   -2   -1    0    1    2    3    4    5    6
     30 |   17   18   18   18   18   18    ·   18    0    0    0    0    0
     74 |   16   17   17   17   17   23    ·   21   21    7    7    7    7
     96 |    5    5    5   11   11   11    ·   22   13   12   12   12   11
    127 |    3    3    3   21   21   20    ·   23   15    9    9    9    9
    159 |   11   11   11   11   15   23    ·   12   12   11   11    3    3
    175 |    1    1    1    1    1    1    ·   18   18   18   17   18    7
    224 |   13   13   13   23   23   23    ·    1    1    1    1    1    1
```

**23 is a knife-edge, not a region.** Almost every perturbation reduces depth, frequently to
single digits: `224 → 225` gives **1**; `175 → 169` gives **1**; `30 → 32` gives **0**. The response
is piecewise constant with plateaus and sudden cliffs.

This explains directly why sampling never finds these cases and adversarial search does — they are
isolated spikes.

## 3. The big cliffs are explicable — and one is a proved threshold

`d_min: 30 → 32` collapses depth from 23 to 0 because `224/32 = 7` **exactly**: every reading is
then `≤ 7`, and `DminClearance.clear_of_reading_le_seven` forces clearance. The cliff sits precisely
at Theorem 4.8's boundary.

Scanning `d_min` confirms the boundary and where the reading sits:

```
   c   depth   initial blockers
  25      18   224 (8.96)
  28      18   224 (8.00)
  30      23   224 (7.47)
  31      18   224 (7.23)
  32       0   none            <- 224/32 = 7 exactly
```

## 4. But depth is **not** determined by the initial conditions — my claim, refuted

I predicted depth would be constant between blocker-set changes. **False.** On `c ∈ [25,31]` the
blocker set is *identical* (only `224`), yet depth reads

```
   18, 18, 18, 18, 18, 23, 18
```

`c = 30` is a spike **inside** a plateau. Tracing `c = 29, 30, 31` side by side: the three
trajectories are **identical for the first 17 steps** — same setter, same scale at every one — and
diverge only at step 17/18. The minimum never sets early; it enters only when the scale has fallen
far enough. So the spike is a *late*-trajectory event.

## 5. The arithmetic hypothesis — tested and refuted

`c = 30 = 2·3·5` sits between primes 29 and 31 and shares factors with five of the six other
disparities (`gcd = [2,6,1,3,5,2]` versus `[1,1,1,1,1,1]`). A resonance hypothesis, and every
feature tested previously had been a *magnitude*, never an arithmetic one. So it was worth testing.

**It fails.** Over 21,351 subjects:

```
  max_gcd_min   correlation −0.1838      (wrong sign)
  sum_gcd_min   correlation −0.1587
  n_share_min   correlation −0.0402

  mean depth by max gcd(d_min, other):
    1→1.001   2→1.199   3→1.213   4→1.056   5→0.987   6→0.804   7→0.751   8→0.801
```

Non-monotone, peaking at `gcd = 2,3` then declining. And on the scan itself `c = 28` has
`max gcd = 28` with depth 18, while `c = 25` has `max gcd = 25` with depth 18 — the gcd structure
does not track the spike at all. **Recorded as a refuted hypothesis, not deleted.**

---

## 6. What the response map establishes

| | |
|---|---|
| depth is scale-invariant | ✅ control passes |
| depth is piecewise constant in each coordinate | ✅ observed, with plateaus |
| the largest cliffs sit at proved band boundaries | ✅ `S ≤ 7` at `c = 32` |
| depth is determined by the initial blocker set | ❌ **refuted** — spike inside a plateau |
| depth tracks shared arithmetic factors | ❌ **refuted** — wrong sign, non-monotone |

So: **depth changes at band crossings by large amounts, and additionally spikes from late-trajectory
arithmetic that no tested input feature — magnitude or gcd-based — predicts.**

That is direct evidence for `ORBIT_PREDICTABILITY_v1` §4 rather than another correlation: the
project's own `existence_of_capped` / `capped_of_existence` make a uniform depth bound equivalent to
Existence, and §4 here shows the obstruction concretely — two disparity sets agreeing on every
summary statistic *and on their first 17 cascade steps* still differ in depth by 5.

## 7. Scope

Figures in §2–§4 are exact and reproducible (one fixed disparity set, integer perturbations); §5's
correlations are from one sampler (speeds `1..89`, 21,351 subjects). No proof at order 8.

```bash
python3 experiments/n8/depth_response_v1.py   # scaling control + the response table
python3 experiments/n8/depth_response_v2.py   # the d_min scan and the S<=7 cliff
python3 experiments/n8/depth_response_v3.py   # traces of c = 29,30,31; divergence at step 17
python3 experiments/n8/depth_arith_v1.py      # the refuted arithmetic hypothesis
```
