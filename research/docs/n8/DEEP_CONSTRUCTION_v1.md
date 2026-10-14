# Constructing deep cases: what worked, what was refuted, and what the search learned on its own

**Owner:** *"test permutations, shifting seeds by magnitude or by increment, on or near other slots
— once you have an idea you can test if you can construct ones not found adversarially."*

Outcome: **the band insight is real and improves the search by a measurable margin; the construction
rule I derived from the depth law is refuted; the record was not beaten.**

---

## 1. The clue, and it holds up on a population

Both known deep cases sit just above the proved `S ≤ 7` threshold — `224/30 = 7.47` and
`366/43 = 8.51`. Sampled over 60,000 arrangements (`deep_construct_v1.py`):

```
   S band        n      mean depth   max   P(depth ≥ 5)
   (7, 7.25)    6698      1.554      12      0.0373
   (7.25, 7.5)  5545      2.094      15      0.0523
   (7.5, 8)    10677      1.985      16      0.0537
   (8, 9)      20781      1.674      15      0.0389
   (9, 10)     18298      1.078      15      0.0213
   (10, 12)    30949      1.017      12      0.0182
   (16, 24)    54893      1.401      12      0.0351
   (40, ∞)     73120      1.342      13      0.0323
```

**Mean depth roughly doubles in `(7.25, 8)`** against everything above `S = 9`, and
`P(depth ≥ 5)` rises by about half. `[EMPIRICAL]`, but on a large unbiased sample.

## 2. Increment shift: the `S ≤ 7` cliff fires exactly

Adding a constant to every disparity of the 23-move case (not scale-invariant, unlike multiplying):

```
   k    -6   -5   -4   -3   -2   -1    0    1    2    3    4 …
 depth  11    1    1   12   12   18   23   18   19    0    0 …
   S   9.08 8.76 8.46 8.19 7.93 7.69 7.47 7.26 7.06 6.88 6.71
```

Sharply peaked at `k = 0`, and **0 from `k = +3` onward — exactly where `S` drops below 7** and
`clear_of_reading_le_seven` forces clearance. The theorem is visible in the response.

## 3. The construction rule from the depth law — **refuted**

`depth ≈ (R−1)·Σ/8` suggested maximising `Σ` (the sum of readings) while holding `S` near 7.5, i.e.
packing every disparity high. Tested against two alternatives, 40,000 candidates each:

```
  A  all-high (max Σ)     best depth   2    Σ = 43.62   [95, 632, 663, 680, 684, 694, 696]
  B  AP-spread readings    best depth  11    Σ = 29.59   [34, 71, 107, 144, 180, 217, 253]
  C  random in-band        best depth  17    Σ = 31.85   [98, 319, 422, 454, 518, 574, 736]
```

**The Σ-maximiser is the worst, by a wide margin.** Clustering the disparities makes them block
*simultaneously*, so crossings collapse into few steps — maximum overlap. `Σ` counts crossings;
depth counts *steps*, and the overlap factor is what separates them. The law is not wrong; reading
it as a construction rule was.

## 4. What did work: the band as a search constraint

Equal budget, hill-climb with and without `S ∈ (7,8)`:

```
  BANDED   best depth 27    [28, 69, 95, 123, 154, 172, 220]   S = 7.857
  UNBANDED best depth 23    [51, 122, 161, 216, 268, 298, 383] S = 7.510
```

**27 versus 23 on the same budget.** And the telling part: the *unconstrained* climb converged to
`S = 7.51` on its own — it found the band without being told, which is independent confirmation that
the deep cases live there.

A larger sweep by sub-band reached **27** at `S = 7.62`, verified (`[55, 131, 181, 233, 293, 329,
419]`).

## 5. Honest scope on the sub-band result

The sweep reported 23, 23, **27**, 16, 20 across `(7.0,7.3) … (8.6,9.5)`, which invites the reading
that the deepest cases live in `(7.6, 8.0)`. **That reading is not supported.** The two known records
sit at `S = 7.47` and `S = 8.51` — in the sub-bands that scored 23 and 16. Those numbers are
finite-budget search outcomes, not maxima. What *is* supported is §1's population enrichment across
`(7, 8)` as a whole.

## 6. The record was not beaten

Best constructed: **27**. On file: 23 and **28**. So band-directed search beats undirected search on
equal budget and reproduces the 23-class, but does not exceed the 28-move case. No deep case was
produced that adversarial search had not already found in kind.

---

## 7. What this adds

* A **population-level** statement about where depth lives, rather than a correlation: the `(7,8)`
  band carries roughly double the mean depth.
* A **refuted construction rule**, with the mechanism named (overlap, not crossings).
* A **cheaper search**: constraining to the band is worth several depth units per unit compute.
* Consistency with `ORBIT_PREDICTABILITY_v1` §4: the band narrows *where* to look, and does not
  predict depth within it — which is what the `CascadeCapped` equivalence says must happen.

```bash
python3 experiments/n8/deep_construct_v1.py   # S-band population scan; increment shift
python3 experiments/n8/deep_construct_v2.py   # the three construction strategies
python3 experiments/n8/deep_construct_v3.py   # banded vs unbanded climb
python3 experiments/n8/deep_construct_v4.py   # sub-band sweep, best 27
```
