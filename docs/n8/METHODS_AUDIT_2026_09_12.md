# Methods audit — exactness and BSM conformance across the mapping series

2026-09-12. n = 8. Records which computational method produced which result, and where
exactness is and is not used.

## 1. The three implementations

| | function | arithmetic | method | used for |
|---|---|---|---|---|
| **A** | `good()` | exact `Fraction` | interval merge of bad sets | earliest notes |
| **B** | `bsm_good()` | exact `Fraction` | Boundary Set Method | transit, window, interaction work |
| **C** | `bsm_count()` | integer | Boundary Set Method | all large sweeps |

**B** builds the boundary set `t = (8k ± 1)/(8d)` and evaluates **boundary points and open
cells separately**, because a single constraint's bad set is the *open* interval between its
boundaries — an endpoint can be lonely while the cell interior is not (`d = 4`, `t = 7/32`:
`‖7/8‖ = 1/8` exactly). Each open cell is probed at three interior points; disagreement would
indicate an incomplete boundary list.

**C** places all boundaries over a common denominator `16·lcm(D)` so midpoints are integral,
making the whole computation integer arithmetic — roughly 1000× faster, which is what made
the exhaustive pair and shape sweeps feasible.

## 2. Three-way control  `[VERIFIED]`

495 primitive constraint sets, spans `[1..10]` through `[1..70]`:

| comparison | disagreements |
|---|---|
| A vs B | **0** |
| B vs C | **0** |
| A vs C | **0** |
| BSM cell anomalies | **0** |

Zero cell anomalies across every run in the series: the boundary list is complete wherever it
was checked.

## 3. The one non-exact step

`experiments/n8/span38.py` screens 12,569,075 difference sets in floating point
(`count_float`, keep `≤ 8`), then verifies every survivor with exact `Fraction` arithmetic.
Roughly 2,800 of 12.6M survive the screen, so the exact stage is cheap.

Two controls:

- `N = 20`: screened pipeline gives 77,400 sets, min count 2, minimisers
  `(1,2,3,4,5,7,8)`, `(1,2,3,4,5,7,16)`, `(1,3,4,5,6,7,8)`, `(1,3,4,5,6,7,16)`, … — identical
  to the fully-exact run.
- `N = 24`: same, 345,304 sets, min 2, same minimisers.

A float screen can only **under**-count, because single-point components vanish in floating
point. It therefore errs toward keeping candidates, not discarding them — the direction that
matters for a floor search.

Everything else in the series is exact.

## 4. What exactness did and did not protect

No result in this series has been overturned by an arithmetic error. Every retraction came
from **experimental design**, not computation:

| retraction | cause |
|---|---|
| `mmin` ceiling of 29 | search box too small |
| "AP minimises the total" | one-runner slice could not reach the minimiser |
| "displacement cost compounds" | gcd changed with the base's scale |
| "low counts only at small span" | box edge |
| "the adversary chooses halves" | true in one regime, reversed in another |
| "crashed runners land on sixteenths" | generalised from one example |
| "worst permutation reconstitutes an AP" | one multiset's accident |
| window trajectories, first run | windows printed in scaled time |
| floor-versus-span table | minima over random samples read as minima over the box |

Exact arithmetic and BSM conformance guarantee that the *numbers* are right. They provide no
protection against measuring the wrong thing, sampling a region that cannot contain the
extremum, or comparing quantities on different scales — which is where every error in this
series has come from.

## 5. Status

`[VERIFIED]` §2's three-way control, 495 sets.
`[VERIFIED]` §3's two screen controls.
`[RECORDED]` §4's nine design-level retractions.
