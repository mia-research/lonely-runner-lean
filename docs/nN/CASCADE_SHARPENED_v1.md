# The counterexample sharpens the `d_min` lattice cascade

2026-09-13. Owner's question. Objects: the cascade of
`experiments/n8/cascade_by_dmin_v1.py` — candidate instants `t = p/(8D)`, `p ∈ {1,3,5,7}`,
ceiling `D ≤ 7·d_min`, clearing test `D ≤ (d·p) mod 8D ≤ 7D` for every difference `d`
(this is `coord_iff` at `n = 8`). Counterexample from `CLAIM_REFUTED_v1.md`.

---

## 1. The cascade succeeds where the window fails

The failing runner — speed `1` in `(1, 1975, 5265, 6910, 8737, 9589, 11845, 15135)`,
`d_min = 1974`.

| | |
|---|---|
| clearing lattices `D` below the ceiling `7·d_min = 13818` | **419** |
| of those, instants landing inside the first window | **0** |
| first clearing lattice | `D = 8`, `p = 3`, `t = 3/64` |
| earliest clearing instant in time | `D = 1451`, `p = 7`, `t = 7/11608` |
| that instant in lap coordinates | `u = 6909/5804 ≈ 1.190` — **lap 2** |

**The counterexample separates the two searches.** The cascade is not a reformulation of
the window procedure; it is strictly larger, and here it succeeds 419 times over while the
window returns nothing. Its earliest instant sits `1.4×` past the window's end.

`D = 8` verified by hand: `t = 3/64` gives phases `34/64, 48/64, 55/64, 32/64, 28/64,
12/64, 26/64`, every one at circle distance `≥ 1/8`.

---

## 2. Why the window is missed — and where `~1200` comes from

A `p = 7` instant `t = 7/(8D)` lies in the window `[1/(8 d_min), 7/(8 d_min)]` **iff
`D ≥ d_min`**. For smaller `p` the admissible band is `D ∈ [p·d_min/7, p·d_min]`.

For this runner the clearing lattices **stop at `D_max = 1451`**, while `d_min = 1974`. The
`p = 7` route is therefore closed outright, and no `p < 7` clear falls in its band either.

**The ceiling is not what binds.** The cascade is allowed up to `D ≤ 13818`; it dies at
`1451`, at `10.5%` of its allowance. The owner's estimate of `~1200` is the right object and
the right magnitude: the clearing band that produces the earliest instants runs
`D ∈ [1241, 1451]`, all with `p = 7`, all landing in lap 2.

---

## 3. The diagnostic: `ρ_max = D_max / d_min`

**It is scale-free.** Multiplying every difference by `c` leaves the readings — hence the
window — unchanged, and leaves `ρ_max` unchanged too:

| `c` | 1 | 2 | 3 | 5 |
|---|---|---|---|---|
| `d_min` | 1974 | 3948 | 5922 | 9870 |
| `D_max` | 1451 | 2902 | 4353 | 7256 |
| `ρ_max` | `0.735` | `0.735` | `0.735` | `0.735` |
| lap-1 instants | 0 | 0 | 0 | 0 |

(Exactly invariant only up to `D`'s integrality — `7256 ≠ 5 × 1451` — but stable to three
decimals.) So `ρ_max` is a function of the **reading vector**, the same object the window
depends on, and the threshold `ρ ≥ 1` is exactly the `p = 7` admissibility condition.

**It separates the counterexample from its own arrangement, with no overlap.**

| runner | speed | `d_min` | `D_max` | `ρ_max` | lap-1 instants | window |
|---|---|---|---|---|---|---|
| **0** | **1** | **1974** | **1451** | **0.735** | **0** | **FAILS** |
| 1 | 1975 | 1974 | 13818 | 7.000 | 3,984 | returns |
| 2 | 5265 | 1645 | 11515 | 7.000 | 6,795 | returns |
| 3 | 6910 | 1645 | 11515 | 7.000 | 9,459 | returns |
| 4 | 8737 | 852 | 4976 | 5.840 | 3,316 | returns |
| 5 | 9589 | 852 | 5922 | 6.951 | 1,945 | returns |
| 6 | 11845 | 2256 | 15792 | 7.000 | 12,399 | returns |
| 7 | 15135 | 3290 | 23030 | 7.000 | 19,024 | returns |

Seven runners at `ρ_max ∈ [5.84, 7.00]` with thousands of in-window instants each; the
eighth at `0.735` with none. The gap is not marginal.

**And `0.735` is outside anything random sampling reaches.** Over **6,559** runner-instances
from random 8-sets in `[1,500]`:

| | |
|---|---|
| `ρ_max` range observed | `[1.500, 7.000]` |
| instances with `ρ_max < 1` | **0** |
| window failures | **0** |

The counterexample's `ρ_max` lies below the minimum of 6,559 random draws.

---

## 4. What this does and does not establish

**Established.** `ρ_max ≥ 1` is *necessary* for the `p = 7` route into the window — that is
arithmetic, not observation. `ρ_max` is scale-free. The counterexample is extremal on it,
below every one of 6,559 random instances and below all seven of its own arrangement-mates.

**Not established.** That `ρ_max < 1` characterises window failure. The random sample
contains **zero failures**, so it cannot test the failure side at all; the discriminating
evidence is one arrangement. And `ρ_max ≥ 1` is not *sufficient* — it licenses the `p = 7`
band without guaranteeing a clear lattice inside it.

**What it is good for.** A scale-free number computable from the reading vector that flags
the edge case, and a threshold with an arithmetic reason behind it rather than a fitted one.
To become a characterisation it needs a population of failures, which `failure_hunt_v1.py`
can now generate.

**Untouched.** LRC(8), which is a theorem. Soundness. §§1–6 and §9.
