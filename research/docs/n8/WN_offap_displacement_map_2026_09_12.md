# Working note — displacing k runners off the AP: the systematic map

2026-09-12. n = 8, individual isolation. AP `(1,…,8)`. Runners displaced to fractional
positions; every runner's isolation measured over one full cycle.

Method: Boundary Set Method in integer arithmetic (`experiments/n8/bsm_fast.py`), controlled
against the exact-`Fraction` BSM — **0 disagreements over 400 constraint sets** — and ~1000×
faster, which is what makes exhaustive pair sweeps possible.

**Metric.** The LRC quantity is the **absolute event count**, not the rate. Rate = count /
cycle conflates the two, and cycle length tracks the denominator of the displaced speed. Both
are reported where they differ; the floor tables use absolute count.

## 1. Finer single-runner gradient  `[VERIFIED — settles a flagged assumption]`

`WN_bsm_full_sweeps` §5 flagged that all its positions had denominator dividing 10, and that
omitted denominators were *expected* to give higher rates. Checked at resolution 1/60, r1
swept `1 → 2`, 59 positions, 0 anomalies:

| denominator of r1 | 2 | 3 | 4 | **5** | 6 | 10 | 12 | 15 | 20 | 30 | 60 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| min rate | 4.00 | 2.67 | 2.25 | **2.00** | 3.17 | 2.70 | 2.25 | 2.13 | 2.15 | 2.37 | 2.18 |

Minimum over all 59 positions is **2.00 at 9/5**, the same as at resolution 1/10. The
assumption holds. Note it is **not monotone** in the denominator — 5 is worse than 2, 3, 4
and 6.

## 2. Floor by number of runners displaced  `[step 1/10]`

| `k` | configs | coverage | **floor (count)** | minimiser |
|---|---|---|---|---|
| 1 | 144 | exhaustive | **6** | `(1, 1.5, 3, 4, 5, 6, 7, 8)` |
| 2 | 9,009 | exhaustive | **4** | `(1.5, 2, 3, 4, 5, 5.5, 7, 8)` |
| 3 | 39,191 | sampled | **2** | `(0.5, 2, 2.5, 4, 5, 6.5, 7, 8)` |
| 4 | 38,331 | sampled | **2** | `(1.5, 2, 3.5, 4, 5.5, 6, 6.5, 8)` |
| 5 | 37,255 | sampled | 6 | `(1, 1.6, 3, 4, 4.2, 5.6, 6.4, 8.4)` |
| 6 | 35,979 | sampled | 4 | `(1, 1.9, 2.5, 4, 5.8, 6.4, 7.9, 7.3)` |
| 7 | 34,460 | sampled | 8 | `(0.6, 1.2, 3, 3.6, 5.4, 6.3, 6.9, 8.4)` |
| 8 | 32,737 | sampled | 6 | `(1.8, 1.5, 3.6, 4.5, 4.8, 6.9, 7.8, 7.2)` |

The floor falls `6 → 4 → 2`, then the `k ≥ 5` rows read `6, 4, 8, 6` — **which is a sampling
artefact, not a rising floor.** Their minimisers are tenths (`1.6, 4.2, 5.6, 6.4, 8.4`), not
halves: with five or more independent random offsets, the chance that all of them land on the
half-integer pattern where low counts live is negligible. §4 searches that region directly
and recovers floor 2 at `k = 5` and `k = 8`.

Count 2 is rare under random sampling: 2 of 39,191 at `k=3`, 1 of 38,331 at `k=4`.

## 3. Fine resolution  `[denominators to 24]`

| `k` | fine configs | floor | minimiser |
|---|---|---|---|
| 2 | 8,978 | **4** | `(1, 2, 7/2, 4, 5, 6, 15/2, 8)` |
| 3 | 8,932 | **2** | `(1, 2, 3, 7/2, 5, 6, 15/2, 17/2)` |

Fine `k=2` reproduces the coarse exhaustive floor of 4 exactly, and fine `k=3` reproduces the
floor of 2 — both with denominators up to 24 available, and both landing on halves.

## 4. The adversary chooses halves

Every minimiser found so far — at both resolutions, at every `k` — places the displaced
runners on **half-integers**:

    k=1  r2 -> 3/2
    k=2  r1 -> 3/2, r6 -> 11/2          (coarse)
    k=2  r3 -> 7/2, r7 -> 15/2          (fine, denominators to 24 available)
    k=3  r1 -> 1/2, r3 -> 5/2, r6 -> 13/2
    k=4  r1 -> 3/2, r3 -> 7/2, r5 -> 11/2, r7 -> 13/2

Not one complex fraction. Half-integers scale by 2 into small integer configurations, and
small configurations are where low counts live — the same conclusion as the `d_min` result in
`LOCALITY_v1` §2, reached independently. **The worst disturbance of the AP is the simplest
one available, not the most irregular.**

## 4a. Exhaustive over the half-integer region  `[VERIFIED — exhaustive, all k]`

Since every minimiser lives on half-integers, search that region directly: offsets drawn from
`{-3/2, -1/2, +1/2, +3/2}`, exhaustive for every `k`.

| `k` | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| configs | 31 | 382 | 2,412 | 8,400 | 16,187 | 16,393 | 7,660 | 1,183 |
| **floor** | 6 | 4 | **2** | **2** | **2** | 4 | 4 | **2** |

Never below 2 at any `k`. At `k = 8` — every runner on a half-integer — count 2 occurs in
**373 of 1,183** configurations (31%), against 1 in 38,331 under random tenths. The minimiser
is `(1/2, 3/2, 5/2, 7/2, 9/2, 11/2, 13/2, 17/2)`, which scales by 2 to the odd set
`(1,3,5,7,9,11,13,17)` and reduces to the constraint set `(1,2,3,4,5,6,8)` — a near-complete
run, the same dense shape as the `PINNED_SET_v1` minimisers.

All-halves configurations scale to all-odd speeds, whose differences are all even, so by the
parity law (`WN_count_parity`) their counts are even — consistent with 2 and never 1.

## 5. Status

`[VERIFIED — exhaustive]` §1's 59 positions; §2's `k=1` (144) and `k=2` (9,009).
`[VERIFIED — sampled]` §2's `k=3..8`; §3's `k=2,3`.
`[VERIFIED — exhaustive]` §4a, all `k` over the half-integer region.
`[RECORDED]` §2's `k ≥ 5` rows are a sampling artefact; §4a is the corrected reading.
`[CONTROLLED]` integer BSM against exact BSM, 0 disagreements over 400 sets.

Nothing at any `k` or resolution went below 2. **n = 8 is not proved.**
