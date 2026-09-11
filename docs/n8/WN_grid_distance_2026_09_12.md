# Working note — grid distance vs the worst runner

2026-09-12. Scripts `experiments/n8/ok_worst_config_v1.py` (+ the inline grid-distance run).
Exact `Fraction`, BSM good sets, eight genuine runners, nothing adjoined.

Working note. Data only.

---

## 1. Definitions used

**Isolation event count** for runner `i` = number of maximal components of its good set
`{t : ‖(v_j − v_i)t‖ ≥ 1/8 ∀j}` over one period. For integer speeds with `gcd = 1` the period
is 1, so the count equals the events-per-unit-time rate of `ISOLATION_COUNT_v1`.

**Grid distance** `k(V)` = `8 − |{(v_i − v_1)/g mod 8}|`, `g` = gcd of the pairwise
differences. `k = 0` means the reduced residues are a complete system mod 8, i.e. the
configuration achieves global isolation (`WHICH_GRIDS_ISOLATE_v1` §1). `k` counts the speeds
whose residue must change to reach a grid.

## 2. Grid distance vs the worst runner  `[VERIFIED — exhaustive]`

All primitive 8-subsets of `[1..20]`:

| `k` | configs | min event count over all runners | worst example (counts) |
|---|---|---|---|
| 0 | 1,300 | **4** | `(1,…,8)` `[4,8,8,6,6,8,8,4]` |
| 1 | 22,922 | **2** | `(1,2,3,4,5,6,7,9)` `[6,6,8,8,6,8,8,2]` |
| 2 | 60,693 | **2** | `(1,2,3,4,5,6,9,10)` `[6,4,6,8,8,8,2,6]` |
| 3 | 36,440 | **2** | `(1,2,3,4,5,9,10,12)` `[8,6,10,8,6,2,6,4]` |
| 4 | 4,514 | **2** | `(1,2,4,5,10,12,13,17)` `[12,8,8,2,4,6,12,10]` |
| 5 | 56 | **4** | `(1,2,4,9,10,12,18,20)` `[14,12,6,4,12,10,12,16]` |

Readable from the table: the floor is `4, 2, 2, 2, 2, 4` across `k = 0..5`. It does not
decrease with `k`. The minimum over all `k` is attained at `k = 1`, one permutation from a
grid, not at large `k`.

## 3. Distribution of the worst runner  `[VERIFIED — exhaustive]`

Min event count per configuration, primitive 8-subsets:

| min | 2 | 4 | 6 | 8 | 9 | 10 | 11 | 12 | 14 |
|---|---|---|---|---|---|---|---|---|---|
| `[1..20]` | 2.07% | 17.58% | 41.01% | 30.87% | 0.31% | 7.36% | 0.03% | 0.74% | 0.02% |

Lowest value observed: **2**, in both `[1..16]` and `[1..20]`. Zero never occurs — a zero
would be an LRC(8) counterexample.

Counts are almost all even. The good set is symmetric under `t → 1−t` (since
`‖e(1−t)‖ = ‖et‖`), so components come in mirror pairs unless one is centred at `t = 1/2`;
the odd entries (9, 11) are the self-mirror cases and are rare.

Configurations attaining 2: `(1,2,3,4,5,6,7,9)`, `(1,2,3,4,5,6,8,9)` — the latter with **two**
runners at 2 — `(1,2,3,4,5,6,8,16)`, `(1,2,3,4,5,6,9,10)`, `(1,2,3,4,5,6,9,11)`,
`(1,2,3,4,5,6,13,14)`. All are the AP with one or two speeds displaced.

## 4. "Worst" is metric-dependent  `[recorded]`

Two different quantities, two different answers:

- by **measure** of the isolation set: the AP is worst — `|G| = 0` for r1 and r8, witnesses at
  isolated points only, no slack (`ISOLATION_COUNT_v1` §1);
- by **event count**: the AP is *not* worst — it has 4, while near-APs at `k = 1..4` have 2.

Both were called "worst" at different points in this session. They are not the same ordering.

## 5. Pending / not measured

- A wider floor search (exhaustive `[1..22]`, near-AP adversaries, random `[1..500]`) was
  launched and had not returned when this note was written. Until it does, "2 is the floor"
  is a statement about `[1..16]` and `[1..20]` only.
- Whether any runner can have exactly **1** event (a single self-mirror component at `t = 1/2`)
  — not found in either box, not excluded.
- Whether the `k = 0` and `k = 5` floors of 4 are stable in larger boxes; `k = 5` has only 56
  configurations here.

`n = 8` is **not proved.**
