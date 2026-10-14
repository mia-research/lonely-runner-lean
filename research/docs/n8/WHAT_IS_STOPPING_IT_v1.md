# What is stopping the proof

2026-09-17. A direct answer, with the number behind each claim. Supersedes the diagnosis in
`WHAT_STOPS_PROOF_v2.md` only for the cascade line; that file's other content is untouched.

---

## The one-line answer

> **Every bound we have charges each cascade move its worst case — the setter caught at the very edge of
> its zone, depth `δ = 0`. That charging yields `n > 2k`, which at `k = 7` differences wants `n > 14`.
> We have `n = 8`. Nothing in the tree bounds the depths, and the obvious repair — bounding `δ` away
> from zero — is false.**

## 1. The target, and why nothing lightens it

§6.7 Existence, per runner. By `lonely_iff_run_ends` (`Iteration.lean:624`, an `↔`) it is exactly LRC(8)
for that runner. No reformulation reduces the weight; the framework's contribution is a determinate
object — one path per arrangement, each step arithmetic — not an easier problem.

## 2. Exactly what is open

Two equivalent readings, both `↔` in Lean:

| reading | proved | **open** |
|---|---|---|
| cascade (`lonely_iff_run_ends`) | `card ≤ 3` (`stops_when_twice_card_lt`), `card ≤ 4` (`four_diffs_stop_ge_eight`) | **`card ∈ {5, 6, 7}`** |
| flanks (`lonely_iff_exists_flank`) | `j ≤ 3` non-integer ratios at some flank | **`j ≥ 4` at every live flank — 85% of arrangements** |

## 3. Why each attack stalls, with its number

| route | where it stops | number |
|---|---|---|
| **counting / potential** (`ManyDifferences`) | charges `2/s` per move ⇒ `n > 2k` | wants `n > 14`; have 8 |
| **move budget** (`four_diffs_stop_ge_eight`) | `nearest_clear_first_moves` needs `((n+1)/(n−1))^j ≤ n−1` | `(9/7)^7 = 5.81 ✓`, `(9/7)^8 = 7.47 ✗` — **7 moves**, against cascades of 23 and 28 |
| **return restriction** (`no_return_after_few_faster`) | `2g+2 ≤ n` is tight; hypothesis `hvmin` is what binds | reaches **7 of 2,885 returns (0.2%)**; exact-growth form excludes none of them (margins 1.17–1.33) |
| **the cap / ladder** (`R < n−1`) | is the first window in lap coordinates, and false at order 8 | `R = 10.31` at `S = 7.467` |

The first three are the same obstruction in three coordinates. The fourth was a different problem.

## 4. The quantity nothing bounds

`ORDER5_GROWTH_v2` §2: a move's contribution to `R` is `(2 − n·δ_j)/s_j`, where
`δ_j = x_j·t_j − Q_j + 1/n ∈ (0, 2/n)` is how far into its zone the setter had gone when caught.
**Charging `δ_j = 0` is what produces `n > 2k`.** Measured (`depth_distribution_v1`), 20,000 moving
arrangements, 43,324 moves, `δ` as a fraction of the zone width `2/n = 1/4`:

| min | 10th pct | median | mean | 90th pct | max |
|---|---|---|---|---|---|
| **0.0017** | 0.0417 | 0.2250 | 0.2682 | 0.5566 | 0.9963 |

So the worst-case charge overpays by `2/(2 − nδ) = 1.29×` per move at the median — real cascades are far
from the worst case, which is why the bounds come out at `M ≲ 38`, `R ≲ 47` against an actual `R = 10.31`.

**And the obvious repair is refuted by the same table.** `δ` cannot be bounded away from zero: the
minimum observed is 0.0017 of the zone, and **24.1% of all moves sit below 10% of it**. A pointwise lower
bound on `δ` does not exist. On the named climbs, 9 of 28 and 6 of 23 moves are in that near-worst-case
band.

## 5. So what a proof has to supply

> An **amortised** statement: the depths cannot *all* be near zero along one cascade — a bound on how
> many consecutive or total near-edge catches a single arrangement can produce.

Not pointwise (§4 refutes that), and not a return restriction of the kind already tried
(`NO_RETURN_TIGHTNESS_v1`: tight, 0.2% reach, no headroom). That is the gap, and it is the whole of it
for the cascade line.

The flank line is the same gap in better coordinates, and is the one I would work: only the non-integer
ratios move (`integer_ratio_clear_iff` settles the rest once), so the open statement is that a flank with
`j ≥ 4` non-integer ratios has a lonely opening — `j ≤ 6` moving parts, integer openings `k`, threshold
`1/8`, shifts `ρ/n` determined by the ratios. Empirically such a flank always has one, at median `k = 0`
and max 10 over 40 sampled open-case arrangements.

## 6. What is not stopping it

Worth saying, because a day was spent on each:

- **not the first window / the cap.** It was never required (§1.3), and its machinery is isolated in
  `Certificate.lean`, used by nothing;
- **not the relaxation in the word LP.** The word it produced is a real cascade, verified;
- **not a missing calibration.** The named cases reproduce exactly, 4 of 4;
- **not an imported object.** The gate over the Existence line comes back clean.
