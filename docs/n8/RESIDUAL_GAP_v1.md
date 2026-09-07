# The residual gap conjecture at n=8

2026-09-07. Continues `TIGHT_INSTANCES_v1.md` §6, which named this as the only
question its decomposition leaves open. Artifacts:
`experiments/n8/{residual_infimum_v1, coarse_gap_v1, tight_sets_v2}.py`.

## 1. Statement

**Residual case `R`** `[PROVED]`: `T` = 7 distinct positive integers, `gcd(T) = 1`,
holding a multiple of 5, of 6, of 7 **and of 8**. Every `T ∉ R` is settled in one
line — `t = 1/q` for a missing level `q ≤ 7` (strictly), or `t = m/8` when no speed
is divisible by 8 (tightly). Every tight instance found lies outside `R`.

> **Conjecture (residual gap).** For every `T ∈ R`, `M(T) ≥ 2/15`.

`2/15 ≈ 0.13333` against `1/8 = 0.125`: a gap of `1/120`. If true it is **sharp** —
two sets attain it — and it gives LRC(8) with room, because the good set then has
nonempty interior on all of `R` and a measure argument becomes available there.

## 2. The extremisers  `[VERIFIED-INSTANCE — two independent exact methods]`

    T = {1, 3, 4, 5, 7, 11, 24}     M = 2/15   at  t = 7/15
    T = {1, 4, 5, 6, 7, 11, 16}     M = 2/15   at  t = 7/15

Both are in `R` (`{1,3,4,5,7,11,24}`: 5→5, 6→24, 7→7, 8→24; `{1,4,5,6,7,11,16}`:
5→5, 6→6, 7→7, 8→16). Profiles at `t = 7/15`, exact:

| | 1 | 3 | 4 | 5 | 7 | 11 | 24 |
|---|---|---|---|---|---|---|---|
| `‖v·7/15‖` | `7/15` | `2/5` | **`2/15`** | `1/3` | `4/15` | **`2/15`** | `1/5` |

Two speeds sit at the minimum in each set, and the witness has denominator **15** —
outside the ladder `{2,…,8}` entirely. So the residual extremum is not a ladder
phenomenon, and the conjecture is not a restatement of §1.

## 3. Evidence  `[EMPIRICAL — scope stated; this is a SEARCH for small M, not a null]`

Four probes, none finding anything below `2/15`:

| probe | scope | smallest `M` found |
|---|---|---|
| exhaustive, ladder-filtered | speeds ≤ 32 (run incomplete when written) | `2/15` |
| targeted: one substitution carrying each tight instance into `R` | replacements ≤ 200 | `2/15` |
| uniform random residual draws | 1500 each at `V = 40, 80, 160` | `1/6`, `14/73`, `3/13` |
| single-replacement hill-climb, 12 restarts | `V = 60` | `1/7` |

The targeted probe is the informative one: it starts from the three sets where `M` is
known to be minimal and asks what entering `R` costs. The answer is at least
`2/15 - 1/8 = 1/120`, and the cheapest entry is `{1,4,5,6,7,11,13} → {1,4,5,6,7,11,16}`
(one speed, `13 → 16`).

The random and hill-climb probes give *larger* minima, and the random minimum **rises**
with the speed bound (`0.167 → 0.192 → 0.231`). Read plainly: small `M` needs small
speeds, so the exhaustive small-speed sweep is the binding evidence and the sampling
probes add little. **This is a one-sided search: it can only over-report the infimum.**
A residual set with `M < 2/15` at speeds above 32 would not have been seen.

## 4. What this is not

Not a proof, and not a closure of anything. Specifically not claimed:

- that `inf{M(T) : T ∈ R}` **is** `2/15` — only that nothing smaller was found in the
  ranges above;
- that no tight instance lies in `R` — that is the `≤ 24` (soon `≤ 34`) sweep result
  of `TIGHT_INSTANCES_v1.md` §3, and it is exhaustive only over that range;
- that a gap of `1/120` is *usable*. The v33 architecture needs a quantitative lower
  bound on the good fraction, not merely a positive one. Removing the `GF = 0`
  counterexamples is necessary, not sufficient.

## 5. Next

1. Finish the exhaustive sweep past 32 and record where it stops.
2. Prove or refute: **no tight instance contains a multiple of 8.** This is the weak
   form of the conjecture and is the one with a plausible proof — a tight instance's
   witness set must contain points isolated from both sides, i.e. speeds with
   `frac(v t*) = 1/8` and with `frac(v t*) = 7/8` simultaneously, and a coarse speed
   constrains `t*` away from the dyadic grid where the known tight witnesses sit.
3. Only then ask whether `2/15` is the true infimum.
