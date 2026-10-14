# Deep review of the manuscript and the Lean tree: is there an assumption Existence does not need?

2026-09-17, at the owner's instruction, after the day's R-programme turned out to rest on the first
window. **Headline: no unnecessary assumption was found on the proved Existence line.** The confinement
that broke the R-programme is contained in one module and is used by nothing. What the review did find is
a structural ceiling on one family result, a much sharper instrument than the one I had been using, and
two things I said earlier today that were wrong.

Artefacts: `experiments/n8/flank_open_frontier_v1.py` / `.out`, plus the day's earlier harnesses.

---

## 1. The confinement has not leaked  `[VERIFIED — grep, whole tree]`

`LRC/Cascade/Certificate.lean` is the cap machinery: `cascadeR_zoneHi`, `nearest_setting_ge`,
`nearest_never_sets`, `lap_lt_of_cascadeR_lt`, `lap_lt_of_ratio_le`, `lap_mem_Icc`. Its own docstring
states the framing — *"below such a cap the nearest never sets"* — which `RETURN_CORRECTION_v3` refutes
as a target at order 8.

**Every one of those six names was grepped across the whole tree. Zero uses outside the module.**
`NearAP.lean` imports the module but uses none of its lemmas. So:

> The first-window confinement is isolated in `Certificate.lean`. No proved Existence result depends on
> it, and the collapse of the R-programme costs no theorem.

The lemmas are not wrong — each is conditional on a cap `C` that is supplied, not assumed. What is stale
is the module's stated purpose. Worth a docstring correction, not a retraction.

## 2. Both formulations are equivalences, not strengthenings  `[PROVED — Lean, two `↔`]`

| | statement | where |
|---|---|---|
| `lonely_iff_run_ends` | subject lonely somewhere **⟺** cascade reaches a fixed point | `Iteration.lean:624` |
| `lonely_iff_exists_flank` | subject lonely somewhere **⟺** some flank has a lonely opening | `Flanks.lean:54` |

Neither formulation is stronger than Existence, so neither smuggles a requirement. This is the check the
R-programme failed (G4), and the tree passes it in both places.

## 3. The open ground at `n = 8` is exactly `card ∈ {5, 6, 7}`

Differences are a `Finset ℝ`, so coincident differences collapse — which only helps, since every result
is stated in `ds.card`.

| result | hypothesis | reach at `n = 8` |
|---|---|---|
| `stops_when_twice_card_lt` | `2·card < n` | card ≤ 3 |
| `four_diffs_stop_ge_eight` | `card ≤ 4`, `8 ≤ n` | card ≤ 4 |
| `slowest_recursion` | `9 ≤ n`, `2^(k−1) ≤ n` | **none** — needs `n ≥ 9` |

So Existence at order 8 is open precisely for **5, 6 or 7 distinct differences**.

## 4. `four_diffs_stop_ge_eight` cannot be pushed to `card = 5`  `[structural, not effort]`

Its step 1 is `nearest_clear_first_moves`, whose hypothesis is
`((n+1)/(n−1))^j ≤ n − 1` — the nearest runner is clear for the first `j` moves. At `n = 8`:

| `j` | 5 | 6 | **7** | **8** |
|---|---|---|---|---|
| `(9/7)^j` | 3.513 | 4.517 | **5.808 ≤ 7 ✓** | **7.467 > 7 ✗** |

**Seven moves is the whole budget at `n = 8`.** The four-differences proof fits because a `card ≤ 4`
cascade stops by move 7. The named cascades run **23 and 28 moves, with the nearest setting at steps 19
and 24** — far outside. Its step 3 also breaks independently: with 5 differences a gap of ≥ 4 moves is
four consecutive moves by *three* runners, which need not alternate, so `no_four_alternation` no longer
applies.

Both failures are architectural. Extending this route to `card = 5` needs a new move-budget argument and
a no-four-consecutive-moves-by-three-runners lemma, not a sharpening.

## 5. The flank reduction is sharper than what I had been using  `[the thing that was missed]`

`position_at_flank` and `fractional_ratio_circDist`: at flank `e`'s `k`-th opening, the runner at `d`
sits at `circDist(k·f + ρ/n)` with `ρ = d/e`, `f = frac(ρ)`. Consequences, all already in Lean:

- **the flank itself sits at exactly `1/n`** — clear, by the open-zone convention (the boundary rule
  deciding a result for the fourth time);
- **an integer ratio never moves.** `integer_ratio_clear_iff`: ratio `A ∈ ℤ` is clear at *every* opening
  iff `n ∤ A`. Settled once, not per opening;
- **only the non-integer ratios move with `k`.**

So Existence at a flank has `j = #(non-integer ratios)` moving parts, `j ≤ n − 2 = 6`, over **integer**
`k`, at threshold `1/n`, with shifts `ρ/n` determined by the ratios. Proved coverage: `j = 1`
(`lonely_opening_of_one_fractional`, via `exists_clear_step`); `j = 2, 3` (Props 6.10–6.11). §6.9 states
the open case as `j ≥ 4`. And only **one** of the seven flanks needs to work.

**How wide the open case is** `[EMPIRICAL — 20,000 shuffled arrangements, integer differences ≤ 60]`:

| min over live flanks of `j` | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| share | 5.3% | 0.6% | 2.2% | 6.6% | 15.6% | 41.1% | 28.5% |

> **85.2% of arrangements have every live flank at `j ≥ 4`.** The proved coverage `j ≤ 3` reaches about
> 15%. The open case is not an edge case; it is the main case.

Against that: of 40 sampled arrangements in the open case, **40 have a lonely flank opening**, at
opening index `k` with median **0** and maximum 10. So the open case is empirically easy and
unproved — the worst combination for judging effort, and exactly why it should be measured rather than
estimated.

*Scope: uniform integer differences `≤ 60`, which biases ratios towards non-integers and so towards
large `j`. Extremal arrangements may sit differently.*

## 6. One place worth looking, flagged not claimed

At a flank with `j` moving ratios the requirement is threshold `1/8` on `j ≤ 6` parts. The conjecture for
6 runners would demand `1/7`. **The flank problem therefore sits at a weaker threshold than LRC does for
the same number of parts** — which looks like slack.

Two things are paid for it, and I have not weighed them: `k` ranges over the **integers**, not the reals,
and the shifts `ρ/n` are present. Discrete time and shifts both generally make such problems harder.
Whether the determined shifts preserve any of the threshold slack is the one question in this review I
could not settle, and it is where I would look for a missed opportunity.

## 7. Two corrections to what I said earlier today

- **`word_no_slow_return` is not an untried tool for the 99.8%.** Its primitive hypothesis is `hvmin` —
  the *returning* runner is the slowest of the intervening setters — from which `hlap` is *derived* via
  `faster_lap_ge'`. Since `hvmin ⟹ hlap`, its reach is at most the 0.2% I measured, not additional to
  it. I read the name as "a slow move intervenes" and it means the opposite.
- **My "ceiling check" is Theorem 4.8.** *"If `d_max ≤ 7·d_min` then `u = 1/8` isolates the subject"*
  (`ratio_condition`, 35,467 checked). I derived it from the phase `d_j/(8d_min)`, verified it 500/500,
  and reported it as an independent positive signal without noticing it is a named theorem of the
  manuscript. It is a reproduction, not a corroboration.

## 8. What I did not review

The `ConstructionN` tree below `Cascade`, `Reading.lean`'s `IdealReading` structure, `Irrational.lean`
beyond its statements, and §§2–5 and §7 of the manuscript. This review targeted the Existence line and
its hypotheses. `ManyDifferences` nativeness, flagged open in memory, remains open: I read its
architecture (a potential function, `n > 2k`) and its hypotheses are native, but I did not audit its
`lapFactor`/`potential` definitions against the framework's objects.
