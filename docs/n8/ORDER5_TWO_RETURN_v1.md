# Order 5: the flank census, the walk transcripts, and what the two-return lemma has to say

2026-09-15. Next step after freezing `MANUSCRIPT_v9_1.md`. Scripts in `experiments/n8/` (outputs `.out`), exact integer
arithmetic: `order5_flank_census_v1.py`, `order5_walks_v1.py`, `order5_two_returns_v1.py`.

Threshold `1/5`; four differences per subject, so **every flank has exactly three other runners** — the case the flank
criterion (`MANUSCRIPT_v9_1` §6.9, Prop 6.11) was built for.

---

## 1. The flank census  `[VERIFIED — exhaustive, 2,776,410 flanks]`

Every 5-subset of `[1, 30]`, every runner, every flank. For each flank: is it shadowed; if not, how late its first clear
opening `k*` is; its ratio denominators; and its criterion sum `Σ = Σ_{non-integer ratios} (2/5 + 1/c_j)`.

| criterion flags `Σ ≥ 1` | dead flank | shadowed | late (`k* ≥ 2`) | early (`k* ≤ 1`) |
|---|---|---|---|---|
| yes | no | 98,148 | 1,436,326 | 886,730 |
| yes | yes | 32,436 | — | — |
| no | yes | 120,784 | — | — |
| no | no | **0** | 9,826 | 192,160 |

**The criterion is sound here: 0 violations in 2,776,410 flanks** — no flank with `Σ < 1` and no dead ratio is shadowed. So

> every shadowed flank is dead or flagged,

which is the criterion's contrapositive, now checked at order 5 as well as proved.

**The correspondence the author asked about is one-directional.** "Near-blocked flanks are exactly the resonant ones the
criterion flags" does not hold as an equivalence:
- 886,730 flagged flanks are clear at their first opening (`k* ≤ 1`);
- 9,826 unflagged flanks are late (`k* ≥ 2`).

Flagging is `Σ ≥ 1`, which two non-integer ratios of denominator `c ≤ 10` already reach, so it is common. What the census does
give is the **shadowed** side exactly, and its signatures are small and uniform: denominators `(1,1,1)`, `(1,2,2)`, `(5,5,5)`,
`(1,1,2)`, `(3,3,3)`, `(2,2,2)`, `(1,3,3)`, `(7,7,7)`, `(1,1,3)`, `(2,4,4)`. Late flanks, by contrast, are dominated by large
prime denominators — `(13,13,13)`, `(11,11,11)`, `(7,7,7)`, `(17,17,17)`, `(19,19,19)` — where the orbit simply takes longer to
leave the arcs. Lateness is not resonance.

---

## 2. The walks  `[VERIFIED — exhaustive, 212,520 runners]`

Every 5-subset of `[1, 24]`, every runner; the cascade recorded as a list of `(setter, lap)`.

| most settings by one runner | runners |
|---|---|
| 0 (no move) | 132,482 |
| 1 | 74,106 |
| 2 (one return) | 5,890 |
| 3 (two returns) | **42** |

- **Between consecutive settings of the same runner**: 1 intervening move in 2,448 cases, 2 in 3,870, 3 in 138.
- **The pricing holds**: in all 6,456 returns the intervening setters' lap factors multiply to more than the returner's lap
  ratio, `∏ (5q + 1)/(5q − 1) > (5Q + 4)/(5Q + 1)` (`return_growth`).
- **The intervening setters are resonant against the returner**: the commonest denominator of `d_y/d_x` is 5 (4,086 of them),
  then 10, 19, 11, 17, 13, 7, 9.
- **Lap pairs** of consecutive settings, commonest first: `(1,2)`, `(2,3)`, `(4,5)`, `(3,4)`, `(4,6)`, `(2,4)`.

**The two-return cases are a short list.** Over `[1, 30]` (186 runners) they come from six difference sets up to dilation:
`{1,7,9,20}`, `{1,9,11,20}`, `{2,8,12,21}`, `{1,8,10,22}`, `{3,10,15,26}`, `{1,13,15,28}`. In each, the returner is the
largest difference, its three laps are `(4,5,7)`, `(5,6,7)` or `(4,5,6)`, the intervening setters are at laps 2 and 3, and
their ratios to the returner are `9/20`, `5/11`, `8/21`, `15/26` — close to one half. Their `R` values are small: 1.55 to 1.80.
Transcript of one: speeds `(1, 2, 8, 10, 21)`, subject 1, differences `1, 7, 9, 20` —
`(3,4), (2,2), (3,5), (1,2), (2,3), (3,7)`, `R = 1.8`.

---

## 3. What the lemma must say, and what it may not say

**The proved pricing, at order 5.** If `x` sets at lap `Q` and returns after a single move by a runner at lap `q`, then
`3q < 2Q + 1` (`return_lemma` at `n = 5`). With two intervening moves, `∏ (5q_j + 1)/(5q_j − 1) > (5Q + 4)/(5Q + 1)`. Both are in
Lean, and the census confirms them in every return.

**A settings cap is not available.** In this integer range no runner sets more than three times, but that is a property of the
range, not of order 5: the resonant chains at near-rational speed ratios run to 300 moves with one runner setting 150 times
(`targets_long_chains_v1.out`), at `R ≈ 1.38`. Any lemma phrased as "a runner sets at most `c` times" is false at order 5.

**So the two-return lemma has to price returns, not forbid or count them**, and it has to hold in the regime where the census
above does not reach — large readings, near-rational ratios. Stated in the framework's vocabulary, without reference to any
other literature:

> **Two-return lemma (target).** Let `x` set three moves of the cascade, at laps `Q₁ < Q₂ < Q₃`. Then the setters between its
> consecutive settings have laps whose factors multiply to more than `x`'s lap ratio across that stretch; and those setters, if
> they in turn return, obey the same bound at their own laps. The lemma is the resulting bound on the growth `x` can
> accumulate between its first and last setting.

The two ends the data mark out for it:
- **integer, small readings:** returns are cheap and rare, the returner is the largest difference, intervening laps are 2 and 3,
  and `R` stays below 2;
- **resonant, large readings:** returns are the rule, laps are large, each factor is near 1, and `R` stays near 1.4.

Both are far below the order-5 target `R < 4`; the open ground is between them, which is where the `R ≈ 31/9` searches live.

**Next actions.** (1) Run the walk census in the resonant regime (near-rational ratios, readings to the hundreds), recording the
same transcript data, so the lemma is stated against both ends. (2) Check whether the pricing plus per-runner distinct laps
already bounds the growth between a runner's first and last setting, for four differences. (3) Only then formalise.

**Tools and targets.** The criterion's pigeonhole and residue count are admissible on the resonant side (author's ruling,
2026-09-15); the statements above are in the framework's own vocabulary — flanks, openings, laps, setters, readings — and do
not depend on the other literature.
