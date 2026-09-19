# Why clear-rate rises with flank size, and what causes the exceptions

Scripts: `experiments/n8/rank_mechanism_v1.py`, `shadow_cause_v1.py`,
`live_shadow_cause_v1.py`, `exception_mechanism_v1.py`, `rank6_dip_v1.py`.
All figures **[VERIFIED]** by the named script; the mechanism links them to **[PROVED]**
theorems in `FlankBridge_v1.lean`, `LastClass_v1.lean`, `MinusSeven_v1.lean`.

---

## 0. A premise that has to go first

**[RETRACTED]** "The largest flank is clear in 100% of 48,000 subjects; the flank at a
subject's largest difference is always clear." That reading (commit `43bdf84`) was superseded
by `2b253c5`: the arrangement `[-4, 0, 1, 3, 4, 5, 7, 8]`, subject `0`, has largest flank
`e = 8` **live and shadowed**. Re-checked here: `q_j = [2,8,8,2,8,8,1]`, `L = 8`, union
coverage exactly `1.000`.

Why sampling missed it is now known rather than guessed: shadowing the largest flank first
becomes possible at `q = 8`, and the exhaustive `q ≤ 7` search found **0 of 74,613**. The
rank-0 row is 100% *of a sample*.

## 1. The controlling quantity is `L`, not density

For flank `e` with movers `d_j`: `q_j = e/gcd(|d_j|,e)`, `L = lcm_j q_j`, and **`L ∣ e`**.
The flank is shadowed iff the movers' blocked classes cover **all `L`** openings.

**[VERIFIED]** It is not a density effect. Across ranks 0–6 the mean union coverage is flat at
`0.81` and the summed per-mover density is flat at `1.2–1.5`. What changes is `L`:

| rank (0 = largest) | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| mean `L` | 3485 | 2882 | 2296 | 1759 | 1256 | 813 | 389 |
| mean union coverage | .809 | .809 | .806 | .804 | .807 | .797 | .724 |

**[VERIFIED]** `P(shadowed ∣ L)` collapses: `49.4%` at `L=1`, `48.5%` at `2`, `36.9%` at `4`,
`12.5%` at `8`, `~1%` at `L≈20`, `0.05%` at `L≥64`, `0.00%` at `L≥512`. Median `L` is **3**
for shadowed flanks and **73** for clear ones; the largest `L` ever shadowed was 431, with the
99th percentile at 18.

**So the rank effect is the `L` effect.** `L ∣ e`, so a large flank carries a large `L`, and
six movers must cover every one of `L` openings without a gap. That is the whole balance.

## 2. Two different exceptions, which must not be pooled

**Dead flank** — some ratio `d/e` is a multiple of 8, so that runner is in the way at *every*
opening. Trivial, and already named by the framework's "live flank" condition. **[VERIFIED]**
6,464 of the shadowed flanks in one run were dead.

**Live shadowed flank** — no such ratio, yet every opening blocked. This is the real
exception, and the counterexample above is one.

Pooling them corrupts the statistics: with dead flanks included, `min(max q)` over shadowed
flanks is 1, which *looks* like a refutation of `shadow_needs_full_denom` and is not one.

## 3. What causes a live shadowed flank: the cheap mode needs `|ρ| > 1`

**[VERIFIED]** The dominant cheap mode is `L = 2`: two movers on opposite parity classes.
Of **2,737** such flanks, **all 2,737** carry at least one mover with `|ρ| > 1`.

That is exactly what **[PROVED — `FlankBridge.no_opposite_parity_halves`]** forbids at the
largest flank: `|d| ≤ e` pins a half-mover's whole part to `{0, -1} ≡ {0, 7} (mod 8)`, and
both block **even** `k`. No half-mover at the largest flank blocks odd `k`.

The consequence is visible in the minimum `L` by rank — **[VERIFIED]**:

| rank | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| live-shadowed rate | 0.78% | 1.25% | 2.12% | 4.84% | 9.24% | 9.58% | 3.92% |
| **minimum `L` observed** | **8** | 4 | 2 | 2 | 2 | 2 | 2 |

The largest flank never reaches `L = 2` or `4`. It is forced onto the expensive `q = 8` mode,
which is why it is shadowed two orders of magnitude less often — not because it is immune.

## 4. `shadow_needs_full_denom` is sharp in its own regime

**[VERIFIED]** Restricted to the theorem's hypothesis — every mover with `0 < ρ < 1`, so
`0 < p < q` — all **5,121** live shadowed flanks found have `max q ≥ 8`, and the minimum
attained is exactly **8**. The theorem is sharp, and the `q = 1` and `|ρ| > 1` cases of §3 lie
outside its hypotheses rather than against them.

## 5. The rank-6 dip is composition, not a new effect

The smallest flank shadows *less* than the second-smallest (3.92% vs 9.58%). **[VERIFIED]**,
by the value of `e` at rank 6:

| `e` | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | ≥9 |
|---|---|---|---|---|---|---|---|---|---|
| live-shadowed | **0.00%** | 23.87% | 7.23% | 16.92% | 8.60% | 13.70% | 4.32% | 10.47% | 0.64% |
| share of rank-6 | 14.9% | 8.1% | 5.0% | 3.5% | 2.7% | 2.1% | 2.1% | 1.7% | 59.8% |

`e = 1` is **never** live-shadowed, over 3,463 cases, and the reason is structural: `q_j ∣ e`
forces every `q_j = 1`, so every ratio is an integer — inert unless a multiple of 8, and a
multiple of 8 would make the flank dead instead. Rank 6 is 14.9% such flanks and 59.8% flanks
with `e ≥ 9` (rate 0.64%), so its average sits below rank 5's.

The same table shows a parity split: even `e` shadows at 23.9 / 16.9 / 13.7 / 10.5% against
odd `e` at 7.2 / 8.6 / 4.3%. The cheap `L = 2` mode needs `q = 2`, which needs `2 ∣ e`.

## 6. Summary of the balance

One quantity, `L = lcm_j(e/gcd(|d_j|,e))`, with `L ∣ e`:

* large `e` → large `L` → more openings to cover → clear (rank 0 is the extreme);
* `L = 2` is cheap but needs opposite-parity half-movers, which `|ρ| ≤ 1` forbids — so the
  largest flank cannot use it and must pay for `q = 8`;
* `e = 1` forces `L = 1` with only inert movers → always clear;
* `2 ∣ e` unlocks the cheap mode → even flanks shadow roughly twice as often as odd.

None of this closes Existence. It explains the shape of the distribution, and it says the
rank-0 row is rare rather than empty — which the explicit counterexample already established.
