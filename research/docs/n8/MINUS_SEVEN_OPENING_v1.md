# The `-7` opening, and what it does and does not give

Lean witness: `experiments/n8/MinusSeven_v1.lean` (5 theorems, 0 errors, all
`[propext, Classical.choice, Quot.sound]`). Scripts: `minus_seven_opening_v1.py`,
`tiny_mover_v1.py`, `factor_seven_v1.py`, `minus_seven_coverage_v1.py`,
`largest_flank_rigidity_v1.py`, `largest_flank_allq_v1.py`, `c_family_v1.py`,
`min_shadow_v1.py`, `all_flanks_v1.py`.

---

## 1. The identity

**[PROVED — `MinusSeven.minus_seven_residue`, `inWay_minus_seven`]** Let `e ∣ L*d` — for a
whole flank, `L = lcm_j (e/gcd(|d_j|,e))`, which divides `e`. Then

```
    d*(8L-7) = -7*d + 8e*(L*d/e) ,
```

so at the opening `k = L-1`, i.e. `A = 8L-7 = 8(L-1)+1`,

```
    inWay d A e   ↔   dist(7*d, 8e·ℤ) < e .
```

The opening index is gone. **[VERIFIED]** 839,537 random movers, 0 mismatches.

## 2. The factor-7 theorem

**[PROVED — `MinusSeven.inWay_iff_tiny`, `flank_clear_of_no_tiny`]** At the largest flank
(`|d| ≤ e`), a nonzero `d` is in the way at this opening **iff** `7|d| < e`. Hence:

> If a subject's differences satisfy `max_j |d_j| ≤ 7 · min_j |d_j|`, the subject is lonely,
> at the explicit time `t = (8L-7)/(8e)` with `e = max_j |d_j|`.

**[VERIFIED]** The size form on 1,190,074 movers; the loneliness conclusion checked directly
against the definition on 36,301 qualifying subjects, all lonely at the predicted time.

`0 < e` is not needed — it follows from `|d| ≤ e` with `d ≠ 0`.

## 3. Coverage — a measured frequency, not a bound

Under uniform random integer arrangements the two conditions fire at stable rates; they do
**not** decay with the range (30,000 subjects per row):

| range | ≥1 flank clear at `c = -7` | `max ≤ 7·min` |
|---|---|---|
| ±10 | 84.95% | 34.11% |
| ±10³ | 68.22% | 29.40% |
| ±10⁶ | 66.58% | 28.94% |
| ±10⁸ | 66.75% | 29.22% |

These are frequencies under that sampling distribution. They are **not** statements about all
arrangements, and the ~33% where the `-7` opening finds no clear flank are not thereby
shadowed — they need a different multiplier.

## 4. The framework is an exact reformulation, not a reduction

**[VERIFIED — 60,000 cases, 0 mismatches]** With `σ_j = d_j/(8e)`,

```
    flank e clear at multiplier c   ⟺   the subject is lonely at time t = c/(8e) .
```

The general criterion is: flank `e` is clear iff some `c ≡ 1 (mod 8)` has
`dist(c·d_j, 8e·ℤ) ≥ e` for all `j`, and `c = -7` is one choice among `e` of them.

So the opening/flank language is a **normal form for the witness** — which is what
`FlankBridge` already stated — and Existence at order 8 does not follow from rearranging it.
Any proof must supply genuine new input; bookkeeping in this vocabulary cannot.

## 5. Two retractions from this session

**[RETRACTED] "Shadowing the largest flank is rigid: 32 cores."** Computed with the mover
pool capped at `q ≤ 8`, it read: minimum shadowing size 5, the 32 minimal configurations all
`{±1/2} × {±1/8, ±3/8, ±5/8, ±7/8}`, and **zero** minimal shadowing sets at size 6 — which
would have pinned the differences of any subject whose largest flank is shadowed.

Removing the cap and searching integer difference sets directly (flanks `e = 1..24`, six
distinct movers `|d| ≤ e`) destroys it: **87,338** shadowing configurations, at **every**
flank `e ≥ 8`, with ratio denominators covering the whole range `2..24`, and **85,532 of
87,338 contain no core**. The rigidity was an artefact of the cap. The pinning route is dead.

**[REFUTED] "A small fixed family of multipliers suffices."** The smallest `|c|` clearing some
flank grows with the arrangement: worst observed 41, 57, 129, 409 over ranges ±12, ±30, ±100,
±400. No bounded family of `c` works.

What survives both: `LastClass.shadow_needs_full_denom` (shadowing forces a reduced
denominator `≥ n`) is consistent with every configuration found — the uncapped search first
admits shadowing at exactly `e = 8`.

## 6. Minimum shadowing size

**[VERIFIED — exhaustive, pool capped at `q ≤ 8`, so scope-limited]** Minimum number of movers
that can shadow a flank: **2** in general (ratios `1/2` and `7/2`), **5** at the largest flank
(`|ρ| ≤ 1`). The size-5 minimum at the largest flank is the counterexample core. Given §5,
this is a statement about the capped pool and is not claimed beyond it.

## 7. State

* Existence at order 8 is **OPEN**, unchanged by this session.
* Proved and durable: the `-7` identity, the tiny-mover law, the factor-7 theorem, and the
  `LastClass` chain (`only_zero_class`, `last_class_forces`, `lcm_minus_one_clear`,
  `shadow_needs_full_denom`).
* The obstacle, stated precisely: at the largest flank each mover forbids a set of multipliers
  of density `1/4`, and six movers give `6/4 > 1`. A union bound cannot close it, and §4 says
  the vocabulary will not close it either. What is needed is control of the **correlations**
  between the forbidden sets of distinct movers — the same gap the counting/density route hit
  earlier (adverse correlation, joint below product).
