# Order 5: the growth identity, the wall it meets, and what the two-return lemma must supply

2026-09-16. Follows `ORDER5_TWO_RETURN_v2.md`. Scripts in `experiments/n8/` (outputs `.out`), exact arithmetic:
`order5_growth_setup_v1.py`, `order5_growth_identity_v1.py`, `order5_per_runner_budget_v1.py`, `order5_term_split_v1.py`,
`order5_why_nested_v1.py`. Threshold `1/n`, four differences at order 5; `m = d_min`, readings `s = d/m`, `R = n·m·t`.

---

## 1. Why the lap-decrease measure had to fail  `[PROVED — from the definitions; verified]`

The refuted measure (`ORDER5_TWO_RETURN_v2` §4) compared a nested return's laps with its parent's. It cannot decrease, for a
reason that needs no computation: **a runner's lap is monotone in time**, and a nested return happens *after* its parent's first
setting. The parent's lap is read at the earlier instant, the nested runner's at a later one. Verified: inner laps are at or
above the parent's in 138 of 138 (integer, `[1,24]`) and 11 of 11 (resonant) — including the 14 cases where the inner runner is
the *slower* one, which is what rules out a speed-based reading of the same data.

**Consequence for the lemma.** No quantity that increases along the cascade — laps, instants, readings, `R` — can found the
recursion. The measure must shrink as the cascade advances: the remaining budget under a first exceedance (§4).

## 2. The growth identity  `[PROVED — arithmetic; verified exactly on 127,610 walks, 0 failures]`

Write the setter of step `j` as `x_j` (reading `s_j`), its lap `Q_j`, its entry `P_j = x_j·t_j` and its **depth**
`δ_j = P_j − (Q_j − 1/n) ∈ (0, 2/n)`. Its exit is `E_j = Q_j + 1/n`, so `t_{j+1} = E_j/x_j`, and with `ρ_j = x_j/x_{j−1}`:

    P_j = ρ_j·E_{j−1},        E_j = ρ_j·E_{j−1} + (2/n − δ_j).

The products of the ratios telescope (`∏_{j>i} ρ_j = s_N/s_i`), giving the identity

> **R = R₁ + Σ_{j ≥ 2} (2 − n·δ_j)/s_j**,

where `R₁` is the value after the first move. **Each move adds exactly `(2 − n·δ_j)/s_j`**: the zone width it still had to cross,
divided by its reading. Equivalently `R` after a move is `(nQ + 1)/s` for that setter, and before it `(nQ − 1 + nδ)/s`.

Checked: the identity holds in all 125,744 integer walks (`[1,26]`) and all 1,866 resonant walks; every term is positive;
`R₁ ≤ 3/2` always (proved: the first setter has `s ∈ (nQ − 1, nQ + 1)`, so `R₁ = (nQ+1)/s < (nQ+1)/(nQ−1) ≤ 3/2`).

## 3. The cap is exactly "the nearest runner never returns"  `[PROVED]`

At order 5 the nearest runner has reading 1, so it is in the way at `t` iff `R = 5·m·t` is within 1 of a multiple of 5. The
first such value above the bound is `R = 4`. So

> `R < 4` ⟺ the nearest runner is never in the way after the bound.

That is the order-5 target restated in the framework's objects, and it matches `nearest_return_needs_product` (if the nearest is
in the way at step `N`, the setter-lap product exceeds `n − 1`).

## 4. Settings are finite under a first exceedance  `[PROVED; verified]`

Take the first step at which `R` reaches the target `C`. Every earlier step has `R < C`, and `R` after a setting of `x` at lap `Q`
is exactly `(nQ + 1)/s_x`, so `Q < (C·s_x − 1)/n` there. A runner's setting laps strictly increase, so before the exceedance
runner `x` sets at most `max(⌊(C·s_x − 1)/n⌋, 1)` times, and the measure "that bound minus the current lap" strictly decreases
along the recursion. **Verified at `C = 4`: 0 violations in 199,248 runner-instances (integer) and 3,005 (resonant).** This is
the well-foundedness the two-return lemma needs.

## 5. The wall: worst-case charging reproduces `n > 2k`  `[PROVED — arithmetic]`

Charge every setting its worst case, `term ≤ 2/s`. A runner whose position advances by `s·A/n` during the cascade crosses at most
`s·A/n + 1` of its zones, so it sets at most that often. Then

    A = Σ terms ≤ Σ_x (s_x·A/n + 1)·(2/s_x) = (2k/n)·A + 2·Σ_x 1/s_x,

which bounds `A` only when `2k/n < 1` — exactly the `n > 2k` threshold of `ManyDifferences`. At order 5 with four differences
`2k/n = 8/5`, and the accounting says nothing. This is the same wall reached from the multiplicative side
(`TARGETS_v3` §3.2), now from the additive one: **no accounting that charges each zone crossing its full width can close order
5.**

## 6. What the depths have to supply, quantified  `[VERIFIED — exact]`

| | integer `[1,26]`, 125,744 walks | resonant, 1,866 walks |
|---|---|---|
| total addition `R − R₁` | median 0, 99th percentile 1.1765, **max 1.7311** | median 0, 99th percentile 0.0453, max 0.1369 |
| from runners' first settings | max 1.5600 | max 0.1131 |
| from repeat settings | max 0.9610 | max 0.0841 |
| term at setting #1 | 73,504 terms, median 0.2321, max 0.8824 | 1,139 terms, median 0.0023, max 0.0847 |
| term at setting #2 | 10,022 terms, median 0.1250, max 0.5546 | 161, median 0.0020, max 0.0283 |
| term at setting #3 | 74 terms, median 0.0955, max 0.1667 | 13, median 0.0030, max 0.0106 |
| settings by one runner | at most 3 | at most 10 |

So the crude bound of §5 gives `A ≤ 2·Σ_x L_x/s_x ≤ 8k/5 = 6.4` where the truth never exceeds **1.73**; the missing factor of
about 3.7 is carried by the depths `δ`. The per-runner budget is not enough on its own: the worst single-runner contribution is
0.8824, and `3/2 + 4·0.8824 = 5.03 > 4`.

**The trade-off the lemma has to exploit** is visible in the table: a small-reading runner gives a large term but, by §4, sets
once or twice; a large-reading runner sets often but each term is at most `2/s`. Terms also decay with the setting index (medians
0.232, 0.125, 0.096), consistent with the proved `term ≤ 2/s ≤ 8/(nQ + 1)` at lap `Q ≥ i`, though that bound is not tight.

## 7. The lemma, in the form the derivation now needs

> **Two-return lemma (target, order 5).** For each runner `x` and each pair of consecutive settings of `x`, bound the total
> addition `Σ (2 − 5δ)/s_x` over `x`'s settings, using: the pricing between consecutive settings (`return_growth`, in Lean); the
> finite setting count of §4; and a lower bound on the depths `δ` at repeat settings. The lemma closes order 5 if the resulting
> total over the four differences stays below `4 − R₁`, for which `R₁ ≤ 3/2` leaves `5/2`.

Everything in that statement is in the framework's own vocabulary: settings, laps, depths, readings, zone widths. The one part
not yet in hand is the depth bound at repeat settings — which is where the next measurement goes: the depth `δ` at a setting as a
function of the previous stretch, at both ends.

**Status.** §§1–5 are proved (§2 and §4 also verified exactly at both ends); §6 is measurement; §7 is open.
