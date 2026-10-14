# Order 5: the two-return lemma, its data at both ends, and the measure that fails

Version 2, 2026-09-16. Supersedes `ORDER5_TWO_RETURN_v1.md`, whose §2 read truncated print output as totals (the six difference
sets were the top six of one run; the "largest difference", lap and `R` ranges came from the same truncation). Corrected from
full output and re-verified here. Scripts in `experiments/n8/`: `order5_flank_census_v1.py`, `order5_walks_v1.py`,
`order5_two_returns_full_v2.py`, `order5_nested_v2.py`, `order5_resonant_walks_v1.py`, `order5_six_configs_v1.py` (outputs
`.out`). Exact arithmetic throughout.

---

## 1. The flank census — unchanged from v1  `[VERIFIED — 2,776,410 flanks]`

Every 5-subset of `[1, 30]`, every runner, every flank. **The flank criterion is sound: 0 flanks with `Σ < 1` and no dead ratio
are shadowed.** Every shadowed flank is dead or flagged.

**The correspondence is one-directional, not an equivalence:** 886,730 flagged flanks are clear at their first opening, and
9,826 unflagged flanks are late (`k* ≥ 2`). Shadowed flanks have small uniform denominator signatures — `(1,2,2)`, `(5,5,5)`,
`(3,3,3)`, `(2,2,2)`, `(2,4,4)`; late flanks are dominated by large primes — `(13,13,13)`, `(11,11,11)`, `(17,17,17)`. Lateness is
orbit length, not resonance. The cheap route to the lemma through the sieve side is closed.

## 2. Two-return runners, complete  `[VERIFIED — exhaustive; corrects v1]`

Every 5-subset of `[1, V]`, every runner; a "two-return" runner is one whose cascade has some runner setting three times.

| | `V = 24` | `V = 30` |
|---|---|---|
| two-return runners | 42 | 186 |
| difference sets | **4**: `{1,7,9,20}` ×14, `{1,9,11,20}` ×14, `{2,8,12,21}` ×8, `{1,8,10,22}` ×6 | **7**: those four (58, 42, 36, 30) plus `{3,10,15,26}` ×10, `{1,13,15,28}` ×6, `{3,11,16,28}` ×4 |
| returner is the largest difference | 42 of 42 | **180 of 186** — the exceptions are `{1,13,15,28}`, returner 15 against `d_max = 28` |
| returner lap triples | `(4,5,7)` ×14, `(4,5,6)` ×14, `(5,6,7)` ×6, **`(2,3,4)` ×8** | those plus `(2,3,4)` ×50, `(3,4,5)` ×6 |
| intervening laps | 1 ×8, 2 ×62, 3 ×34 | 1 ×60, 2 ×268, 3 ×136, 4 ×6, 6 ×6, 7 ×6, 8 ×6 |
| `R` | `31/20` to **2** | `31/20` to **`63/26 ≈ 2.4231`** |
| first intervening ratio to the returner | `9/20`, `8/21`, `5/11` | those plus `15/26`, **`28/15 ≈ 1.87`**, `11/28` |

So: not always the largest difference, laps reach down to `(2,3,4)` and intervening laps down to 1, and `R` reaches `63/26`.
The thesis of v1 survives every correction — two-return cases are few, structured, and far below the `R < 4` target — but its
figures were wrong and its "six sets, laps 2–3, ratios near one half, `R ≤ 1.80`" description was an artefact of truncation.

## 3. The resonant end  `[VERIFIED — 7,200 walks, exact]`

Near-rational ratios, readings in the hundreds (`order5_resonant_walks_v1.py`):
- moves: median 1, 99th percentile 5, **maximum 244**; one runner sets up to **122** times;
- `R`: median 1.0024, 99th percentile 1.0697, **maximum 1.4142**;
- pricing (`return_growth`) holds in **1,509 of 1,509** returns.

Mild `R`, wild chains — the opposite extreme from §2, and the end where a wrong lemma looks right.

## 4. The candidate measure fails  `[REFUTED — both ends]`

The recursion in the lemma ("those setters, if they return in turn, obey the same bound at their own laps") needs a well-founded
measure. The candidate was: a nested return happens at strictly lower laps than its parent.

| | nested returns | inner laps strictly below the parent lap |
|---|---|---|
| integer, every 5-subset of `[1, 24]` | 138 | **0** |
| resonant, 7,200 walks | 463 | 2 |

**It is false at both ends**, and comprehensively so in the integer range: all 138 nested returns sit at laps at or above the
parent's (example: speeds `(1, 2, 9, 11, 19)`, subject 1, parent lap 2, inner laps 4 and 5). What v1 read as "nested setters at
lower laps" was the separate, weaker fact that in 2,820 of 6,456 stretches every intervening lap is below the parent's.

**What is true and can carry the recursion.** A runner's setting laps strictly increase: after setting at lap `Q` it is clear
until its lap-`Q+1` zone (`inWay_until_opening`). Laps therefore have no upper bound of their own — the resonant chains reach
lap 543 — so finiteness has to come from a budget, not from the laps themselves. Under a first-exceedance hypothesis (take the
first step at which `R` reaches the target, so every earlier step has `R` below it), each runner's laps at earlier steps are
below `s·R/5 + 1/5`, and the measure "bound minus current lap" strictly decreases along the recursion. That is the
well-foundedness the lemma needs, and it is the same device as the order-5 certificate route.

## 5. The shift constant  `[SETTLED — from the transcripts]`

Owed from earlier: is the drift `g` or `1 + g`? From the six configurations move by move (`order5_six_configs_v1.out`), the
shift is

    g = 5N + 1 − s_x,   and every other reading moves by  g·(d_y/d_x),

with `g = 1 + δ` when the setter sits **below** its multiple of 5 at depth `δ`, `g = 1 − e` when it sits **above** at height `e`,
and `g = 1` exactly when the setter is an exact slot-sharer (`δ = 0`). Examples: `s_x = 189/20` below 10 by `11/20` gives
`g = 31/20`; `s_x = 21/2` above 10 by `1/2` gives `g = 1/2`; `s_x = 20` at scale 1 gives `g = 1`. `MANUSCRIPT_v9_1` §6.2 states
this correctly (`g = 8N + 1 − s_x ∈ (0, 2)`); the depth `δ` alone is never the shift.

## 6. The lemma, restated

> **Two-return lemma (target).** Let `x` set three moves of the cascade, at laps `Q₁ < Q₂ < Q₃`. Between consecutive settings of
> `x`, the intervening setters' lap factors multiply to more than `x`'s lap ratio across that stretch (`return_growth`, in Lean);
> and each intervening setter that itself returns obeys the same bound at its own laps. The recursion is well-founded not by lap
> decrease — refuted, §4 — but by the lap deficit below a first exceedance of the target. The lemma is the resulting bound on the
> growth `x` can accumulate between its first and last setting.

It is stated in the framework's own vocabulary — setters, laps, openings, readings, growth — with no reference to any other
literature, which is the test the author set for a target.

**Next.** (1) Derive the growth bound from the pricing plus the first-exceedance measure, for four differences. (2) Test it against
both ends before fixing constants: `R ≤ 63/26` and laps down to `(2,3,4)` at the integer end; 244-move chains and 122 settings at
the resonant end. (3) Only then formalise.
