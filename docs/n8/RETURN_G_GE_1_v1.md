# Work item B, first result: the return lemma for `g ≥ 1`

2026-09-18. Lean: `LRC/Cascade/SmallOrders.lean`, namespace `ChainBounds`, both new theorems
axiom-clean, `lake build` 2423 jobs. Artefacts: `experiments/n8/return_g_ge_1_v1/`.

## 1. What was blocking

`TerminationFour.return_lemma` concludes `Q(n−2) < 2P+1`, but requires `hret` — the returning runner
in the way **at the next setter's opening**. So it speaks only about an immediate return and is
silent once anything intervenes. That was the named obstruction.

## 2. The removal, and why it is not a new inequality

`return_growth` already bounds a return from **below**, in the only currency a return has: how far
the instant must travel. `t' > [(P + 1 − 1/n)/(P + 1/n)] · t`. Any upper bound on the travel over the
same window closes against it — whatever happened in between, and however many moves it took.

    return_needs_growth :  t = (P + 1/n)/x,  t < t',  inWay n x t',  t' ≤ C·t
                           ⟹  (P + 1 − 1/n)/(P + 1/n)  <  C            `[PROVED]`

**No hypothesis on the window.** The number of intervening moves, their setters and their laps are
all free. That is the whole gain: `return_lemma` could only speak when `t'` was the very next
opening.

## 3. Two instantiations

**Crude, with `C = ((1+1/n)/(1−1/n))^m`** (`return_needs_moves`, `[PROVED]`). Every lap is `≥ 1` and
`(Q + 1/n)/(Q − 1/n)` decreases in `Q`, so each move supplies at most `9/7` at `n = 8`:

| lap `P` | cost `(P+7/8)/(P+1/8)` | minimum intervening moves |
|---|---|---|
| 0 | 7.0000 | **8** |
| 1 | 1.6667 | **3** |
| 2 | 1.3529 | **2** |
| ≥ 3 | ≤ 1.2400 | none |

Consistent with `return_lemma`, which also forbids an immediate return from `P = 1, 2` (`6Q < 2P+1`
with `Q ≥ 1`). **Validated**: 588 returns including both named hard cases, **0 violations** — but
**never tight**, minimum slack 1 move, and it constrains only `P ≤ 2`.

**Sharp, with the real laps.** `return_needs_growth` takes any `C`, so it composes directly with the
actual window product `∏ (Q_j + 1/n)/(Q_j − 1/n)` — no further theorem needed:

    (P + 1 − 1/n)/(P + 1/n)  <  ∏_{j ∈ window} (Q_j + 1/n)/(Q_j − 1/n)

Measured as *need / supplied*, where `1.0` is exactly tight:

| | returns | violations | max | median |
|---|---|---|---|---|
| §6.7 climb, subject 393 | 21 | 0 | **0.885** | 0.739 |
| §6.9 row, subject 1 | 16 | 0 | **0.901** | 0.660 |
| random sample | 508 | 0 | **0.980** | 0.723 |

**499 of 508 returns consume more than half the growth their window supplies.**

## 4. Assessment

This is the first constraint measured in this line that is **not vacuous**. Every counting route has
been slack by a factor of 1.5 to 2.3 and independent of the data; this one runs at a median 72% and a
maximum 98% of its budget, and it tightens exactly where the cascade works hardest.

**It is not a proof and does not bound the cascade.** The gap between 0.98 and 1.0 is where a cascade
can keep running, and nothing here forbids that. What it does give is a genuine structural
restriction with a clear reading: **a returning runner must be paid for by small intervening laps**,
since large `Q` supplies little growth. That is a statement about the setter word, in the framework's
own objects, and it is the kind of thing the `n = 3` and `n = 4` proofs closed with.

**Next.** The crude form loses because it assumes every intervening lap is `1`. The sharp form is
near-tight but needs the laps. The question for the next step is whether the laps in a window can be
bounded **below** — if returns force small laps and small laps force fast growth, the two may close
against each other without a counting argument.

## 5. What this does not rest on

The `n = 4` proof also used a window invariant — the nearest runner staying in its **first** clear
window. That invariant is **false at `n = 8`** and is **not a framework requirement**: the nearest
runner re-enters a clear window every lap, and nothing in the construction says it must stay in the
first. Neither theorem above uses it.
