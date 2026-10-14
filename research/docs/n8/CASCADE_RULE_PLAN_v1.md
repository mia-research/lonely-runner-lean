# The cascade as a rule — plan

2026-09-14. **Goal:** a rule that takes the eight speeds and, for each runner, computes the time
at which it is lonely — and a proof that the rule never fails. Nothing here touches the frozen
manuscript or the Lean trees.

---

## 1. The rule, as stated so far

Sources: the owner's statement of 2026-09-14 (revision list item 12) and `SKETCH_v7` §7c (the
three tiers). **For the owner to confirm or correct before any proof is attempted.**

For one runner:

1. **Scale.** `m = d_min`, its nearest speed difference (from its two speed-neighbours). Every
   other runner is read proportionately: reading `s = e/m` for each difference `e`. Real speeds
   are allowed; nothing is rounded.
2. **AP times at scale 1.** Candidate times `t = a/(8m)`, `a` odd, laps continuing without limit:
   `u = m·t = a/8`, the spine points `k + r/8`, `r ∈ {1,3,5,7}`, on every lap `k`.
3. **The cascade.** If no candidate at scale 1 works, move to the next AP scale: `t = a/(8Dm)`…
   written generally, `t = a/(8D)` with `a` odd and the step `D` taken from the arrangement's own
   scales, in order:

   | tier | step `D` | exists for |
   |---|---|---|
   | AP | `g`, the gcd of the differences | commensurate arrangements only |
   | grid | `m = d_min` | every arrangement |
   | enlarged | `k·m`, `k = 2, 3, …` | every arrangement |

4. **Output.** The tier, the step `D`, the numerator `a` (its spine point `a mod 8` and lap
   `⌊m·t⌋` follow), and the time `t = a/(8D)` — irrational whenever `D` is.

A candidate **clears** when every other runner is at distance at least `1/8`:
`‖e·a/(8D)‖ ≥ 1/8` for all seven differences `e` (for integers, `D ≤ (a·e mod 8D) ≤ 7D`).

Open questions about the rule itself, which the test in §2 is designed to answer:

- Is the AP tier (`D = g`) ever needed once the grid and enlarged tiers are read on all laps, or
  does `D = k·m` alone always suffice?
- How far does `k` have to go?
- Can the least working `k` and `a` be written as a formula in the speeds?

## 2. Step 1 — test the rule, pre-registered

Before running: pre-registration by `experiment-designer`, written to
`docs/n8/PREREG_CASCADE_RULE_v1.md`. Exact arithmetic throughout (rationals; exact `Q(√2)` for
irrational speeds), every runner of every arrangement, no runner pinned.

## 3. Step 2 — closed forms already in hand, to be used in the rule

- **A reading that is a whole multiple of `8` blocks every AP time at scale 1.** If `s` is an
  integer, it is in the way at `u = a/8` for every odd `a` exactly when `8 | s`; odd `s`, and
  `s ≡ 2, 4, 6 (mod 8)`, never block. (Integral readings are all-or-nothing in `a`.)
- **The free test.** Difference `e` can never block at step `D` exactly when `8D/gcd(e, 8D)` is
  even and at most `8`.
- **Dead steps.** A step `D` is hopeless when some difference is a multiple of `8D`; for integer
  speeds these are exactly the divisors of `{e/8 : 8 | e}`.

## 4. Step 3 — the proof, case by case

The rule is proved to work in a case when, for every arrangement in that case, the tier, `D` and
`a` are **named by formula** and shown to clear. Cases already proved:

| case | named time | proved |
|---|---|---|
| `d_max ≤ 7·d_min` | `u = 1/8` | Theorem 4.8, in Lean over the reals |
| no reading within 1 of a multiple of `8` | `u = 1/8` | band identity, in Lean over the reals |
| some `r ∈ {1,3,5,7}` clears every reading | `u = r/8` | spine row, in Lean over the reals |

The remaining cases are whatever the test shows they are. Each gets its own statement, proof, and
Lean declaration, in order of how many runners it reaches.

## 5. What would count as done

One theorem, in Lean, over real speeds: **for every eight distinct speeds and every runner, that
runner is lonely at the time the rule computes.** Until then, every case proved is recorded as a
case, not as the whole.
