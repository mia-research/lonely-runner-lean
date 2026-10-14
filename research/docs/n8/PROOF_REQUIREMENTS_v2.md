# What a proof requires — in this framework's terms

2026-09-14, **v2**. Corrections from the owner's review are marked in §8; the v1 text they
correct is quoted there rather than deleted.

Written because every assessment so far has silently translated the framework's
claim into someone else's apparatus and then measured it against that. This sets out the
question, the apparatus others have added to it, and what this framework has to do — with no
reference to how anyone else has chosen to answer it.

---

## 1. What the conjecture asks

> `n` runners, distinct constant speeds, starting together on a circle of circumference 1.
> **For each runner, is there a time at which every other runner is at distance at least
> `1/n` from it?**

That is the whole question. Two features of it matter and are routinely lost:

- **Per runner.** Not all at once. Each runner gets its own time.
- **A time.** Not a set, not a measure, not a complement.

## 2. What others have added to it

None of the following is in the question. Each is a decision about how to answer it, and
each imports a frame.

| apparatus | what it does | what it imports |
|---|---|---|
| **the stationary frame** | subtract **one** runner's speed once and for all, so it sits at `0`; study `n−1` nonzero speeds | a **globally privileged** runner; the per-runner symmetry is hidden inside a quantifier. **This is not what the framework does:** it subtracts *each* runner in turn, and reading `v_j − v_i` is what "`i` is lonely" *means* rather than a WLOG privileging `i` (`PROOF_CANDIDATE_v3` Step 3) |
| **the good set** | define `G = {t : all distances ≥ 1/n}` and ask whether `G ≠ ∅` | a set where there was a construction; every set-tool then becomes natural, and none of them names a `t` |
| **covering** | ask whether the bad sets fail to cover the line | a complement — reasoning about what is *not* there |
| **measure and density** | bound how much of the line the bad sets occupy | dead here regardless: the arithmetic progression's **reading** is four isolated points (§6.1) |
| **view obstruction** | lattice points missing a family of boxes | different objects entirely |
| **exhaustion** | check a bounded family, bound a minimal counterexample | settles the question and **names nothing** |

The last is worth stating plainly because it is the current state of the art at `n = 8`:
it establishes that a time exists and says nothing about where it is.

## 3. What this framework asserts

Not that a set is non-empty. In its own objects — gaps, `d_min`, readings, resolution:

> **For every runner in every arrangement, the construction returns an exact instant at
> which that runner is lonely, together with the resolution at which it returns.**

The instant is a rational `t = a/(8D)`: `D` is the **resolution** — the denominator scale at
which the differences are read — and `a ≡ 1 (mod 8)` is the numerator. **The pair `(D, a)` is
the whole output.** No lap index is part of it: lap and cycle counts are time statements and
belong to the prediction work, not to the construction's contract. The clearing test is
Proposition 2.1 — `D ≤ (a·e mod 8D) ≤ 7D` for every difference `e` — pure integer
comparison, no division, no floor, no fractional part.

**This is stronger than the conjecture and answers it directly.** The conjecture asks
whether a time exists; the construction hands it over.

## 4. What counts as a proof here

The construction takes seven differences and must produce `(D, a)`. So:

> **A proof is a rule that produces `(D, a)` from the differences, valid for every
> configuration** — or a finite set of rules whose side conditions are exhaustive.

That is what "the construction always returns" means, and it is the whole obligation. Note
what it is **not**: it is not a proof that a set is non-empty, and it is not a bound on a
search. A bound makes a search finite; it does not make it succeed.

## 5. Where the framework stands against that obligation

**Three rules are proved, and each names its instant outright.**

| rule | side condition | it returns |
|---|---|---|
| the gcd lattice | **integer differences**: no difference is `≡ 0 (mod 8g)`. General form: no reading within `1` of a multiple of `8` | `D = g`, `a = 1` |
| the ratio condition (Thm 4.8) | `d_max ≤ 7·d_min` | `D = d_min`, `a = 1` |
| the four candidates | some `r ∈ {1,3,5,7}` clears every reading | `D = d_min`, `a = r` |

Their union covers `0.71–0.83` of runners across spans from 40 to 5,000. **That fraction is a
measure of proof progress, not of the framework's reach.** It is not conditioned on any
window: each rule names its instant outright, and where that instant falls is not part of the
claim.

**Two further facts are proved and are about the structure of the search, not its success.**

- **Dead lattices have a closed form** (`SKETCH_v7` §7c). `D` is dead when some difference is
  divisible by `8D`; with `M = {d/8 : 8 | d}`, the dead lattices are exactly the divisors of
  elements of `M`, and `L_0` is the first live one.
- **The ceiling.** No step above `7·d_min` clears — **for `p ∈ {1,3,5,7}`.**

## 6. The ceiling does not bind the construction as stated

The ceiling's proof runs: if `D > 7·d_min` then `p·d_min ≤ 7·d_min < D` for every
`p ∈ {1,3,5,7}`, so the residue falls below the band. **It needs `p ≤ 7`.** With
`a ≡ 1 (mod 8)` free to exceed 7, `a·d_min mod 8D` is unconstrained and the argument does
not apply.

This is not academic. `SKETCH_v7` §7c exhibits a failure:

> `V = [27, 45, 308, 678, 679, 799, 806, 979]`, runner `r4 = 678`, differences
> `1, 121, 128, 301, 370, 633, 651`. `128 = 2⁷` so `M = {16}`, `Dead = {1,2,4,8,16}`,
> `L_0 = 3`; `d_min = 1` caps the range at 7; the live steps `{3,5,6,7}` all fail.

**The construction as stated in §3 returns for it.** At `D = 5`, `a = 9`, `t = 9/40` —
verified, every distance at or above `1/8`. That is the **smallest resolution** that works,
not the earliest instant: the sketch's own `t = 305/2408 ≈ 0.127` is earlier than
`9/40 = 0.225`, and it too is of the form, `D = 301`, `a = 305 ≡ 1 (mod 8)` — a resolution
**43 times the ceiling** `7·d_min = 7`.

So the exhibited failure is a failure of the restriction `p ∈ {1,3,5,7}`, not of the
construction. **That is the same shape as the first-window restriction**: a bound that was
never part of the framework, imported into a statement of it, and then read back as a limit.

## 7. What is missing, stated here and nowhere else

The three proved rules have side conditions. **For integer differences**, every runner they
miss has at least one difference `≡ 0 (mod 8g)` — that is exactly when the gcd lattice dies,
and it is the only quantity that has ever forced the resolution up.

**The characterisation is false for general readings and must be scoped.** The readings
`{5.2, 6.4, 7.6, 8.6, 9.2}` block all four spine points — `r = 1` by `7.6` and `8.6`, `r = 3`
by `5.2`, `r = 5` by `6.4`, `r = 7` by `9.2` — with **no reading an exact multiple of 8**.
Divisibility is the integer shadow of the band condition, not the condition itself.

The table below is integer data and is scoped accordingly:

| differences `≡ 0 (mod 8g)` | mean resolution | max observed |
|---|---|---|
| 0 | 1.01 | 2 |
| 1 | 3.47 | 11 |
| 2 | 4.06 | 13 |
| 3 or more | 4.4–5.0 | 10 |

> **The obligation is a fourth rule: produce `(D, a)` when `j ≥ 1` differences are divisible
> by `8g`.**

Two things already in hand point at it. `L_0` is the closed form for the first live lattice,
and the clearing step **is** `L_0` in `78.6%` of enlarged cases and within 2 of it in `91%`.
A rule of the form "take `L_0`, and when it fails take the next live lattice, and this
terminates" would discharge the obligation. `[VERIFIED — 31,066 of 31,066 runners named,
largest resolution 13]`, but it is not proved, and the 21.4% where the step is not `L_0` is
where the rule has to be found.

**Nothing here is measured against another formulation, and no coverage figure in this
document is conditioned on a lap.**


---

## 8. Corrections applied in v2

From the owner's review of v1. The v1 wording is quoted so the change is visible.

| # | v1 said | corrected to | status |
|---|---|---|---|
| 1 | "the lap is `⌊d_min·t⌋`" as part of the output; "56.8% … beyond lap 1" | `(D, a)` is the whole output; lap statistics removed | **accepted** — lap and cycle counts are prediction-work currency, not the construction's contract |
| 2 | the ban-table's stationary-frame row, undistinguished | the row now says *globally* privileged, and names the framework's per-runner reading as a different thing | **accepted** — as written v1 condemned the framework's own engine |
| 3 | "the arithmetic progression's **good set**" | "the AP's **reading**" | **accepted** — v1 used the banned apparatus's name for the framework's object |
| 4 | "Smallest solution `D = 5`, `a = 9`" | "smallest **resolution**", with the time order stated | **accepted and verified**: `305/2408 ≈ 0.127 < 9/40 = 0.225` |
| 5 | "no difference is `≡ 0 (mod 8g)`" | scoped to integer differences, band form given | **accepted in substance.** The offered counterexample `e = 17, g = 2` is not realisable — `g` is the gcd of all differences, so every difference is a multiple of `g`, and `17` is odd. For integer differences the two forms are **equivalent**: `e = kg` gives `(e mod 8g) = g·(k mod 8)`, so the band is `8 ∤ k`. Checked, **0 mismatches in 32,000 runners**. The scoping is right for the reason in row 7 |
| 6 | "56.8% beyond lap 1" said to contradict row 1 | lap material removed | **the reasoning does not hold**, but the fix is the same. Row 1 returns `t = 1/(8g)`, so `u = d_min/(8g)`, **not** `a/8`; it is `1/8` only when `d_min = g`. Verified: differences `26,60,130,159,…` give `u = 13/4`, lap 3. Item 1 removes the statistic regardless |
| 7 | "Every runner they miss has at least one difference `≡ 0 (mod 8g)`" | scoped to integer differences, with the counterexample | **accepted and verified**: `{5.2, 6.4, 7.6, 8.6, 9.2}` blocks all four spines with no exact multiple of 8 |
| minor | "301 times the ceiling" | 43 times the ceiling (`301 = 43 × 7`) | **accepted** |
| minor | "the resolution at which the seed is framed" | "the denominator scale at which the differences are read" | **accepted** — "seed" was undefined |
