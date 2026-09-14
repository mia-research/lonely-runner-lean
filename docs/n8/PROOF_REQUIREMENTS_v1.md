# What a proof requires — in this framework's terms

2026-09-14. Written because every assessment so far has silently translated the framework's
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
| **the stationary frame** | subtract one runner's speed so it sits at `0`; study `n−1` nonzero speeds | a privileged runner; the per-runner symmetry is hidden inside a quantifier |
| **the good set** | define `G = {t : all distances ≥ 1/n}` and ask whether `G ≠ ∅` | a set where there was a construction; every set-tool then becomes natural, and none of them names a `t` |
| **covering** | ask whether the bad sets fail to cover the line | a complement — reasoning about what is *not* there |
| **measure and density** | bound how much of the line the bad sets occupy | dead here regardless: the arithmetic progression's good set is a finite set of points (§6.1) |
| **view obstruction** | lattice points missing a family of boxes | different objects entirely |
| **exhaustion** | check a bounded family, bound a minimal counterexample | settles the question and **names nothing** |

The last is worth stating plainly because it is the current state of the art at `n = 8`:
it establishes that a time exists and says nothing about where it is.

## 3. What this framework asserts

Not that a set is non-empty. In its own objects — gaps, `d_min`, readings, resolution:

> **For every runner in every arrangement, the construction returns an exact instant at
> which that runner is lonely, together with the resolution at which it returns.**

The instant is a rational `t = a/(8D)`: `D` is the resolution at which the seed is framed,
`a ≡ 1 (mod 8)` the numerator, and the lap is `⌊d_min · t⌋`. The clearing test is
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
| the gcd lattice | no difference is `≡ 0 (mod 8g)` | `D = g`, `a = 1` |
| the ratio condition (Thm 4.8) | `d_max ≤ 7·d_min` | `D = d_min`, `a = 1` |
| the four candidates | some `r ∈ {1,3,5,7}` clears every reading | `D = d_min`, `a = r` |

Their union covers `0.71–0.83` of runners across spans from 40 to 5,000. **That fraction is
a measure of proof progress, not of the framework's reach**, and it is not tied to any lap:
`56.8%` of the gcd lattice's instants lie beyond lap 1, rising to `97.8%` at span 4,000.

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

**The construction as stated in §3 returns for it.** Smallest solution `D = 5`, `a = 9`,
`t = 9/40` — verified, every distance at or above `1/8`. And the sketch's own
`t = 305/2408` is `a/(8D)` with `D = 301`, `a = 305 ≡ 1 (mod 8)`: a resolution **301 times**
the ceiling.

So the exhibited failure is a failure of the restriction `p ∈ {1,3,5,7}`, not of the
construction. **That is the same shape as the first-window restriction**: a bound that was
never part of the framework, imported into a statement of it, and then read back as a limit.

## 7. What is missing, stated here and nowhere else

The three proved rules have side conditions. Every runner they miss has **at least one
difference `≡ 0 (mod 8g)`** — that is exactly when the gcd lattice dies, and it is the only
quantity that has ever forced the resolution up. It is flat in every magnitude:

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
