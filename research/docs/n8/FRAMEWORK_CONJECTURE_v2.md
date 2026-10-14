# What we are proving

2026-09-14, v2. Supersedes v1, which stated the target as a pair `(D, a)` and measured it
against another formulation. Owner's statement, in the owner's words.

---

## 1. The setting

> Imagine `k+1` runners starting at the same time and place on a circular track with a length
> (circumference) of 1 unit. Each runner moves at a constant speed, and all speeds are
> completely different from one another. A runner is considered **lonely** at any given moment
> if their distance along the track from every other runner is at least `1/(k+1)`.

Write `n = k+1`. Distance along the track is the shorter way round. "At least" is `≥`: a
runner exactly `1/n` away is lonely.

## 2. What we prove

> **Every runner becomes lonely at some point in time, and we provide a time for at least one
> instance of loneliness.**

The second half carries the first: a time provided is a time at which the runner is lonely, so
the runner becomes lonely. **So there is one claim, and it is constructive.**

> **The claim.** For every runner, produce a time at which it is lonely.

## 3. What "produce" requires

A time is **produced** when it is computed from the speeds. Not assumed, not shown to exist,
not found by trying candidates until one works.

This is what rules the wrong shapes out, and it rules them out by the form of the claim rather
than by a list of bans:

- an argument that the obstructions are collectively too small produces nothing;
- an argument that they fail to cover the track produces nothing;
- an argument that some instant must survive produces nothing.

Each concludes that a time exists. **The claim asks for the time.**

## 4. The objects

For a subject runner, the other `n−1` have speed differences `e₁ … e_{n−1}`. A candidate time
is `t = a/(nD)` for positive integers `a` and `D`.

> **The test.** The runner at difference `e` is at distance at least `1/n` from the subject at
> `t = a/(nD)` exactly when, with `R = (a·e) mod nD`,
>
>     D ≤ R ≤ (n−1)·D
>
> — integer comparison, no division, no floor, no fractional part.

`[PROVED — this is Proposition 2.1; checked across n = 5,6,7,8,9,11,13 over 28,000 cases,
0 disagreements]`

So producing a time means producing `a` and `D`. **That is not two choices — it is the time
written in these coordinates**, recoverable from `t` itself.

## 5. What is produced so far

Three rules, each computing the time outright from the differences. At `n = 8`, writing `g`
for the gcd of the differences and `m` for the least:

| condition on the differences | the time produced |
|---|---|
| no difference is `≡ 0 (mod 8g)` | `t = 1/(8g)` |
| `e_max ≤ 7·m` | `t = 1/(8m)` |
| some `r ∈ {1,3,5,7}` clears every difference | `t = r/(8m)` |

Together they produce the time for **0.71–0.83** of runners, across speeds from 40 to 5,000.

Two supporting facts, both of which name rather than count:

- **`e` cannot block at gap `D`** exactly when `nD/gcd(e, nD)` is even and `≤ n`. In
  particular when `D | e` and `e/D` is odd. `[PROVED — 2,600 pairs, 0 disagreements]`
- **gap `D` is hopeless** when some difference is divisible by `nD`; the hopeless gaps are the
  divisors of `{e/n : n | e}`, and `L_0` is the first usable one. `[PROVED]`

## 6. What remains

**A rule for the runners the three miss.** At `n = 8` those are exactly the runners with at
least one difference `≡ 0 (mod 8g)`, and the gcd lattice fails for them *all at once* — every
candidate at that gap gives the same verdict, so there is nothing to try there and the gap
must change.

The largest block is one such difference. Its arithmetic is already explicit: at `D = 2` the
blocked candidates are exactly `±e⁻¹ (mod 16)` over the odd differences — **a named set**. A
rule must produce a residue outside it by formula.

---

**Nothing in this document measures the work against another formulation, and no coverage
figure in it is conditioned on when the time falls.**
