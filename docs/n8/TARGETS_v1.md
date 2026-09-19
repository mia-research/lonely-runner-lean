# The target list, checked against the record

Five targets were proposed. **Three are stale**, one carries an unverified claim that is **false as
stated**, and two are live. Corrections first, then what is actually actionable.

## 1. "Integer readings, finite middle band `8 ≤ bᵢ ≤ 27`" — **stale**

The band was defined by the `bᵢ ≥ 28` rounding threshold. **That threshold was withdrawn**
(`0f4e2bf`, `BAND_FACET_v1.md` §1): it rested on a test that searched for the order-7 witness on a
grid too coarse to represent it and counted "not found" as "route failed", on a population that was
almost entirely the easy half of the category.

With the rounding corrected — the candidate is `(8q+1)/(8m)`, not `q/m` — the route reaches `bᵢ ≥ 8`,
and **the whole divisor-closed category is settled by an explicit rule**: 103,060 profiles,
exhaustive over `m < 400`, **0 not settled** (`42f1736`).

**There is no band `8 ≤ bᵢ ≤ 27`.** What is open for divisor-closed is different and sharper: the
category is `[VERIFIED]`, not proved, and the obstruction is that the **extremal witness supply is
exhausted at 38.83%** while the remaining cases admit only **interior** witnesses.

## 2. "Integer readings, mixed quotients" — **live, but not as described**

The description ("small-quotient non-divisibility interacting with large-quotient LRC phases") is the
withdrawn framing. The real mixed case found in the record is different: profiles whose moduli are
**mixed between `b mod 8 ∈ {0,1}` and `b mod 8 ∈ [2,7]`**, which admit **no reflection centre at all**
— `c ≡ 0` and `c ≡ −1` cannot hold simultaneously mod a common `b ≥ 2`. That is **13,122 of 19,880**
profiles (66%), where `|S| ≥ 2` holds by a surviving orbit rather than by closure.

## 3. "Rational speeds, ≤ 2 non-integer ratios" — **`[PROVED]`, correct as listed**

## 4. "Rational speeds, 3+ common-lattice ratios" — **live**

Correct, and now sharper: the rational frontier is exactly **integer speed sets with no unit speed**
(200,000 sets, 0 mismatches), and the cost over the integer case is exactly one theorem,
`unit_never_blocks`, worth **5.76%** of candidates — the share where the minimum speed is the *sole*
blocker.

## 5. "General real / irrational, equivalent to `R < 16` or the `s₇·R = 89` ceiling" — **stale, and the `89` claim is false as a bound**

**`R < 16` is not a real/irrational handle.** `R` is the least clear point `≥ 1` (Theorem 11.1), and
`Guard.block_periodic` makes band 1 a `+8` shift of band 0 for integer readings — so `R > 7` forces
**non-integer** readings. **`R < 16` and target 4 are one problem**, confirmed on every deep case on
file (`R16_IS_RATIONAL_v1.md`).

**`s₇·R ≤ 89` is false.** Tested on 6,000 random profiles: exceeded **410 times**, with `s₇·R`
reaching **3001**. It fails because `s₇` is unbounded — at `s₇ = 3001` with `R ≈ 1` the claimed
ceiling `89/S ≈ 0.03` lies below `R = 1`.

What **is** true, and is worth keeping: `s₇·R = 89` **exactly** at the two largest deep cases on file
(`R = 44856/3749` and `14062/1179`), and not at the third (`8428/97 ≈ 86.89`). Since `89 = 8·11+1`,
this says the **extremal** profile is bound by `s₇` at a lap-11 zone endpoint — a description of the
maximiser, **not** a universal ceiling. Any argument using `R ≤ 89/S` as a bound is using a false
premise.

## The corrected list

| target | status |
|---|---|
| divisor-closed, general | `[VERIFIED]` 185,729 exhaustive — **open**, obstruction named: only interior witnesses admitted |
| integer readings, mixed reflection-centre profiles | **open** — 66%, no centre exists |
| Branch B, general | **open** — resists every named rule (best union 59.49%) |
| rational readings = no unit speed = `R` band 1 | **open** — one problem, not three |
| real / irrational | **open** — untouched; `R < 16` is *not* the handle |

## What is actionable now

Not a frontier, but the highest-yield mechanical task in the record: **Tier 2**
(`THEOREM_TIERS_v1.md`) — results stated at order 8 whose proofs consume less. One was found by
inspection (`odd_clear_of_not_dvd` → `GeneralOrder.clear_of_not_dvd`, giving **Branch A at every
order**, proved on `[propext]` alone). The rest are found the same way: compare each statement's
hypotheses against what its proof actually uses.

That converts existing proved results into stronger ones at no research risk, and 25 of 56
declarations are already order-free, so the general-`n` programme inherits them unchanged.
