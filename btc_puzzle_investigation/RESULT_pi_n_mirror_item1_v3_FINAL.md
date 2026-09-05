# RESULT — ITEM 1 FINAL: the `(π_n)` mirror is a different object; the record is VINDICATED on all three of my challenges

**Date:** 2026-08-01. **Supersedes v1 and v2 of this result.** Scripts: `pi_n_mirror_v3.py` + the
reconciliation runs. **Grade: `[VERIFIED — exact, independent reimplementation]`.**

## 0. Summary

Item 1 asked whether the pinned pair on `(π_n)` matches `(π_p)`. **Answer: it does not — the
falsifier fires.** Along the way I raised three objections to the record. **All three were my own
errors.** Each is recorded below, because the error pattern matters more than the individual slips.

## 1. ITEM 1 ANSWER

Under the record's own basis convention and the trace-pinned Frobenius `π = ((t+k)/2, k)`,
`t²−4M = −3k²`:

| ideal | trace | pinned pair | bridge predicts | match |
|---|---|---|---|---|
| `(π_p)` | `t_p = p+1−n` | **`[0,3]`** | `[0,3]` | ✓ |
| `(π_n)` | `t_n = n+1−p = 2−t_p` | **`[1,4]`** | `[1,4]` | ✓ |

> ### The pinned pairs DIFFER — the falsifier fires.
> §2.4's own criterion: **"the two ideals are not interchangeable and the mirror is a different
> object."** And the bridge rule *correctly predicts the difference* on both sides.

**Consequence:** the norm band, Cap Law, `σ`, frame operator and `C_T` on `(π_n)` are **distinct
unrun objects**, not restatements of the `(π_p)` programme. §2.4's remaining items are worth more,
not less.

**Structural note:** `eis_n(d) = d mod π_n` **is** the GLV decomposition `d ↦ (k₁,k₂)`. The `n`-side
lift and the GLV lift are the same map.

## 2. Independent confirmation of the record

- **The record's published sector values reproduce exactly** from its own basis:
  `c₀ = c₃ = 1/8`, `c₁ = c₄ = 0.129658895`, `c₂ = c₅ = 0.245341105`.
- **The bridge rule reproduces at 69/69, 0 violations**, from an independent reimplementation.
  That is a genuine independent confirmation of a `[VERIFIED]` claim, which the record did not have.

## 3. My three errors, in order

**(a) "The pinned pair is not a property of the ideal; impose `arg(π)∈[0,60°)`." — WRONG.**
`π` is the **Frobenius endomorphism**, pinned by `π+π̄ = 2Re(π) = t`. The six associates carry six
different traces; multiplying by a unit changes `t` and no longer represents the curve. My
normalization erased the Frobenius angle, produced a constant, and I blamed the record for the
constant I had manufactured. *(User-identified.)*

**(b) "The record's hardcoded `aP,bP` is an undocumented convention." — WRONG.**
`2·aP − bP = 432420386565659656852420866390673177327 = t_p` exactly. It is the trace-pinned
Frobenius: the mathematically forced choice.

**(c) "`gauss()` reduces with the Euclidean coefficient dot product, so the parallelogram may be
skewed and the published probabilities may be artifacts." — DOES NOT MATERIALIZE, provably.**
`p` is the **minimal** Eisenstein norm in `(π)`, and the only vectors of norm `p` in the ideal are
the **six associates**. Any lattice reduction — Euclidean or Eisenstein — can therefore only
terminate on associates. Every reduced basis is a rhombus with both sides of norm `p`, and all such
rhombi are **congruent** (half-diagonals `|π|/2` and `√3|π|/2`), differing only by rotation.
Measured: the two bases give sector-fraction multisets that are **identical**, related by a cyclic
shift. **The `1/8` pinned value, the Cap Law densities and the sector enhancements are NOT artifacts
of a skewed box.** The wrong metric cannot skew this particular basis, and that is a theorem about
the ideal, not luck.

**(d) A fourth slip, mine: "the bridge scores 35/69."** §2.4 states the rule with **`θ mod 60°`**;
I implemented raw `θ < 30°`. Every violation was explained by the missing reduction. With
`θ mod 60° < 30°` — exactly: `t>0 ∧ (t²>3M ∨ t²≤M)`, or `t<0 ∧ M≤t²<3M` — the rule scores **69/69**.

## 4. Calibration — a NEW error mode

The standing calibration says my error direction is one-way deflationary (deflations, not
overstatements). **This item adds a distinct mode: manufacturing defects against the record.**
Three false alarms in one item, each internally plausible, each dissolved by one computation I could
have run before speaking. Two were caught by the user, one by finally measuring instead of flagging.

The generating pattern: after being corrected once, I hedged the *next* finding ("flagged as
unreconciled, not calling it a defect") instead of **testing** it. Hedging is not rigor. The
correct response to "I might be wrong again" is a computation, not a caveat.

**Standing rule from this item:** a script that normalizes `π` must **assert** `2Re(π) = t` rather
than print a claim about it — v1's output contained the string `"(matches curve trace)"` next to a
number that did not.

## 5. Still unrun in §2.4

Norm band, Cap Law, `σ`, frame operator, `C_T` on `(π_n)` — now established as genuinely distinct
objects. The `h(−n)` analogue of `|FLD| = 6h(−p)` remains a small-prime study.
