# RESULT — frontier #17 secondaries `S1` and `S6` (v1 spec, executed late)

*2026-07-24. Executes the two secondaries of `PREREG_row_budget_lowtail_v1.md` §3.3 that the v1 run
skipped (deviations D3, D4). Script: `row_budget_s1_s6_v1.py`. Frozen lists hash-checked
(`9695989b…`, `dfa9f7a4…`). `R = 64`, all 10 frozen primes.*

> ⚠ **ORDERING, stated plainly.** Both statistics and both formulas were frozen in the v1 spec
> **before any data was seen**; they are run now only because v1 did not run them. The v1 spec
> declares both "reported, **never verdict-bearing on their own**".
> **The v1 verdict remains ABSTAIN (outcome O6 — planted control did not fire). Nothing here
> revives it, and frontier §XI.17 remains open with its status line unchanged.**

**No leakage, key-recovery or ECDLP claim.**

---

## 1. `S1` — the coupling is nil

`Θ_p` = Spearman rank correlation across frequencies between `N_LOW(f)` and
`B_HIGH(f) = (1/n)Σ_{a≠0, r>1.5} ρ(a;f)`, integer mid-ranks, against the MN-μ6 replicate
distribution. v1 singles this out as **the only statistic in the design that is not an additive
marginal** — the only one F5 does not render uninformative on the character side.

| `p` | 163 | 211 | 349 | 433 | 577 | 991 | 2089 | 4159 | 9319 | 19231 |
|---|---|---|---|---|---|---|---|---|---|---|
| `z` | −0.33 | −1.36 | +1.34 | −0.03 | +1.54 | +0.49 | −1.30 | −0.61 | −0.84 | +0.23 |

`Θ_char ≈ Θ_null ≈ +0.085` at every prime — **the forced positive coupling from the fixed budget
appears in both arms**, exactly as the spec predicted, and only the difference is read. That
difference is **5 negative / 5 positive, every `|z| < 1.6`**.

> **`[EMPIRICAL — 10 primes, `R=64`, this statistic, MN-μ6 null]` No char−null coupling between the
> low tail and the high tail at the same frequency, at this sample size.** The "low tail is slaved
> to the top" reading is not supported here; the low tail behaves as row-local. A magnitude with its
> scope — not a closure of anything.

## 2. `S6` — the two special strata move in OPPOSITE directions

`c=0` is the **x-only** readout (`U = T(a,b)`), `b=0` is the **y-only** readout. Per F7 these use
negation-commuting nulls only (MN-μ6, MN-neg); a free shuffle is an invalid null here, and the
strata are never pooled with the generic one.

| stratum | `p=577` | `p=991` | `p=2089` | `p=4159` | `p=9319` | `p=19231` |
|---|---|---|---|---|---|---|
| **`c=0`** char vs MN-μ6, `z` | −1.08 | −5.37 | −10.42 | −20.37 | −26.80 | −24.34 |
| **`b=0`** char vs MN-μ6, `z` | +5.44 | +9.58 | +20.95 | +28.03 | +27.66 | +24.96 |

At `p = 19231`: `c=0` char **160.6** vs null **194.0** (**−17.2%**); `b=0` char **1676.5** vs null
**1553.2** (**+7.9%**). The generic stratum was **+7.4%**.

> **`[EMPIRICAL — 10 primes, uncalibrated: see the caveat]` The `y`-involving readouts are
> sub-Rayleigh in the low tail; the `x`-only readout is *super*-Rayleigh. Opposite signs, both
> growing with `p`.** v1's generic-stratum-only design could not see this split.

**The symmetries are carried by the nulls — checked, not assumed** (`p=577`, char and both nulls
agree to `≤6.6×10⁻¹⁶`): for `b=0`, `U(a) ∈ ℝ` for every `a`; for `c=0`, the profile satisfies
`ρ(a)=ρ(−a)`. So neither effect is an artifact of the stratum's defining symmetry leaking into only
one arm.

⚠ **An error in v1's F7, found by that check and reported to the v2 spec.** F7 asserts the
profile symmetry `ρ(a;0,c)=ρ(−a;0,c)` for the `b=0` stratum **as well as** realness. **That clause is
false.** The two strata have *different* symmetries, not overlapping ones:
`c=0` ⇒ `s` even in `d` ⇒ `U(−a)=U(a)` ⇒ symmetric profile, **`U` not real**;
`b=0` ⇒ `s(−d)=conj(s(d))` ⇒ **`U` real**, profile **not** symmetric.
Measured: `c=0` symmetric TRUE with `max|Im U|/max|U| = 0.86`; `b=0` symmetric FALSE with
`max|Im U|/max|U| = 6.6×10⁻¹⁶`. **No v1 number depends on the false clause** — the run never used it
— but the choice of admissible null depends on getting each stratum's symmetry right, so it is
corrected here and in v2.

## 3. Caveats that bound §2, and they are not small

- ⚠⚠ **No planted control was ever specified for the strata.** v1's P-DET covers the generic
  stratum only. These `z` values are **uncalibrated characterizations, not bounds**: nothing
  establishes what effect size the strata instrument could or could not detect.
- `m` is small for `c=0` (27 … 693 orbits) and modest for `b=0` (81 … 1044).
- The parallel to `M3`/`N1` — where `χ₂(y)` saturates `½` while the `x`-only `bx` saturates 0.909,
  also an x/y asymmetry — is **an open question raised here, not a claim.** The two are different
  statistics on different objects; whether they are the same phenomenon is unexamined.

## 4. Status

Frontier **§XI.17 remains open**. The v1 arm abstains. `S1` adds a scoped null; `S6` adds an
uncalibrated opposite-sign split between the `x`-only and `y`-only strata that wants its own
planted control and, on the evidence, possibly its own pre-registration.
