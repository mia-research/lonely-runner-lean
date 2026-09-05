# RESULT v2 — frontier #17 secondaries `S1` and `S6`

*2026-07-24. **Supersedes `RESULT_row_budget_secondaries_S1_S6_v1.md`.** One claim of v1 is bounded
by a `[PROVED]` correction (§3), and the out-of-sample status of §2 is settled (§4). All numbers are
unchanged. Script: `row_budget_s1_s6_v1.py`. Deviations: `PREREG_row_budget_lowtail_v1_DEVIATIONS.md`
(D3, D4, **D7**).*

> ⚠ **ORDERING.** Both statistics were frozen in `PREREG_row_budget_lowtail_v1.md` §3.3 **before any
> data was seen**, and both are declared there "reported, **never verdict-bearing on their own**".
> **The v1 verdict remains ABSTAIN (O6). Frontier §XI.17 remains open, status line unchanged.**

**No leakage, key-recovery or ECDLP claim.**

---

## 1. `S1` — the coupling is nil (unchanged from v1)

| `p` | 163 | 211 | 349 | 433 | 577 | 991 | 2089 | 4159 | 9319 | 19231 |
|---|---|---|---|---|---|---|---|---|---|---|
| `z` | −0.33 | −1.36 | +1.34 | −0.03 | +1.54 | +0.49 | −1.30 | −0.61 | −0.84 | +0.23 |

`Θ_char ≈ Θ_null ≈ +0.085` at every prime — the budget-forced coupling appears in both arms — and
the difference is 5 negative / 5 positive, all `|z| < 1.6`. Pooled `sd(Θ) = 1/√87335 = 0.00338`,
so the MDE at 4σ is `0.0135` = **15.9% of the forced coupling**.

> **`[EMPIRICAL — bound with power]` No char−null low/high coupling above 15.9% of the forced
> coupling, at `R=64`, this statistic, the MN-μ6 null.** It does **not** bound: top-row coupling,
> conditional coupling at fixed `B_HIGH` decile, cross-frequency-within-orbit, or either stratum.

## 2. `S6` — the strata move in opposite directions (numbers unchanged)

| stratum | `p=577` | `p=991` | `p=2089` | `p=4159` | `p=9319` | `p=19231` |
|---|---|---|---|---|---|---|
| **`c=0`** (x-only) `z` | −1.08 | −5.37 | −10.42 | −20.37 | −26.80 | −24.34 |
| **`b=0`** (y-only) `z` | +5.44 | +9.58 | +20.95 | +28.03 | +27.66 | +24.96 |

Each `z` is the character against **its own stratum's** MN-μ6 null, so each sign is internally valid.
The symmetries are carried by the nulls (checked, `≤6.6×10⁻¹⁶`): `b=0` ⇒ `U ∈ ℝ`; `c=0` ⇒
`ρ(a)=ρ(−a)`.

## 3. ★ CORRECTION to v1 §2 — the two strata are NOT the same statistic, so the magnitudes are not comparable

v1 reported "`c=0` **−17.2%**, `b=0` **+7.9%**, generic +7.4%" side by side. **The percentages may not
be compared across strata**, for a reason that is `[PROVED]`, not a caveat:

`b=0` has `U(a) ∈ ℝ`, so `ρ ~ χ²₁`, not `χ²₂`. The frozen threshold `ρ < 0.01` therefore sits at

```
b=0     : q = erf(√(θ/2))  = 0.079656        <- the 7.97% quantile
generic : q = 1 − e^{−θ}   = 0.009950        <- the 1.00% quantile     ratio 8.0055×
```

**Confirmed against this run's own measured nulls:** predicted `b=0` reference at `n=19501` is
`(n−1)·q = 1553.286` vs measured MN-μ6 null **1553.2**; predicted `c=0` reference `194.028` vs
measured **194.0**. Both land.

Consequences:
- **`N_LOW` on `b=0` is a different statistic** — a count below the 7.97% quantile, not the 1%. The
  `−17.2%` and `+7.9%` are relative excesses of two different quantities.
- **The signs still stand** (each is char vs its own null), and so does the qualitative statement:
  **the y-only readout is sub-Rayleigh in the low tail and the x-only readout is super-Rayleigh.**
- Had the generic REF-RAY been applied to `b=0` it would have reported a spurious **+700%**. It was
  not — this run compared within-stratum throughout — but the trap is recorded.
- `c=0` pairs rows (`ρ(a)=ρ(−a)`) ⇒ `N_LOW` there is **even exactly** and its variance is doubled;
  every `c=0` MDE carries a `√2`.

## 4. ★ SEEN-DATA: there is no out-of-sample set for the strata (D7)

`PREREG_row_budget_lowtail_v2.md` registers `H-STRATA` with `p ∈ {163, 211, 349, 433, 991}` as a
holdout, admissible only under attestation that those primes were unread at freeze time.

> **They were read.** This run covered all ten frozen primes and v1 §2 published the `z` values for
> the full list. **The holdout does not exist, so outcome O-B4 (descriptive) governs.** The split may
> not be reported as an out-of-sample confirmation. A genuine holdout would need primes outside the
> frozen curve list, which the spec forbids.

## 5. Caveats that bound §2 — unchanged and still the binding ones

- ⚠⚠ **No planted control exists for either stratum.** v1's P-DET covers the generic stratum only.
  These are **uncalibrated characterizations, not bounds**: nothing establishes what effect size the
  strata instrument could detect. v2 registers a per-stratum P-DET with the correct per-stratum
  extremes (constant `t≡1` → `N_LOW = n−1`; Legendre `χ(d)`, or `i·χ(d)` at `n ≡ 3 mod 4`, → `0`
  exactly with `U` real — both **verified exactly here** at `n = 139, 397, 1009, 2143, 19501`).
- `m` is small for `c=0` (27 … 693 orbits); `c=0` at `p=163, 211` has `E|z| ≤ 1.0`.
- The parallel to `M3`/`N1` (`χ₂(y)` at `½` vs x-only `bx` at 0.909 — also an x/y asymmetry) is
  **an open question, not a claim.** Different statistics on different objects; §3 makes the "same
  phenomenon" reading harder, not easier, since even the two strata here are not one statistic.
