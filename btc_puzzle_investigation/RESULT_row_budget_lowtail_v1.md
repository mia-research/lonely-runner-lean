# RESULT — frontier #17 (the row budget): **ABSTAIN**, planted control did not fire

*2026-07-24. Executes `PREREG_row_budget_lowtail_v1.md` (frozen pre-run; frequency lists hash-checked
`9695989b…`). Scripts: `row_budget_core_v1.py`, `row_budget_run_v1.py`, `row_budget_pdet_v1.py`.
Deviations: `PREREG_row_budget_lowtail_v1_DEVIATIONS.md`.*

**No leakage, key-recovery or ECDLP claim. Frontier §XI.17 is NOT closed and its status line is
unchanged.**

---

## 1. The verdict, which is the spec's outcome **O6**

> **P-DET criterion 3 FAILED. Therefore: "planted control did not fire; the null is uninformative."
> No verdict is issued, however clean the primary's numbers look** (spec §4.1 and O6).

The primary's numbers are reported in §3 as **descriptive only**. Under the frozen spec they may not
be read as a finding, and they are not graded. This is the abstention rule operating as designed:
a pre-committed gate failed, and a failed gate is not overridden by a post-hoc statistic — however
strongly the rest of the run points one way. *(Abstaining is not a closure of the frontier.)*

## 2. What passed, and what failed

**All seven forced/readout checks passed at all 10 primes:**

| check | result |
|---|---|
| `C-EQ-int` `max_d((x_{λd} − βx_d) mod p) == 0` | **0** exactly, all 10 primes (β derived, not transcribed) |
| `C-BUDGET` `Σ_a\|U\|² = n(n−1)` | rel `≤ 1.5×10⁻¹⁵` (char, every null draw, every plant level) |
| `C-A0` `U_char(0,f) = U_null(0,f)` | rel `≤ 2.1×10⁻¹³` |
| F8 chirp `N_LOW = 0` exactly | **0**, all 10 primes |
| F8 tone `N_LOW = n−2` exactly | **0 violations**, all 10 primes |

**P-DET, at full spec (`m_p` from the frozen lists, `R = 64`):**

| criterion | result |
|---|---|
| 1 — `ε=1.00` returns `N_LOW = n−2` exactly | **PASS** |
| 2 — chirp returns `N_LOW = 0` exactly | **PASS** |
| 3 — `N̄(ε)` strictly increasing over the seven levels | **FAIL — 8 of 10 primes** |
| 4 — `z(ε=0.20)` vs MN-μ6 exceeds `+6` for `p ≥ 577` | **PASS** |

Calibration (reported, not a criterion): measured excess at `ε=0.20` is **3.47%–5.21%** against the
derived `ε²/(1−ε²) = 4.2%` — inside the spec's own factor-2 band `[2.1%, 8.4%]` at every prime. The
detector's **measured MDE is `ε = 0.05`**, the smallest level swept, at 7 of 10 primes.

**So the detector is sensitive and correctly calibrated in magnitude — and criterion 3 still failed.**

## 3. Why criterion 3 failed: the criterion is mis-specified, not the detector

The failure is at **small `ε`**, and it is the same at every prime: `N̄` *drops* from `ε=0` to
`ε≈0.05–0.10`, then rises monotonically.

| `p` | char | `ε=0.05` | `ε=0.10` | `ε=0.20` | `ε=0.30` | `ε=0.50` | `ε=0.80` | `ε=1.00` |
|---|---|---|---|---|---|---|---|---|
| 991 | 10.769 | 10.324 | 10.290 | 10.439 | 10.995 | 13.351 | 27.412 | 1007 |
| 19231 | 208.435 | 199.644 | 197.776 | 202.706 | 212.734 | 259.859 | 533.535 | 19499 |

**Cause.** The plant interpolates from the character (`ε=0`) to the pure tone (`ε=1`). But the
`ε=0` end **has an excess of its own**, so the plant does two opposing things at once: it *adds*
tone-spike low rows, and it *destroys* the character's own alignment. At small `ε` the destruction
dominates. Measured, and consistent at every prime:

> **Replacing just 5% of the character's values moves `N̄` about **60%** of the way from the character
> down to the null level** (`−50.5%, −77.8%, −60.7%, −64.5%, −66.9%, −59.5%, −62.1%, −61.0%, −55.3%,
> −60.8%` at the ten primes).

The spec's monotone model `ε²/(1−ε²)` describes the spike term only; it is valid when the `ε=0`
carrier has no excess. Here it does. **Criterion 3 is therefore not a well-posed gate for this
plant design** — but it was frozen, it failed, and it governs.

**The v2 fix, named now:** plant into the **MN-μ6 carrier** (which sits at the null level and has no
excess) rather than into the character. Then the spike term acts alone and the monotone prediction is
valid. Alternatively restrict criterion 3 to `ε ≥ 0.2`. **Either change requires a new frozen spec;
neither may be applied to this run's numbers.**

## 4. The primary — DESCRIPTIVE ONLY, not a verdict (see §1)

`N_LOW(f) = #{a ≠ 0 : |U(a,f)|² < 0.01(n−1)}`, `N̄` = mean over the frozen frequency list.

| `p` | `n` | `m_p` | char | MN-μ6 | MN-neg | MN-free | REF-RAY | excess | `z` |
|---|---|---|---|---|---|---|---|---|---|
| 163 | 139 | 2 187 | 1.464 | 1.363 | 1.364 | 1.366 | 1.373 | +7.42% | +4.43 |
| 211 | 199 | 3 675 | 2.131 | 1.959 | 1.962 | 1.963 | 1.970 | +8.74% | +6.94 |
| 349 | 313 | 10 092 | 3.300 | 3.094 | 3.094 | 3.094 | 3.104 | +6.66% | +12.15 |
| 433 | 397 | 15 552 | 4.198 | 3.929 | 3.933 | 3.933 | 3.940 | +6.85% | +16.07 |
| 577 | 613 | 26 143 | 6.491 | 6.080 | 6.080 | 6.083 | 6.090 | +6.76% | +28.18 |
| 991 | 1009 | 15 873 | 10.769 | 10.020 | 10.026 | 10.021 | 10.030 | +7.48% | +33.95 |
| 2089 | 2143 | 7 469 | 22.849 | 21.312 | 21.291 | 21.312 | 21.313 | +7.21% | +40.80 |
| 4159 | 4243 | 3 771 | 45.385 | 42.193 | 42.203 | 42.207 | 42.209 | +7.57% | +33.07 |
| 9319 | 9127 | 1 753 | 97.258 | 90.750 | 90.793 | 90.790 | 90.805 | +7.17% | +33.09 |
| 19231 | 19501 | 820 | 208.435 | 194.084 | 194.002 | 194.109 | 194.028 | +7.39% | +33.96 |

Pooled Stouffer `Z = +76.73`, sign test **10/10 positive**. `S3` (the threshold-free order-statistic
twin) **agrees in sign 10/10**. `S5` (μ₆-orbit occupancy of the low set) is quiet — `|z| ≤ 2.37`
everywhere, so the low rows are not concentrated in particular μ₆ orbits.

**The ladder** (mean over primes, as % of REF-RAY) — the reason the spec called §3 load-bearing:

```
char    − MN-μ6   = +7.3090%    group-law / arithmetic alignment beyond μ₆
MN-μ6   − MN-neg  = −0.0356%    order-3 CM/GLV (λ) layer
MN-neg  − MN-free = −0.0331%    negation ([−1]) layer
MN-free − REF-RAY = −0.1573%    unit-modulus / exact-multiset / row-budget layer
```

**All four sum to `char − REF-RAY` by construction.** The excess sits **entirely** in the first
layer; the budget layer — the object frontier #17 was formulated around — carries `−0.157%` of it.

⚠ **F5 governs the char column.** The spec pre-declared that the character-side value of an additive
shape functional is `≈ n ×` the prior run's already-measured `(b,c)`-marginal, hence **not new
information**. That the row-axis excess (~7.3%) tracks the prior frequency-axis excess (~8%) is
therefore expected, not a confirmation. **The only new content is the null column — and it is exactly
the column the failed gate forbids issuing a verdict on.**

## 5. One thing this run does establish, independent of the gate

`row_budget_core_v1.py`, a `[PROVED]`-grade structural fact, not a measurement:

> **The conservation `Σ_a |U(a,b,c)|² = n(n−1)` is Parseval for a unit-modulus sequence in `d`.**
> It holds for *any* target of modulus 1 — verified against a random unit-modulus target at
> `0.000×10⁰`. **It is not a curve property.**

§A1.7-3 records it as "the one conservation the nulls do not carry." That is accurate about the
*specific* prior nulls (MC1/MC2 permute character values at fixed `a₀`, so they have no `a`-family
and the constraint is vacuous for them rather than violated) — but the constraint **cannot
discriminate the curve from a generic unit-modulus target**, because every null in this spec's ladder
carries it for free. This should be carried into any successor formulation of #17.

## 6. Scope and what is NOT claimed

- 10 curves `E: y²=x³+7`, `p = 163…19231` (`9.2×` the prior ceiling of 2089), `N_LOW` at the prior
  run's own `r<0.10` threshold, `R=64`, this frozen frequency list, these four nulls.
- **No verdict on H-BUDGET.** It is neither falsified nor supported by this run.
- **Frontier #17 remains open**, with its status line unchanged, and now with a named instrument
  defect to fix and a `[PROVED]` structural correction to its premise.
- Nothing here concerns `p = 2²⁵⁶−2³²−977`. The scale banner (#5) governs every row above.

## 7. Next

1. **A v2 spec with the plant carrier changed to MN-μ6** — the single blocking change.
2. Re-run unchanged otherwise; the frozen frequency lists and curve list carry over.
3. `S1` (the low/high coupling Spearman) and `S6` (strata) were not run — see deviations.
