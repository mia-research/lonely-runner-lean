# RESULT v2 — frontier #17: the repaired gate WORKS; the arm **abstains again**, on a different control

*2026-07-24. Executes `PREREG_row_budget_lowtail_v2.md` (frozen pre-run). Script:
`row_budget_v2_run.py`. Frequency list hash-checked `9695989b…`. `R = 64`, all 10 frozen primes.
Predecessor: `RESULT_row_budget_lowtail_v1.md` (abstained on criterion 3).*

**No leakage, key-recovery or ECDLP claim. Frontier §XI.17 is NOT closed; status line unchanged.**

---

## 1. Verdict

> **P-DET-A criterion 5 (P-SIZE) FAILED ⇒ no Arm A verdict** (spec §4.1).
> **Arm A3 (pre-registered, UNSEEN) also FAILED** its pre-committed slope band.

**The repair worked.** Criterion 3 — the one v1 failed — **PASSES at every prime**, and so do
criteria 1, 2, 4, plus both new gates `C-SELFZ` and `C-DISP`. The abstention is now driven by a
*different* control, and that control is **demonstrably mis-calibrated** (§3).

## 2. What passed

| check | result |
|---|---|
| `C-EQ-int` | **0** exactly, all 10 primes |
| `C-BUDGET` | rel `≤ 1.2×10⁻¹⁵` |
| **Criterion 1** `ε=1 ⇒ N_LOW = n−1` exactly | **PASS**, 0 violations (the F14 change from v1's `n−2`) |
| **Criterion 2** chirp `⇒ N_LOW = 0` exactly | **PASS**, 0 violations |
| **Criterion 3** `Δ_meas ≈ Δ_pred` on the admissible sub-grid | **PASS at every prime** |
| **Criterion 4** `z(ε=0.20) > +6`, `p ≥ 577` | **PASS** |
| `C-SELFZ` | **PASS** — `|z_split| ≤ 0.49`, leave-one-out sd `1.031…1.038` ⊂ `[0.7,1.4]` |
| `C-DISP` | **PASS** — `D_char/D_null = 0.979…1.048`, nowhere near the 1.5 inflation trigger |

**The derived response model is confirmed.** With the constant plant (`a*=0`, so the spike lands on
the F4-excluded row) `Δ_meas` tracks the exact, `n`-free `Δ_pred(ε) = (1−e^{−θ/(1−ε²)})/(1−e^{−θ})−1`:

| `p` | `ε=0.20` | `ε=0.30` | `ε=0.50` | `ε=0.80` |
|---|---|---|---|---|
| **predicted** | +4.145% | +9.836% | +33.11% | +175.33% |
| measured, `p=211` | +6.207% | +9.910% | +35.797% | +173.974% |
| measured, `p=163` (sub-grid starts at 0.30) | — | +4.654% | +29.832% | +164.383% |

Both v2 diagnoses of v1's failure are thereby vindicated: the F12 spike-row cancellation and the
F13 smearing kernel were the causes, and removing them makes the response monotone and predictable.

## 3. What failed — and criterion 5 is incoherent as written `[PROVED]`

Criterion 5: *"`|z| ≤ 3` at every prime, and over 64 independent carriers the fraction with `|z| > 2`
must be `≤ 0.10`."* The **second clause passes everywhere** (`0.031…0.094`). The **max-clause fails**
at `p=211` (`4.04`) and `p=433` (`3.87`).

**The null is calibrated.** Pooling all `10 × 64 = 640` unplanted-carrier `z` values:

```
mean  +0.038      sd  1.019      skew  −0.176
|z|>3 : observed  2   expected under N(0,1)  1.7
|z|>2 : observed 4.9%  expected               4.6%
```

**The criterion is not.** For 64 draws of a calibrated `N(0,1)`,

```
P(max|z| > 3 over 64 draws)              = 0.159   per prime
P(at least one of 10 primes exceeds 3)   = 0.823
```

> **A "max over 64 draws ≤ 3σ" gate is expected to fail somewhere ~82% of the time by chance.**
> Observed: 2 of 10 primes, against an expectation of 1.6. The gate is doing what it was always
> going to do, and it is measuring nothing about this instrument.

**No post-hoc repair was applied.** Criterion 5 was frozen, it failed, and it governs. The v3 fix
must replace the max-clause with something order-statistic-aware — a pooled Kolmogorov–Smirnov or
Anderson–Darling test of the 640 `z` against `N(0,1)`, or a per-prime bound at the correct quantile
(`≈3.5` for 5% per prime; `≈3.94` Bonferroni over 640). **That requires a new frozen spec.**

### Arm A3 (UNSEEN, pre-registered) — FAILS, and the test was underpowered over 40% of its range

F11 predicts relative layer `= −0.4950/(n−1)`; A3 fits `log|layer|` on `log(n−1)`, pre-committed
slope `−1`, band `[−1.35, −0.65]`.

> **Measured slope = `−0.500` ⇒ FAIL.** Signs: 7/10 negative (F11 predicts all 10 negative).

**Diagnosis.** The predicted quantity falls below this run's own noise floor at the top of the range:

| `p` | 163 | 433 | 991 | 2089 | 4159 | 9319 | 19231 |
|---|---|---|---|---|---|---|---|
| predicted % | −0.359 | −0.125 | −0.049 | −0.023 | −0.012 | −0.005 | −0.003 |
| measured % | −0.330 | −0.280 | −0.062 | **+0.037** | −0.042 | **+0.018** | **+0.043** |
| signal / noise | 1.50 | 2.42 | 1.51 | **0.72** | **0.36** | **0.16** | **0.08** |

All three sign violations sit where `S/N < 0.8`. **F11 is not falsified by this** — the regression
spans a region where the target is up to `12×` below the measurement floor, which the spec did not
account for. *(A post-hoc restriction to `p ≤ 991`, where `S/N > 1.5`, gives slope `−0.872`, inside
the band. That is **EXPLORATORY** and does not rescue a pre-registered failure.)*

## 4. Arm A primary — DESCRIPTIVE ONLY (gate failed; and `[SEEN-DATA]` by spec §0)

Now with the v2 **paired per-frequency error model**, which gives an honest frequency-population SE
that v1's replicate-only `z` did not:

| `p` | 163 | 211 | 349 | 433 | 577 | 991 | 2089 | 4159 | 9319 | 19231 |
|---|---|---|---|---|---|---|---|---|---|---|
| excess | +7.26% | +8.53% | +6.68% | +6.76% | +6.80% | +7.48% | +7.27% | +7.55% | +7.13% | +7.29%* |
| ± SE | 1.91% | 1.23% | 0.58% | 0.41% | 0.26% | 0.26% | 0.26% | 0.26% | 0.26% | 0.26% |

Pooled Stouffer `Z = +69.67`, sign 10/10. Ladder, mean over primes as % of REF-RAY:

```
char    − MN-μ6   = +7.2780%
MN-μ6   − MN-neg  = +0.0336%
MN-neg  − MN-free = −0.1258%
MN-free − REF-RAY = −0.1027%      (the entry A3 was meant to certify, and did not)
```

⚠ These numbers may not be promoted. The gate failed, and independently spec §0 caps Arm A at
`[EMPIRICAL — SEEN-DATA, CONTROL-REPAIRED]` because v1's primary was already read.

## 5. ★ A workflow finding, recorded because it is now a pattern

**Two consecutive frozen specs, two gate failures, neither from the instrument or the mathematics:**

- **v1 criterion 3** was *mathematically* ill-posed — a monotone response model applied to a carrier
  that carries its own excess.
- **v2 criterion 5** is *statistically* incoherent — a max-over-64 bound at 3σ, which fails ~82% of
  the time by chance.

Both were written by a careful, isolated designer; both passed review; **both were caught only by
running them.** The forced-structure sections (F1–F14) have been excellent — several are `[PROVED]`
and two of them (F12, F13) correctly diagnosed v1's failure in advance. The weakness is specifically
in **pass-criterion calibration**, which is where a spec makes a probabilistic claim about its own
behaviour under the null. **Any future spec should carry a section that computes the false-failure
rate of each of its own gates**, exactly as it computes power for its primary. That check is cheap,
and it would have caught both failures before either run.

## 6. Status and next

- **§XI.17 remains open.** Two abstentions, zero verdicts, and the live question is unchanged:
  `char − MN-μ6` and its λ/[−1] decomposition (v2's `H-ALIGN`).
- **What v2 did settle:** the plant design is now correct and validated (criteria 1–4, `C-SELFZ`,
  `C-DISP`), and `H-BUDGET` was already settled by algebra in v2 §1.4 — a constraint both arms carry
  cannot produce a contrast.
- **v3 needs exactly two changes:** an order-statistic-aware negative control, and an A3 restricted
  to the range where its target exceeds the noise floor. Everything else carries over.
- Arm B (strata) is governed by **O-B4 descriptive** — the holdout does not exist (D7 attestation).
