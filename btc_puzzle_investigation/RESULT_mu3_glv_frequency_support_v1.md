# RESULT — is the sub-Rayleigh deficit μ₃/GLV-organized in the b-frequency? A τ-robust scoped null

**Date:** 2026-08-10. Executes `PREREG_mu3_glv_frequency_support_v1.md` + `_v2.md` (spec frozen before data).
**Grade:** `[EMPIRICAL — scoped null, τ-robust, well-powered]`. **No grade change** to the underlying
−13.99σ deficit (`RETROSPECTIVE_FINDING_01_subrayleigh_demotion_v1.md`), which stays real,
matched-null-surviving, and mechanism-open.
**Artifacts:** `mu3_glv_frequency_support_v1.py` (runner, `--selftest` clean); run logs
`mu3_glv_frequency_support_v1_run.log` (τ=0.10), `_tau005.log`, `_tau015.log`; forced-algebra
`verify_U_pullback.py` + the designer's `partA.py`/`partA4fix.py`/`partB_fast.py`.

---

## 1. What was tested (the object, not a proxy)

Whether the deficit's **carrier** — the ~8% excess of near-zero harmonics (`ρ=|U|/√(n−1) < τ`) of
`U(a₀,b,c)=Σ_{d=1}^{n−1} e_p(bx_d+cy_d)e_n(a₀d)` — is **organized as μ₃-multiplicative co-occurrence in
the x-frequency b** (near-zeros clustering within the GLV triples `{b,βb,β²b}`), versus diffuse.

**Primary statistic** `S = Σ_{a₀-reps,c,μ₆-orbits} C(k,2)` = count of near-zero pairs sharing a μ₃-triple,
pooled over 24 a-orbit reps and all columns c, on ±-reps (forced μ₂ folded away). **Null-B** =
marginal-preserving equipartition of the K near-zeros into the R/3 triples (exact combinatorial moments,
validated vs empirical permutation in `--selftest`). Decision = one-sided Stouffer Z over the prime schedule.

The statistic is **not forced**: within-triple spread ≠ 0 at a₀≠0 (A5), and S is orthogonal to the l²
conservations `Σ_{b,c}|U|²=p²(n−1)` (A1), `Σ_a|U|²=n(n−1)` (A2), and invariant to the forced μ₂ (A3).
All verified exactly (max|Δ|≤1.6e−15 on the exact-int point path).

## 2. Controls (all behaved)

| control | result | required |
|---|---|---|
| **Implementation** (§11): forced-diagonal intra-orbit Var(\|U\|) | **5.7e−27 ≈ 0** | ≈0 (pullback indexing correct) |
| **Plant** (5% of triples forced near-zero, p=2089) | **Z = +5965** | fire ≫ 0 ✓ |
| **Negative-scatter** (same # near-zeros, μ₃-agnostic) | **Z = −0.75** | stay ~0 ✓ |

The plant/scatter pair confirms **specificity**: S keys on μ₃-*clustering*, not on the marginal near-zero
rate. The statistic can detect sub-percent pooled clustering (`partB_fast.py` power table).

## 3. Result — all near-zero pairs co-occur at chance, at every threshold

Nine prime-order curves `y²=x³+7`, all qualifying primes in the five pre-registered windows (no filtering),
24 a-reps.

| p | Z (τ=0.05) | Z (τ=0.10, primary) | Z (τ=0.15) |
|---|---|---|---|
| 2089  | +0.59 | +1.04 | +0.76 |
| 2143  | −0.82 | −0.50 | +0.32 |
| 4159  | +0.38 | +1.91 | −0.22 |
| 8191  | −1.23 | +0.51 | −0.55 |
| 8209  | −1.78 | +0.31 | −0.14 |
| 8293  | −0.29 | +0.49 | +0.02 |
| 16477 | −0.35 | −0.73 | −0.51 |
| 19231 | −2.72 | −0.52 | +0.72 |
| 19249 | +1.81 | −0.54 | −0.16 |
| **POOLED Stouffer** | **−1.47** | **+0.66** | **+0.08** |

- All three pooled |Z| < 3. Individual Z scatter about 0 with **no trend in p** and **no sign coherence**
  (adjacent 19231/19249 flip −2.72/+1.81 at τ=0.05; pooled sign flips −1.47→+0.66→+0.08 across τ). This is
  a noise signature, not a threshold-hidden signal.
- **Secondary `S_GLV` (descriptive):** `≈ 0.3332 = 1/3` at every prime and every τ — exactly the η² null
  baseline for unstructured size-3 grouping. So there is no μ₃ organization in the **bulk/high tail** either,
  not just the near-zero tail.

## 4. Reading (pre-committed outcome table, v1 §9)

Pooled |Z| < 3 at the primary τ=0.10 (and τ-robustly at 0.05, 0.15) ⇒ **SCOPED NULL**. Per the pre-commit,
we **abandon the hypothesis** "the deficit's near-zero excess is μ₃-multiplicatively organized in the
b-frequency (near-zero co-occurrence within GLV triples)."

**What this closes (named, so the negative carries the same burden as a PROVED claim):**
- **Object:** the near-zero harmonics of `U(a₀,b,c)` on CM `y²=x³+7`.
- **Class of observable:** μ₃-multiplicative co-occurrence of near-zeros within the frequency triples
  `{b,βb,β²b}` (and the bulk η² μ₃-grading, via `S_GLV`).
- **Power:** resolves sub-percent pooled relative excess (plant fires at Z≈+6000 for 5%); 9 primes to p≈19k.
- **Scope:** CM family `y²=x³+7`, `p∈{2089…19249}`, 24 a-orbit reps, `τ∈{0.05,0.10,0.15}`.

**What this does NOT touch (the null is scoped, never "the deficit is structureless"):**
- **Higher μ₃-moments** — phase/argument alignment of `U` within a triple, not just the ≥2-near-zero
  co-occurrence this statistic counts. A triple could be μ₃-organized in *phase* while its magnitudes are
  co-occurrence-flat.
- **The c-axis** (y-frequency) organization, and the **additive** (not multiplicative) b-structure.
- **The curve-tied diagonal `c = ±b`** (the `xy_interference` test-3 axis, a non-μ₃ structure).
- The **−13.99σ deficit itself**, which is unchanged: real, matched-null-surviving, universal over
  characters, mechanism-open. Its live candidate remains the **row-budget shadow** (Frontier #17,
  `row_budget_lowtail_v1..v3`), and its decision-relevant open re-test remains the **p-scaling
  const-vs-1/log p** separation (retrospective §4) — neither affected by this result.

## 5. Net

The `W_N` route was locked analytically (`RESULT_intertwined_proxy_WN_tested_v1.md`); its productive 2-D
descendant — the μ₃/GLV frequency-support question — was pre-registered, powered, and run. The deficit's
near-zero carrier is **not** μ₃-multiplicatively clustered in b at the tested thresholds and power. The
deficit stays exactly as live as before; the next probes are the unprojected subspaces above (phase-within-
triple μ₃-moments and the c/`c=±b` axes are the natural first two), each its own pre-registration.
