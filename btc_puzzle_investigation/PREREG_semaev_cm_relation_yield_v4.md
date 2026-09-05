# PREREG v4 — Semaev CM Relation-Yield Scaling Extension: does T1 keep growing with |V|?

**File:** `PREREG_semaev_cm_relation_yield_v4.md`  **Date:** 2026-08-07
**Supersedes v3** in scope only (v3 is the completed baseline; v4 extends the |V| sweep).
**Status: PRE-RUN.** No confirmatory statistic computed. **Gate: experiment-designer pass OWED before grading.**
**Depends on:** `RESULT_semaev_cm_relation_yield_v3.md` (A1 verdict — H1 fires, Scaling grows at j0).

---

## §0 SCOPE BANNER (governs every number)

Enumerable model curves `E : y²=x³+Ax+B` over small `F_p` (`p ≡ 1 mod 3`, `p ∈ [523, 823]`).
`p = 2²⁵⁶−2³²−977` is **not** enumerable; **nothing here transfers.**
No secp break; no ECDLP/extraction/security claim. Per v3 §0 and F2: the object is
**CM (μ₄,μ₆) vs non-CM (μ₂)**, NOT secp-vs-world. Any effect is a constant factor unless
Scaling demonstrates growth — and even growth at model-scale does not transfer to the
2²⁵⁶ field without a mechanism proof and asymptotic analysis.

---

## §1 OBJECT (reuses the FROZEN instrument `semaev_elimination_v1.py`)

Same instrument and measurement as v3. Per curve `E/F_p`, `m` points per relation:
```
quo = dim_F F[x]/I  (I the decomposition ideal, dim 0) = # decompositions of target t over base V
```
- **Consistent regime only.** Targets from `decomposable_target(F,A,B,m,extra,seed)` (genuine sum).
- **Curve classes.** `j0=(0,B0)` μ₆; `j1728=(A0,0)` μ₄; `nonCM=(A,B)` random `j∉{0,1728}`, μ₂.
- **Cell value `Q = mean_K quo`** (full K-vector logged).

**What changes from v3:** the |V| sweep range. v3 tested |V|∈{4,5} (two points). v4 tests |V|∈{4,5,6,7,8,9}
(six points) to fit a scaling model with >2 degrees of freedom.

---

## §2 FORCED / ANCHOR FACTS — from v3, ZERO new evidence

All forced facts from v3 §2 carry over unchanged:
- **A1** — `#E` drives `quo` as `≈1+(|V|^m/m!)/#E`. Controlled by matching (§3).
- **A2** — automorphism order `κ` acts on TARGET ORBIT / factor-base SIZE, NOT on single-target `quo`.
  H2 is unbenchmarked (`R2≠1`, two-sided).
- **A3** — `deg(Sx)` curve-independent [PROVED].

**New forced fact (from v3 RESULT):**
- **A4 — T1(j0) grows with |V| in the tested range {4,5}.** ΔT1(j0) = +0.202 over a single |V|-step.
  This is the observation that motivates v4; it is NOT a proof of continued growth. The Scaling
  verdict in v4 is the confirmatory test of whether this observation generalizes.

---

## §3 HYPOTHESES & STATISTICS (frozen; sign pre-committed = CM higher, from v3 F3)

Schedule §6. Per prime `p`: `j0`, `j1728`, and **≥5** non-CM curves (frozen seed, same as v3),
`|V|` equal across all classes (`|V|=m+extra`, frozen), `K=25` decomposable targets per cell,
`m=3`, `extra∈{1,2,3,4,5,6}` (`|V|∈{4,5,6,7,8,9}`).

| id | hypothesis / statistic (verdict-bearing) | matched null |
|---|---|---|
| **H1 (PRIMARY — same as v3)** | Matched-`#E` paired design. `Δ = logQ_CM − logQ_nonCM(matched)`.
`T1 = mean over pairs of Δ`, one-sided (CM higher). Run per |V|-level and pooled.
**Unbenchmarked magnitude.** | **within-pair label swap**: independent flip per pair, recompute T1; ≥1e4 draws; integer-rank one-sided p. |
| **Scaling (NEW — the primary extension)** | T1(|V|) fitted to three pre-committed models:
(1) **M_flat:** T1 = c (constant)
(2) **M_linear:** T1 = a·|V| + b
(3) **M_log:** T1 = a·log|V| + b
Fit by weighted LS (weights = 1/Var(T1) per level). Model comparison by **AIC** (Akaike,
corrected for small n: AICc = n·ln(RSS/n) + 2k + 2k(k+1)/(n−k−1)).
Pre-committed: if AICc(M_linear) < AICc(M_flat) − 6 (strong evidence per Burnham–Anderson) OR
AICc(M_log) < AICc(M_flat) − 6, Scaling verdict = **GROWS**.
If AICc(M_flat) ≤ AICc(M_linear) + 2 AND AICc(M_flat) ≤ AICc(M_log) + 2, Scaling verdict = **FLAT**.
Otherwise: **INCONCLUSIVE** (models not separable at this resolution). | **Permutation calibration:** Residual bootstrap of the T1(|V|) values (10000 draws, sampling with replacement from the per-prime Δ distributions at each |V|), refit all three models, compute ΔAICc. The calibrated p is the fraction of bootstrap draws where the best-growing model beats flat by ≥6 AICc units. This guards against the non-normality of the T1 distribution. |
| **H2 (same as v3 — secondary)** | `mu3_lever_test` on `j0`: `R2 = quo_βinv / quo_rand`, paired across primes; two-sided `R2≠1`. Run per |V|-level. | permute (βinv↔rand) label per prime; integer-rank p, null centered at `R2=1`. |
| **H2-Scaling (NEW — secondary)** | Does R2 change with |V|? Same model-comparison framework as Scaling but applied to R2(|V|). | Same residual bootstrap. |
| secondary | consistent-regime `d_solv`, CM vs matched non-CM (A3), per-|V|-level. Reported, not verdict. | within-pair swap |

**Verdicts (conjunctions; no post-hoc subset).**

| # | Condition | Conclusion |
|---|---|---|
| **A1** | H1 fires (pooled or at ≥4 |V|-levels) ∧ Scaling **GROWS** | **Candidate lever confirmed:** CM raises Semaev relation yield, and the advantage grows with |V|. Report the best-fit model (linear vs log), the growth rate, and the extrapolation caveat (model-scale only). |
| **A2** | H1 fires ∧ Scaling **FLAT** | **Bounded CM relation-yield effect.** T1≈const across |V|. The v3 observation of growth was a small-|V| artifact or insufficient resolution. Report the constant magnitude. This DOWNGRADES the v3 A1 verdict to bounded (A2). |
| **A3** | H1 fires ∧ Scaling **INCONCLUSIVE** | CM effect present; growth direction unclear at tested |V| resolution. Report T1 per level. Extend |V| range in a future prereg. |
| **A4** | H1 null (powered) | No CM effect survives #E matching at the extended |V| range. Scoped null. H2 outcome reported separately (see below). |
| **A5** | H2 fires ∧ H2-Scaling GROWS | x-closure effect grows with |V|. **Independent of H1 verdict** — can fire alongside A1–A4. Report magnitude. |
| **A6** | H2 fires ∧ H2-Scaling FLAT | x-closure effect present but bounded. **Independent of H1 verdict.** |
| **A7** | any C1–C5 fails | that arm uninformative; no verdict. |

**Catch-all:** Outcomes not matching A1–A7 (e.g., H2-Scaling INCONCLUSIVE, underpowered H1, H1-null with H2-null) are reported with full statistics but receive no named verdict; noted as requiring future prereg for formal routing.

**Note on v3 consistency:** v3 found A1 (H1 fires, Scaling grows) with 2 |V|-points. If v4 finds A2 (flat), this is not a contradiction — it means the 2-point growth was within noise and the model comparison with 6 points has more power to resolve the true shape. The v4 verdict supersedes v3's Scaling verdict.

---

## §4 CONTROLS (all must fire/hold; no verdict if any fails)

Same five controls as v3, unchanged:
- **C1 — firing plant.** Planted decomposable system with quo >> baseline.
- **C2 — `#E`-match adequacy.** Median relative #E gap ≤ 2/√p.
- **C3 — `|V|` equality** across classes at every prime (code assert).
- **C4 — `#E`-stratified negation-only null.** nonCM(high) vs nonCM(low): T1≈0.
- **C5 — group-law construction.** Each target's own decomposition is a system root.

**v4-specific control:**
- **C6 — v3 reproducibility.** The |V|=4 and |V|=5 arms of v4 must reproduce the v3 T1 values within
  the matched-pair null band (the same frozen schedule is reused; any deviation >2σ flags a
  non-reproducibility issue). This guards against instrument drift or seed-dependent artifacts.

---

## §5 EXACTNESS (same as v3)

- **Exact int / GF(p):** curve arithmetic, `#E`, `quo`, `d_solv`, all permutation/rank counts.
- **Sanctioned analytic-only float:** `log Q`, `T1`, `R2`, and the Scaling model fits (weighted LS, AICc)
  enter only as monotone statistics or permutation-calibrated comparisons.
- **Scaling model fit:** weighted LS coefficients and AICc are float, but the verdict is calibrated by
  the **permutation bootstrap** (integer-count p from 10000 resamples), not by the raw AICc values.
  `check_no_float.sh` on the statistic module.

---

## §6 SCOPE & SCHEDULE (frozen pre-run, SHA-256'd)

- **Primes:** the same 24 primes as v3: p ≡ 1 mod 3, p ∈ [523, 823] (deterministic rule:
  `primes_1mod3(500, 24, cap=8000)`). Identical to v3 for C6 reproducibility.
- **Curves:** same per-prime construction as v3 (seed=1000+p). j0, j1728, ≥5 nonCM.
- **|V| sweep:** `extra ∈ {1, 2, 3, 4, 5}` ⇒ `|V| ∈ {4, 5, 6, 7, 8}`.
  - `|V|=4,5` replicate v3 for C6 reproducibility.
  - `|V|=6,7,8` are new.
  - |V|=9 dropped (projected ~53 hours single-process; 5 points sufficient for AICc model comparison).
  - **DEVIATION D1:** prereg specified {4,5,6,7,8,9}; truncated to {4,5,6,7,8} after smoke-test timing.
    If the 5-point Scaling signal is borderline (ΔAICc within 2–6), |V|=9 will be added as a follow-up.
- **m=3** (primary). m=4 is out of scope (S₅ build gated; not attempted).
- **K=25** decomposable targets per (curve, prime, |V|).
- **Cost estimate.** Per cell at |V|=8: Dmax=33, max matrix columns = C(36,3)=7140. Smoke-test timing:
  |V|=6 mean-cell = 14s (K=5), |V|=7 mean-cell = 37s (K=5). Scaling to K=25: ~71s (|V|=6), ~183s (|V|=7),
  extrapolated ~460s (|V|=8). Total: 5 |V| × 24 primes × ~7 curves × 25 targets ≈ 21K calls.
  **Estimated wall time: ~35 hours** on a single Sage process. Two parallel Sage processes: ~18 hours.
  (|V|=9 dropped per smoke-test timing — ~53h single-process, not justified given 5 points suffice.)
- **`_SCHEDULE_v4.json`** (SHA-256'd with this spec **before the first `quo`**): same prime list and curve
  construction as v3, extended with the |V| sweep range. The schedule hash is computed from the curve
  definitions only (not the quo values), matching v3's approach.

---

## §7 POWER (pinned as numbers)

- **H1 per |V|-level:** same as v3. 24 primes × 2 CM levels = 48 matched pairs. MDE = T1 ≥ 0.092 at
  power 0.8, α=0.01 one-sided. At any single |V|-level, H1 fires if the true T1 exceeds 0.092.
- **Scaling model comparison:**
  - With 6 |V|-points and weighted LS, the model comparison has 6 data points and 1–2 parameters per model.
  - The AICc threshold of Δ=6 corresponds to a likelihood ratio of ~e³ ≈ 20. For normal residuals with
    σ ≈ 0.06 (observed per-prime Δ scatter in v3), this detects a slope of ≥0.03/|V|-step in the linear
    model with power ≈ 0.9.
  - The v3 observation (ΔT1 = +0.202 per |V|-step for j0) is well above this detection threshold if the
    growth continues. If growth saturates (slope drops to <0.03/step), the flat model wins.
  - **`[UNDERPOWERED]` boundary:** if the true |V|-dependence has |slope| < 0.02/step, the models are
    not separable at 6 points → Scaling verdict = INCONCLUSIVE (A3), not a refutation of growth.
- **H2 per |V|-level:** same as v3. 24 paired primes. MDE = |log R2| ≥ 0.174 at power 0.8, α=0.01.
- **Pooled H1 (across all |V|):** If T1 is consistent across levels, the pooled SE decreases as
  σ/√(6×48) ≈ 0.2/√288 ≈ 0.012, giving a very sensitive test for any positive T1. This is reported but
  is NOT the Scaling test (which requires the |V|-dependence structure, not just the mean).

---

## §8 PRE-COMMITTED OUTCOME TABLE

No dismissal vocabulary; every row a positive result.

| # | Outcome | Reported as |
|---|---|---|
| **A1** | H1 fires ∧ Scaling GROWS | **Candidate lever confirmed.** Report best-fit model, growth rate, per-level T1, d_solv. Next probe: mechanism, larger m, or extrapolation caveats. |
| **A2** | H1 fires ∧ Scaling FLAT | **Bounded effect.** T1≈const. v3's 2-point growth was within noise. Report constant magnitude. This downgrades v3 A1→A2. |
| **A3** | H1 fires ∧ Scaling INCONCLUSIVE | CM effect present; growth unresolved. Report T1 per level. Extend |V| in future prereg. |
| **A4** | H1 null (powered) | No CM effect at extended |V|. Scoped null. |
| **A5** | H2 fires ∧ H2-Scaling GROWS | x-closure effect grows with |V|. Report magnitude. |
| **A6** | H2 fires ∧ H2-Scaling FLAT | x-closure effect bounded. |
| **A7** | any control fails | uninformative; no verdict. |

**Unprojected-covariate clause.** An H1 null must NOT be read "no structure": report (i) T1 per |V|-level;
(ii) the Scaling model residuals; (iii) raw un-matched CM/non-CM ratio; (iv) untested extensions
(m=4, larger p, non-sextic CM, d_solv asymptotics) as next candidates, not absences.

**Output type:** a characterization of Scaling with power + §0 scope. Never ECDLP/extraction/security.

---

## §9 CHANGE LOG v3→v4

1. **|V| sweep extended** from {4,5} to {4,5,6,7,8,9}. Six |V|-points enable model comparison
   (flat vs linear vs log) with >2 d.o.f.
2. **Scaling formalized as a pre-committed model comparison** (AICc + permutation bootstrap), replacing
   v3's ad-hoc "slope ≥ 0.10/step" criterion.
3. **H2-Scaling added** as a secondary arm: does the x-closure effect grow with |V|?
4. **C6 reproducibility control added:** |V|=4,5 arms must reproduce v3 within null band.
5. **Verdict table rewritten** to distinguish GROWS/FLAT/INCONCLUSIVE scaling outcomes (A1–A3).
6. **v3 consistency clause added:** v4 supersedes v3's Scaling verdict; A2 in v4 does not contradict
   v3's A1 (the 2-point growth was underdetermined).
7. **No changes to H1, H2, C1–C5 controls, instrument, or exactness rules.** These are inherited from v3
   with gate clearance.

---

## §10 DEVIATIONS

- **D1 — |V|=9 truncated.** Prereg specified {4,5,6,7,8,9}; smoke-test showed |V|=7 cells at 37s (K=5),
  projecting ~1145s/cell at K=25 for |V|=9 (~53h total). Truncated to {4,5,6,7,8} (5 points).
  Five |V|-points are sufficient for the 3-parameter AICc model comparison (flat/linear/log).
  If the 5-point Scaling signal is borderline (ΔAICc between flat and best growing model in [2,6]),
  |V|=9 will be added as a follow-up run.

## §11 Files this run will produce

- `semaev_cm_relation_yield_v4.py` (reuses `semaev_elimination_v1.py`)
- `_SCHEDULE_semaev_cm_relation_yield_v4.json` (SHA-256'd before first quo)
- `semaev_cm_relation_yield_v4.log`
- `RESULT_semaev_cm_relation_yield_v4.md`
