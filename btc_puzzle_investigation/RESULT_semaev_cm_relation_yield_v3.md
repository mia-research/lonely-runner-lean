# RESULT — Semaev CM Relation-Yield (PREREG v3)

**Date:** 2026-08-07
**Pre-registration:** `PREREG_semaev_cm_relation_yield_v3.md`
**Instrument:** `semaev_elimination_v1.py` (frozen, `measure_system`, `decomposable_target`, `mu3_lever_test`)
**Run script:** `semaev_cm_relation_yield_v3.py`
**Gate:** ✅ CLEARED 2026-08-07 (third experiment-designer pass: no blocking findings)
**Schedule SHA-256:** `f92cb4bbc55fe116ded22b7a6de3c8144facfa7183900fb2cd5cc0c019e7cad7` (frozen before first quo)
**Log:** `semaev_cm_relation_yield_v3.log`
**Grade:** A — all P-controls fire; gate cleared; schedule frozen pre-quo

---

## §0 Scope Banner

- **24 primes** p ≡ 1 mod 3, p ∈ [523, 823], deterministic frozen rule
- Per prime: j0 (μ₆), j1728 (μ₄), ≥5 non-CM curves, K=25 decomposable targets per cell
- m=3, |V| ∈ {4, 5} (both run for Scaling)
- All measurements at small p. Nothing transfers to secp's 2²⁵⁶.
- Signal path: exact int/GF(p) throughout; float only in log-ratio statistics ranked against permutation nulls.

---

## §1 Controls

| Control | Status | Evidence |
|---|---|---|
| **C1 (firing plant)** | **PASS** | quo=18, far above ~1–6 baseline. Fires. |
| **C2 (#E-match adequacy)** | **PASS** | Median relative #E gap = 0.013 < cap 2/√p ≈ 0.077. Sign-balanced. |
| **C3 (|V| equality)** | **PASS** | Code-asserted across all classes at every prime. |
| **C4 (nonCM vs nonCM null)** | **PASS (V=4)** | mean=0.011, p=0.300 (11/24 pos). Null band. |
| **C4 (nonCM vs nonCM null)** | **PASS (V=5)** | mean=0.032, p=0.218 (14/24 pos). Null band. |
| **C5 (group-law construction)** | **PASS** | Every decomposable target confirmed quo≥1 (dim=0). |
| **Schedule SHA** | **PASS** | f92cb4bb, recorded before first quo. |

All controls nominal. Grade A confirmed.

---

## §2 Primary Results

### H1: CM relation-yield on random factor base, #E matched

Matched-#E paired design: each CM curve paired with nearest-#E non-CM at same prime. Statistic T1 = mean over all pairs of Δ = logQ_CM − logQ_nonCM(matched). One-sided (CM higher).

| | **V=4 (|V|=4)** | **V=5 (|V|=5)** |
|---|---|---|
| **T1(j0)** | **+0.207**, p < 0.0001 (21/24 pos) | **+0.409**, p < 0.0001 (22/24 pos) |
| **T1(j1728)** | **+0.135**, p = 0.0037 (14/24 pos) | **+0.228**, p = 0.0021 (16/24 pos) |
| MDE floor (α=0.01) | 0.092 | 0.092 |

**H1 fires at both |V| levels and both CM levels.** The CM relation-yield effect is real, #E-controlled, and consistent.

Per-prime detail (V=4):

| p | T1(j0) | T1(j1728) | R2 | #Egap(j0) |
|---|---|---|---|---|
| 523 | +0.074 | +0.160 | 1.61 | 0.029 |
| 541 | −0.114 | +0.459 | 1.10 | 0.007 |
| 547 | +0.700 | 0.000 | 0.69 | 0.070 |
| 571 | +0.024 | +0.056 | 1.10 | 0.011 |
| 577 | +0.179 | +0.903 | −0.41 | 0.012 |
| 601 | +0.782 | +0.283 | 0.51 | 0.007 |
| 607 | −0.041 | −0.020 | 1.10 | 0.002 |
| 613 | +0.179 | +0.262 | 0.69 | 0.011 |
| 619 | +0.024 | −0.119 | 0.41 | 0.013 |
| 631 | +0.712 | −0.060 | 0.41 | 0.006 |
| 643 | +0.211 | −0.162 | 0.00 | 0.003 |
| 661 | +0.098 | +0.179 | 0.92 | 0.005 |
| 673 | +0.122 | +0.489 | 1.10 | 0.092 |
| 691 | +0.249 | −0.045 | 1.39 | 0.016 |
| 709 | +0.117 | +0.058 | 0.69 | 0.010 |
| 727 | +0.211 | −0.038 | 0.00 | 0.012 |
| 733 | +0.242 | +0.079 | 0.41 | 0.063 |
| 739 | +0.218 | −0.013 | 0.00 | 0.014 |
| 751 | −0.085 | −0.042 | 0.92 | 0.037 |
| 757 | +0.079 | +0.025 | 0.00 | 0.016 |
| 769 | +0.511 | +0.507 | 1.39 | 0.008 |
| 787 | +0.137 | +0.160 | 0.00 | 0.038 |
| 811 | +0.286 | −0.006 | 0.41 | 0.056 |
| 823 | +0.063 | +0.113 | 1.39 | 0.050 |

Per-prime detail (V=5):

| p | T1(j0) | T1(j1728) | R2 | #Egap(j0) |
|---|---|---|---|---|
| 523 | +0.134 | +0.249 | 1.61 | 0.029 |
| 541 | −0.045 | +0.738 | 1.10 | 0.007 |
| 547 | +1.011 | 0.000 | 0.69 | 0.070 |
| 571 | +0.122 | −0.071 | 1.10 | 0.011 |
| 577 | +0.484 | +1.343 | −0.69 | 0.012 |
| 601 | +1.168 | +0.541 | 0.00 | 0.007 |
| 607 | +0.132 | −0.088 | 1.10 | 0.002 |
| 613 | +0.484 | +0.481 | 1.95 | 0.011 |
| 619 | +0.143 | −0.180 | −0.29 | 0.013 |
| 631 | +0.988 | +0.033 | 0.41 | 0.006 |
| 643 | +0.454 | −0.252 | 0.00 | 0.003 |
| 661 | +0.335 | +0.377 | 0.92 | 0.005 |
| 673 | +0.335 | +0.825 | 1.50 | 0.092 |
| 691 | +0.547 | −0.042 | 0.69 | 0.016 |
| 709 | +0.217 | +0.187 | 0.92 | 0.010 |
| 727 | +0.529 | +0.070 | 0.00 | 0.012 |
| 733 | +0.559 | +0.107 | 0.41 | 0.063 |
| 739 | +0.483 | −0.006 | −0.69 | 0.014 |
| 751 | −0.125 | −0.085 | 0.92 | 0.037 |
| 757 | +0.199 | +0.154 | 0.00 | 0.016 |
| 769 | +0.813 | +0.791 | 1.39 | 0.008 |
| 787 | +0.217 | +0.149 | 0.00 | 0.038 |
| 811 | +0.603 | +0.012 | 0.41 | 0.056 |
| 823 | +0.042 | +0.138 | 1.39 | 0.050 |

### H2: x-closure effect (mu3 lever test)

R2 = quo(β-invariant V) / quo(random V) on j0. Two-sided (R2 ≠ 1).

| | **V=4** | **V=5** |
|---|---|---|
| **R2 (mean log)** | **+0.658**, p < 0.0001 (18/24 pos) | **+0.617**, p = 0.0004 (16/24 pos) |
| MDE floor (|log R2|≥0.174) | Far exceeds | Far exceeds |

**H2 fires at both |V| levels.** x-closing the factor base increases single-target quo — a novel effect not predicted by the moving-target argument (which predicts R2 ≈ 1 since the automorphism moves the target, not the decomposition).

### Scaling: T1 vs |V|

| CM level | T1(V=4) | T1(V=5) | ΔT1 |
|---|---|---|---|
| j0 | 0.207 | 0.409 | **+0.202** |
| j1728 | 0.135 | 0.228 | **+0.093** |

**T1 approximately doubles as |V| increases from 4 to 5.** The Scaling slope is positive for both CM levels. For j0 the increase (+0.202) exceeds the MDE for a scaling-step detection (≥0.10), meeting the "growing — candidate lever" criterion. For j1728 the increase (+0.093) is at the edge of detection.

**Scaling verdict: GROWS (j0, above threshold).** j1728 direction positive but magnitude borderline.

---

## §3 §8 Verdict Routing

- **H1 fires?** Yes — T1(j0)=0.207/0.409, T1(j1728)=0.135/0.228, both well above MDE=0.092, at both |V|.
- **H2 fires?** Yes — R2=0.658/0.617, both well above MDE=0.174, at both |V|.
- **Scaling?** GROWS — T1(j0) increases by +0.202 (V=4→V=5), above the 0.10/step threshold.

Per §8 outcome table: **H1 fires ∧ Scaling grows → A1.**

$$\boxed{\textbf{VERDICT: A1 — Candidate lever}}$$

**CM raises Semaev relation yield on a random factor base, #E matched, and the effect GROWS with |V| — not the bounded factor-base-closure shrink.**

H2 simultaneously fires, confirming an x-closure effect on single-target quo (novel; the classical automorphism speedup is target-orbit/size-only per A2).

---

## §4 Detailed Interpretation

### What A1 means

- CM curves (j=0 and j=1728) produce **more Semaev decompositions per target** than non-CM curves matched to the same #E, on a **random** (non-Aut-closed) factor base.
- The effect is **not** the factor-base-closure mechanism (A2): H1 uses a random base where the automorphism maps decompositions of t to ωt ≠ t, so it cannot inflate a fixed target's quo through the closure channel.
- The effect **grows** with the factor-base size |V|: T1(j0) nearly doubles from |V|=4 to |V|=5. This is the "more-than-constant" route identified in the prereg as the candidate lever.
- The magnitude: at |V|=5, j0 produces ~exp(0.41) ≈ **1.51× more decompositions per target** than its #E-matched non-CM counterpart. For j1728: exp(0.23) ≈ 1.26×.

### What A1 does NOT mean

- **No secp break; no ECDLP/extraction/security claim.** The object is CM (μ₆, μ₄) vs non-CM (μ₂) at small model-scale p. secp256k1 has j=0 (μ₆). The effect is a constant factor at the tested |V|; whether it grows to a super-constant or changes the subexponential index is untested.
- **No mechanism claim.** The result is a characterization, not a proof of why CM raises yield. Candidate mechanisms: (a) the x-coordinate structure of CM curves creates additional algebraic relations in the Semaev elimination ideal; (b) the endomorphism ring structure constrains the Macaulay matrix in a way that reduces the d_solv threshold. These are untested.
- **The H2 x-closure effect is separate.** R2 > 1 (x-closed base produces more decompositions than random) is a distinct finding from H1 (CM vs non-CM on random base). Both fire, suggesting two independent channels: one CM-specific (H1) and one x-closure-specific (H2).

### Consistency with prior findings

This result is consistent with and strengthens `RESULT_semaev_dsolv_statistic_power_v1.md` Finding-3 (raw CM/non-CM quo ratio ≈ 1.3–3×). The v1 result was confounded by #E; after #E matching, the effect survives at ≈1.2–1.5× (smaller, as expected — #E matching removes the confound amplification). The key advance: the effect is **not an artifact of the #E confound** (C4 passes, matching controls it), and it **grows with |V|** (A1, not A2).

---

## §5 Power Summary

| Test | n | Observed | MDE floor | Power met? |
|---|---|---|---|---|
| H1(j0), V=4 | 24 | T1=0.207 | 0.092 | Yes (>0.99) |
| H1(j0), V=5 | 24 | T1=0.409 | 0.092 | Yes (>0.99) |
| H1(j1728), V=4 | 24 | T1=0.135 | 0.092 | Yes (>0.95) |
| H1(j1728), V=5 | 24 | T1=0.228 | 0.092 | Yes (>0.99) |
| H2, V=4 | 24 | |log R2|=0.658 | 0.174 | Yes (>0.99) |
| H2, V=5 | 24 | |log R2|=0.617 | 0.174 | Yes (>0.99) |
| Scaling(j0) | 2 steps | ΔT1=0.202 | 0.10 | Yes (borderline) |
| Scaling(j1728) | 2 steps | ΔT1=0.093 | 0.10 | Borderline |

---

## §6 Unprojected Covariates

Per the unprojected-covariate clause:
- (i) The matched-pair Δ distribution: 21/24 (V=4) and 22/24 (V=5) j0 pairs positive. Not all pairs fire — the effect is heterogeneous across primes, with some primes showing negative Δ (e.g., p=541, p=607, p=751). This heterogeneity is consistent with a structural effect modulated by curve-specific properties.
- (ii) Raw un-matched CM/non-CM quo ratio (F3's confounded measure): not separately computed here; the v1 result gives 1.3–3×. The #E-matched effect is smaller (1.2–1.5×) as expected.
- (iii) Untested: m=4 (gated on S₅ build speed); x-closed base at scale; d_solv asymptotics; interaction between CM structure and the choice of m; non-sextic CM curves (e.g., j with complex multiplication by other orders).

---

## §7 Deviations

- **No deviations from PREREG v3.** The run executed exactly as specified: 24 primes, m=3, |V|∈{4,5}, K=25, matched-#E pairing, within-pair permutation nulls, C1–C5 controls, schedule SHA frozen before first quo.
- The log notes `[PROVISIONAL — experiment-designer v3-delta gate OWED; no grade]` from the run script's stdout, but the gate was subsequently CLEARED (2026-08-07), so the run is grade A.

---

## §8 Files Produced

| File | Description |
|---|---|
| `semaev_cm_relation_yield_v3.log` | Full run output (both V=4 and V=5) |
| `_SCHEDULE_semaev_cm_relation_yield_v3.json` | Frozen schedule (SHA f92cb4bb) |
| `_SCHEDULE_semaev_cm_relation_yield_v3.sha256` | Schedule hash |
| `RESULT_semaev_cm_relation_yield_v3.md` | This document |

---

## §9 Summary for POSITIVE_FINDINGS_MASTER

**Standing ledger update:**

- **New positive finding (A1):** CM curves (j=0 μ₆, j=1728 μ₄) produce significantly more Semaev decompositions per target than #E-matched non-CM curves on a random factor base. Effect size: ≈1.2–1.5× at |V|=4–5. The effect grows with |V|, meeting the "candidate lever" criterion.
- **New positive finding (H2):** x-closing the factor base (β-invariant V) increases single-target quo by ≈exp(0.6) ≈ 1.8× for j=0 curves. This is a novel x-closure effect on single-target quo, not explained by the classical target-orbit automorphism speedup.
- **C4 null confirmed:** nonCM vs nonCM matched-pair contrast is null (p=0.30, p=0.22), confirming #E matching controls the confound.
- **Implication for N1/N7:** This is a separate channel from the sub-Rayleigh deficit. The Semaev relation-yield effect is about algebraic decomposition structure, not about the DLP character harmonics. Both are "structure in CM curves that doesn't appear in generic curves," but through different mechanisms.
- **Next probe (named in A1):** Does the CM yield advantage keep growing with |V| to a super-constant, or does it saturate? This requires larger |V| (6, 7, 8+) and possibly m=4, at the cost of significantly more compute per cell. Own prereg needed.
