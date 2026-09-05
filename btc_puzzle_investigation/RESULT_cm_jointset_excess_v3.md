# RESULT — A-joint (CM-structured joint-set synergy): scoped null at model scale

**Grade:** `[VERIFIED-scope — scoped null; discovery + OOS confirmation + scale ladder to 2¹⁶, R=10⁴, all firing controls fired]`
**Date:** 2026-08-22. **Prereg:** `PREREG_cm_jointset_excess_v3.md` (SHA `3560eb73cce2…`, second-read
DISCHARGED). **Runner:** `cm_jointset_excess_v3.py` (imports `model_curve_infra_v1.py`; `check_no_float`
exits 0). **Logs:** `log_ajoint_v3_controls.txt`, `log_ajoint_v3_discovery.txt`,
`log_ajoint_v3_confirmation.txt`.

**NOT a closure.** Model curves only, `q ∈ {541,…,65539}` (`q ≲ 2¹⁶`); `q=2²⁵⁶−2³²−977` is not
enumerable and carries ZERO power against secp256k1. This is a bounded magnitude with stated power and
scope, not a statement that the avenue is dead. No ECDLP/extraction/security claim.

---

## Object
The synergy `E = Î(cross-feature ; J | Φ^pt)` of an `m=3` set of independently-drawn small-interval
scalars `d_i` on matched CM (`j=0`) vs non-CM model curves: does CM structure raise the joint MI of the
SET's public cross-features about a joint label ABOVE the per-point marginals, and is any such excess
CM-specific? Three projected channels:
- **primary (Semaev-μ₃):** `Ψ = χ₃(S₃(x₁,x₂,x₃))` vs `J = (d₁+d₂+d₃) mod 3`;
- **omnibus (additive-combo):** `L_sum = (L₁₂+L₁₃+L₂₃) mod 3`, `L_{ij}=χ₃(x(P_i+P_j))`, vs `J`;
- **secondary (interval):** `Ψ` vs `J' = (Σ block(d_i)) mod 2`.
Verdict statistic `Δ = Î_prim(CM) − Î_prim(non-CM)`; exact within-`Φ^pt`-stratum permutation p-values.

## Firing controls (all fired, R=10⁴) — the null is EARNED
| control | channel | result |
|---|---|---|
| PC-SEM (resample `d₃` s.t. `χ₃(S₃)==J`) | primary | fires p=1e-4, monotone mi 0.058→0.155→0.524, non-degenerate (distinct_Ψ=3, S₃≠0) |
| PC-COMBO (resample `d₃` s.t. `L_sum==J`, indep. `P₃`) | omnibus | fires p=1e-4, monotone mi 0.062→0.167→0.536, non-degenerate (distinct_Lsum=3) |
| PC-GRADE | resolution floor | fires p=1e-4, monotone |

Every measurement below is on an instrument proven live by these controls (VOID rule satisfied).

## Result — every CM-arm channel within the matched null, both tiers

**Discovery (N=5,000):**
| q | primary CM (p) | combo CM (p) | interval CM (p) | Δ |
|---|---|---|---|---|
| 541 | 0.0333 (0.19) | 0.0289 (0.88) | 0.0165 (0.28) | +0.0009 |
| 571 | 0.0296 (0.79) | 0.0301 (0.73) | 0.0160 (0.39) | −0.0049 |
| 577 | 0.0329 (0.23) | 0.0276 (0.97) | 0.0166 (0.25) | −0.0003 |

**Confirmation (OOS, N=20,000):**
| q | primary CM (p) | combo CM (p) | interval CM (p) | Δ | nonCM primary (p) |
|---|---|---|---|---|---|
| 2029 | 0.0076 (0.64) | 0.0078 (0.46) | 0.0038 (0.55) | −0.0015 | 0.0091 (0.012) |
| 2053 | 0.0075 (0.73) | 0.0080 (0.36) | 0.0045 (0.053) | −0.0008 | 0.0083 (0.20) |
| 2089 | 0.0073 (0.82) | 0.0077 (0.53) | 0.0037 (0.69) | −0.0010 | 0.0083 (0.19) |

**Scale ladder (N=5,000; non-CM arm via bounded random matcher, exact order match, D-LADDER):**
| q | primary CM (p) | combo CM (p) | interval CM (p) | Δ |
|---|---|---|---|---|
| 1033 | 0.0298 (0.77) | 0.0308 (0.59) | 0.0191 (0.020) | −0.0020 |
| 4111 | 0.0358 (0.026) | 0.0322 (0.34) | 0.0148 (0.69) | +0.0056 |
| 16417 | 0.0324 (0.31) | 0.0313 (0.50) | 0.0154 (0.53) | +0.0007 |
| 65539 | 0.0285 (0.92) | 0.0295 (0.80) | 0.0134 (0.95) | −0.0044 |

- **CM arm: not significant (p<0.01) in any channel at any of the 10 primes** (q from 541 to 65539).
- **Δ ≈ 0 across the whole schedule AND flat across the scale ladder to 2¹⁶** — Δ>0 on 1/3 discovery,
  0/3 confirmation, 2/4 ladder; `Δ∈[−0.005,+0.006]`, no upward trend with q. `|Δ| < MI_min` everywhere
  (`MI_min = 7.9×10⁻³` @5k, `2.0×10⁻³` @20k). The raw `Î` shrinks with N (0.033→0.0075), the fingerprint
  of plug-in bias absorbed by the matched null, not signal.
- **Marginal hits, all surfaced and tested — none survives:** across **60 tests** (10 primes × 2 arms ×
  3 channels), three fall in [0.01, 0.05] and **none below 0.01** — the exact multiple-comparison noise
  floor (expect ~3 below 0.05, ~0.6 below 0.01). The three: `nonCM primary p=0.012` @2029 (wrong arm,
  1/3 primes), `CM primary p=0.026` @4111 (right arm — but 1/4 ladder primes, does not reproduce at
  1033/16417/65539), `CM interval p=0.020` @1033 (1/4 primes, does not reproduce). Each fails
  reproduction; none is a lead.

## Verdict (pre-committed, prereg §7/§9 "Scoped null" row)
No CM-specific joint-set synergy in the `{Semaev-μ₃, additive-combo, interval}` channels of an `m=3` set
across `q ∈ {541,…,65539}` (10 primes, discovery + OOS confirmation + scale ladder to 2¹⁶), at power
`MI_min = 7.9×10⁻³` (N=5k) / `2.0×10⁻³` (N=20k), with all firing controls live, OOS reproduction, and a
**flat Δ scale trend** (no growth with q). `[VERIFIED-scope — scoped null]`.

## What is NOT settled (the null is bounded, not a closure)
- **Untested finer channels:** `r ≥ 4` Semaev; `m ≥ 4`; other label moduli `ℓ | N`; GLV-mixed features
  `x([λ]P_i + [λ²]P_j)`; a coordinate-pair (x & y) joint statistic; a finer interval-position label.
- **The scale ladder is complete to 2¹⁶** (via the D-LADDER bounded random matcher, exact order matches
  at all four ladder primes); Δ is flat with no scale trend. It does not extend beyond 2¹⁶ here; the
  per-prime exponential-sum cost and the point-count `O(q)` bound the reachable model scale, still ~240
  binary orders short of secp.
- **secp256k1:** zero power (model scale). This result says nothing about the real curve.

## Provenance
Exact int/GF(q) signal path throughout; float only as the `log₂` inside MI, ranked against exact
integer within-stratum permutation counts. Schedule `schedules_v1/schedule_A_joint_v1.json`
(SHA `c533f669…`, anomalous curves excluded both arms). Deviations + gate discharge:
`PREREG_cm_jointset_excess_v3_DEVIATIONS.md`.
