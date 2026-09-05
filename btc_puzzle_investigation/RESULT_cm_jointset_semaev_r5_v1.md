# RESULT — S5 (r=5 Semaev): CM-specific joint-set synergy — scoped null across discovery+OOS+ladder

**Grade:** `[VERIFIED-scope — scoped null; S5-multiset within null at all 10 primes across discovery +
confirmation(OOS) + ladder to 2¹⁶; PC-S5 + PC-GRADE fired, PC-PLACEBO silent (the anti-tautology
invariant) at every prime; model scale, ZERO secp power.]`
**Date:** 2026-08-25. **Prereg:** `PREREG_cm_jointset_semaev_r5_v1.md` (runner prints SHA
`a9d8f4482370…`) + deviation **D1** (`..._v1_DEVIATIONS.md`: coincident-x guard is construction hygiene,
NOT trivial-zero removal — corrected for odd r=5). **Runner:** `cm_jointset_semaev_r5_v1.py`
(new primitive `semaev_s5`; imports `cm_jointset_ho_v1` + `model_curve_infra_v1`; `check_no_float.sh`
exits 0). **Extends:** `RESULT_cm_jointset_excess_v3` (r=3) and `RESULT_cm_jointset_higherorder_v1`
(r=4) to the r=5 PURE-Semaev channel.

**MODEL SCALE — ZERO power against secp256k1** (q ∈ {541,…,65539} ≪ 2¹⁶). Measures a MECHANISM only.
No ECDLP / extraction / security claim. A null is a bounded magnitude with power + scope, never a closure.

---

## Object
`Ψ₅ = χ₃(S₅(x₁,…,x₅))` vs `J = (Σd_i) mod 3`, m=5 independent small-interval scalars, conditioned on the
**symmetric multiset stratum** `(n₀,n₁,n₂)` = counts of `χ₃(x_i)` (21 estimable strata). `S₅ =
Res_X(S₄(x₁,x₂,x₃,X), S₃(x₄,x₅,X))` as a 6×6 Sylvester determinant, exact over GF(q) via Lagrange
interpolation of the citation-verified `semaev_s4`. Verdict `Δ = Î(CM) − Î(non-CM)`.

## The multiset coarsening (the novel frame element) — verified sound
The full ordered stratum `Φ^pt(5) = 3⁵ = 243` is unestimable at feasible N (the S-C5 wall). The primary
uses the **multiset** stratum (21 strata), which is information-equivalent for the true synergy: since
`Ψ₅` and `J` are both symmetric and the `(x_i,d_i)` pairs are exchangeable, the multiset is a sufficient
statistic and `Î(Ψ₅;J | ordered) = Î(Ψ₅;J | multiset)` in the population. **Empirically confirmed:**
the registered `PC-PLACEBO` control (`Ψ_pp = Σχ₃(x_i) mod 3`, a per-point-symmetric aggregate) returns
`mi = 0.000000, p = 1.0` at ALL 10 primes — the multiset stratum removes the per-point χ₃-marginal
completely, exactly as the sufficiency argument requires.

## Instrument is LIVE (controls, CM q=541)
- **PC-S5** (mixture, resample d₅ until Ψ₅==J, distinct-x): fires monotone `mi = 0.056 → 0.102 → 0.182
  → 0.601` across ρ = 0/0.15/0.30/0.60, p at the floor from ρ=0.15, distinct_planted=3.
- **PC-GRADE**: fires monotone (mix 0→0.1→0.25: p 0.197 → 0.0075 → 0.0025).
- **PC-PLACEBO**: silent (p=1.0) — required must-NOT-fire control (above).

## Result — S5-multiset CM within-null p and Δ = Î(CM) − Î(non-CM)

**Discovery (N=5000):**
| q | CM p | Δ |
|---|---|---|
| 541 | 0.110 | −0.0012 |
| 571 | 0.149 | +0.0001 |
| 577 | 0.548 | −0.0024 |

**Confirmation (OOS, N=20000):**
| q | CM p | Δ |
|---|---|---|
| 2029 | 0.969 | −0.0012 |
| 2053 | 0.540 | −0.0011 |
| 2089 | 0.434 | −0.0001 |

**Ladder (N=5000, to 2¹⁶):**
| q | CM p | Δ |
|---|---|---|
| 1033 | 0.660 | −0.0023 |
| 4111 | 0.664 | −0.0033 |
| 16417 | 0.654 | −0.0052 |
| 65539 | 0.703 | −0.0038 |

- **CM within null at all 10 primes** (every p ≫ 0.01). **Δ ≤ 0 everywhere** (CM never exceeds non-CM;
  on the ladder Δ is uniformly negative and flat — no upward scale trend to 2¹⁶). PC-PLACEBO silent at
  all 10. The lone `nonCM q=2053 p=0.0193` is a wrong-arm, non-reproducing marginal (noise).
- **Power (per §5, conservative):** `MI_min ≈ 6.2×10⁻³` (N=5k) / `1.5×10⁻³` (N=20k) for the 21-stratum
  multiset primary; every `|Δ| < MI_min`.

## Verdict
No CM-specific joint-set synergy in the **r=5 pure-Semaev** channel at model scale (q ≲ 2¹⁶, m=5), across
discovery + OOS + ladder, at the tabulated power, with PC-S5+PC-GRADE fired and PC-PLACEBO silent. A
BOUNDED MAGNITUDE, NOT a closure. This completes the Semaev-order sweep **r=3 (v3) → r=4 (HO) → r=5**,
all scoped nulls; and the m-order sweep on CM joint-set synergy up to m=5.

## Gate status
- **`semaev_s5` exactness KAT — PASSED (mechanical, self-auditable):** 80/80 true 5-relations vanish;
  4/283 random distinct-x vanish (generic-nonzero). Guard confirmed to remove only construction-
  degenerate builds (D1). `[VERIFIED — KAT + artifact]`.
- **D1 correction (recorded):** coincident-x does NOT force `S₅=0` for odd r=5 (4/198 ≈ random rate) —
  the guard is construction hygiene (x₄=x₅ zeros S₃'s leading coeff), not trivial-zero removal.
- **`citation-verifier` on the r=5 extraneous-factor question — OWED** before any S5 *positive* promotes
  (moot for this null; the S₄ base is `[CITED-verified]`; the r=5 recursion inherits Semaev Thm 1 / K-Y
  Prop 2.1 but the deg-4⊗deg-2 resultant's exactness at r=5 + the odd-vs-even coincident-x distinction
  should be confirmed).
- **Second independent `experiment-designer` read of the S5 prereg — OWED** before any Δ promotes (the
  multiset matched-null adequacy is the flagged highest-risk frame item; moot for this null).

## What is NOT settled (untested channels)
- **Ordered-243 frontier co-arm** (S5-ordered): registered but NOT run here (the multiset primary is the
  headline); available as a VOID-gated robustness check.
- **joint-μ₆ label; r ≥ 6.** All model-scale; zero secp power regardless.

## Provenance
Exact int/GF(q) signal path (curve arithmetic, `χ₃`, `S₃`, `S₄`, the S₅ 6×6 Sylvester determinant via
Lagrange interpolation with modular inverse, multiset counts, labels, permutation counts). Float only in
the MI log₂, ranked against exact integer within-stratum permutation counts (`# noqa: float`). Curve
schedule reused from `schedules_v1/schedule_A_joint_v1.json` (SHA c533f669…). Coincident-x guard
(== distinct-scalar in-interval) in `draw_sets` + plants, applied identically to both arms. Seed 20260821.
Runner + logs archived.
