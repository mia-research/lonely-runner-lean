# `n = 11` AP Proof: Canonical Status Ledger

**Date:** 2026-03-27 (updated; original 2026-03-26)
**Purpose:** Single status source inside `Math Ex` after the static-core extraction.

## Label Meanings

- `proved`
- `invalid as written`
- `superseded`
- `historical`

## Canonical Chain

| Claim / file | Label | Current role |
|---|---|---|
| `lrc_n11_static_core_theorem_v1.md` | `proved` | Authoritative static-front theorem note (static route only). |
| `lrc_n11_universalincompat_v3.md` | `proved` | Canonical `sigma_2 = +1` theorem (Theorem U + Theorem UB). |
| `lrc_n11_lemma_s1_runner2_elimination_v1.md` | `proved` | Canonical runner-2 elimination lemma. |
| `lrc_n11_lemma_s2_proof_v2.md` | `proved` | Canonical `sigma_2 = -1` theorem (Lemma S2, min gap `538/54395`). |
| `lrc_n11_w1_argument_v1.md` | `proved` | W_ref window construction; computational verification 112/112. |
| `lrc_n11_periodicity_lemma_v1.md` | `proved` | Phase-Uniform Theorem U + Corollary W_ref. Closes all Case R> residuals. |

## Non-Canonical / Demoted Files

| Claim / file | Label | Why |
|---|---|---|
| `lrc_n11_slot_economy_theorem_v1.md` | `superseded` | Originally invalid (staircase flaw); now superseded — Route 3 + Corollary W_ref covers all cases without SET. |
| `lrc_n11_lemma_wit_analytic_v1.md` | `superseded` | Originally invalid (large-p inequality false); now superseded — Route 3 + Corollary W_ref covers all cases without WIT. |
| `lrc_n11_proof_complete_v1.md` | `superseded` | Its complete-proof status depends on the invalid SET route. |
| `lrc_n11_ap_paper_v22.md` | `proved` | Canonical clean paper (2026-03-27, 876 lines). Main body: rigorously proved content only. Appendix A: computational corroboration. Appendix B: historical approaches (SET/WIT/ILE). |
| `lrc_n11_ap_paper_v21.md` | `historical` | Full historical record including legacy proof attempts; superseded by v22 as the canonical document. |
| `lrc_n11_ap_paper_v18.md` | `historical` | Retained as a draft, but not a canonical status document. |
| `lrc_n11_ap_paper_v17.md` | `historical` | Retained as a draft, but not a canonical status document. |
| `lrc_n11_boundary_defect_reduction_v1.md` | `historical` | Useful reduction / mechanism memo; no longer a canonical theorem container. |
| `lrc_n11_incompatibility_v1.md` | `historical` | Important seed note, but not part of the canonical dependency chain after extraction. |

## Verification Snapshot

The exact-rational spot checks recorded on 2026-03-26 confirm:

- `86/9`
- `172/81`
- `181/6380`
- `59/9460`
- `103/3850`
- `538/54395`
- `((9/11)^8 - 16/69) < 0`

These checks were run from the audit script
`/Users/trentpalelei/Documents/Claude Library/lrc_n11_audit_checks_v1.py`.

## Verification Snapshot (2026-03-27 addition)

Computational corroboration of Corollary W_ref:
- **112/112** canonical integer configs `{1,...,9,p10}` for `p10 ∈ {89,...,200}` have witnesses in `W_ref`.
- Script: `tools/lrc_case_r_residual_harness_v1.py`.

## Current Canonical Verdict

**The AP proof for `n = 11` is complete.**

Dependency chain:

```
Theorem U (lrc_n11_universalincompat_v3.md)      →  sigma_2 = +1 closed
Lemma S1 + S2 (s1_runner2_elimination, s2_proof) →  sigma_2 = -1 closed
    Static Core Theorem (static_core_theorem_v1)  →  all 256 sign classes (static front)
Lemma P + Lemma C (periodicity_lemma_v1)          →  cascade is phase-independent
    Corollary W_ref (periodicity_lemma_v1)         →  all Case R> (ratio > 10) closed
```

The proof is now dependency-clean. SET and WIT are superseded (not needed; see above).
