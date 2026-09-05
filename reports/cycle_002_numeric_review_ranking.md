# Cycle 002 Numeric Result Review + Ranking

## Core
- numeric_claims_reviewed: 27
- all_precision_ladder_status: stable (27/27)
- max_rel_float64_vs_mpmath: 2.045174182592e-10
- max_rel_decimal128_vs_mpmath: 8.639082042811e-32
- truncated_inputs_at_current_cap: 0
- metric_partial_items: 0

## Tier Counts
- A_repro_verified_strong: 27

## Recommendation Counts
- promote_to_claim_dossier: 27

## Top 12 Ranked

| Rank | Claim | Score | Tier | Recommendation | MaxRel(f64/mp) | Metric | Values |
|---:|---|---:|---|---|---:|---|---:|
| 1 | CLAIM-LRC-000055 | 102.223 | A_repro_verified_strong | promote_to_claim_dossier | 3.452e-15 | pass | 4400550 |
| 2 | CLAIM-LRC-000052 | 102.214 | A_repro_verified_strong | promote_to_claim_dossier | 5.334e-15 | pass | 54967 |
| 3 | CLAIM-LRC-000053 | 102.201 | A_repro_verified_strong | promote_to_claim_dossier | 9.396e-15 | pass | 69718 |
| 4 | CLAIM-LRC-000054 | 102.201 | A_repro_verified_strong | promote_to_claim_dossier | 9.516e-15 | pass | 221100 |
| 5 | CLAIM-LRC-000020 | 102.177 | A_repro_verified_strong | promote_to_claim_dossier | 2.902e-16 | pass | 101 |
| 6 | CLAIM-LRC-000032 | 100.690 | A_repro_verified_strong | promote_to_claim_dossier | 1.551e-16 | pass | 201 |
| 7 | CLAIM-LRC-000045 | 100.270 | A_repro_verified_strong | promote_to_claim_dossier | 4.066e-16 | pass | 1410 |
| 8 | CLAIM-LRC-000047 | 100.251 | A_repro_verified_strong | promote_to_claim_dossier | 9.740e-16 | pass | 1445 |
| 9 | CLAIM-LRC-000046 | 100.248 | A_repro_verified_strong | promote_to_claim_dossier | 1.111e-15 | pass | 6720 |
| 10 | CLAIM-LRC-000041 | 100.232 | A_repro_verified_strong | promote_to_claim_dossier | 2.264e-15 | pass | 9600 |
| 11 | CLAIM-LRC-000043 | 100.227 | A_repro_verified_strong | promote_to_claim_dossier | 2.837e-15 | pass | 3456 |
| 12 | CLAIM-LRC-000044 | 100.227 | A_repro_verified_strong | promote_to_claim_dossier | 2.837e-15 | pass | 3456 |

## Notes
- Ranking combines governance priority, adjudication score, audit quality, float risk, precision deltas, and numeric coverage depth.
- Measurement-fix tickets for previously partial claims are now applied in queue state before this ranking refresh.
