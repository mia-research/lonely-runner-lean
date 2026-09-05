# Cycle 002 Evidence Book

Generated: 2026-02-25T23:58:54Z
Primary track: LRC

## Included Artifacts
- Ranking: /Users/trentpalelei/Desktop/Math Ex/reports/cycle_002_numeric_review_ranking.md
- Dossier index: /Users/trentpalelei/Desktop/Math Ex/reports/dossiers/cycle_002_promoted_index.md
- Measurement-fix execution: /Users/trentpalelei/Desktop/Math Ex/reports/cycle_002_measurement_fix_execution.md

## Ranking Snapshot

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

## Measurement-Fix Snapshot

# Measurement Fix Execution Summary

Generated: 2026-02-25T23:51:25Z
Tickets executed: 4

## Status Counts
- resolved_pass: 4

## Ticket Results

| Ticket | Claim | Status | Metric Match Out | Checks (pass/fail) | Notes |
|---|---|---|---|---|---|
| MFIX-LRC-0001 | CLAIM-LRC-000032 | resolved_pass | pass | 25/0 | canonical_success_rate_table_extracted |
| MFIX-LRC-0002 | CLAIM-LRC-000049 | resolved_pass | pass | 11/0 | residue_consistency_invariants_valid |
| MFIX-LRC-0003 | CLAIM-LRC-000050 | resolved_pass | pass | 11/0 | residue_consistency_invariants_valid |
| MFIX-LRC-0004 | CLAIM-LRC-000051 | resolved_pass | pass | 7/0 | statistical_schema_canonicalized |

## Claim Dossiers (Rank Order)

---

## Dossier File: 01_CLAIM-LRC-000055.md

# Claim Dossier: CLAIM-LRC-000055

## Metadata
- rank: 1
- review_score: 102.223
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: lrc_validation_large_1759238706040.csv
- source_path: /Users/trentpalelei/Downloads/lrc_validation_large_1759238706040.csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: test_type,n,phi_n,prime,family,base,delta,alpha,ratio,seed,boundary_count,isolation_count,unique_phases,phi_match,runtime_ms,first_isolation arithmetic_varied,5,4,YES,arithmetic,0.3,0.02,0,0,0,28,12,4,YES,0.10,9.999999999999991 arithmetic_v
- assumptions: explicit assumptions pending extraction review
- excerpt: test_type,n,phi_n,prime,family,base,delta,alpha,ratio,seed,boundary_count,isolation_count,unique_phases,phi_match,runtime_ms,first_isolation arithmetic_varied,5,4,YES,arithmetic,0.3,0.02,0,0,0,28,12,4,YES,0.10,9.999999999999991 arithmetic_varied,5,4,YES,arithmetic,0.3,0.04,0,0,0,28,12,4,YES,0.00,4.999999999999996 arith

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 3.452160046289e-15
- max_rel_decimal128_vs_mpmath: 8.639082042811e-32
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 4400550
- tokens_extracted: 4400550
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000055

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 12

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 02_CLAIM-LRC-000052.md

# Claim Dossier: CLAIM-LRC-000052

## Metadata
- rank: 2
- review_score: 102.214
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: lrc_validation_data_2025-09-23T11-19-31-619Z.csv
- source_path: /Users/trentpalelei/Downloads/lrc_validation_data_2025-09-23T11-19-31-619Z.csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: test_type,n,phi_n,prime,family,seed,boundary_count,isolation_count,unique_phases,phi_match,runtime_ms,first_isolation arithmetic_baseline,5,4,YES,arithmetic,1,30,12,4,YES,0.30,2.000000 arithmetic_baseline,5,4,YES,arithmetic,2,30,12,4,YES,0.
- assumptions: explicit assumptions pending extraction review
- excerpt: test_type,n,phi_n,prime,family,seed,boundary_count,isolation_count,unique_phases,phi_match,runtime_ms,first_isolation arithmetic_baseline,5,4,YES,arithmetic,1,30,12,4,YES,0.30,2.000000 arithmetic_baseline,5,4,YES,arithmetic,2,30,12,4,YES,0.20,2.000000 arithmetic_baseline,5,4,YES,arithmetic,3,30,12,4,YES,0.10,2.000000 a

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 5.334259598839e-15
- max_rel_decimal128_vs_mpmath: 1.528807921989e-32
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 54967
- tokens_extracted: 54967
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000052

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 8

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 03_CLAIM-LRC-000053.md

# Claim Dossier: CLAIM-LRC-000053

## Metadata
- rank: 3
- review_score: 102.201
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: lrc_validation_large_1759238333891.csv
- source_path: /Users/trentpalelei/Downloads/lrc_validation_large_1759238333891.csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: test_type,n,phi_n,prime,family,base,delta,alpha,ratio,seed,boundary_count,isolation_count,unique_phases,phi_match,runtime_ms,first_isolation arithmetic_varied,5,4,YES,arithmetic,0.3,0.02,0,0,0,28,12,4,YES,0.30,9.999999999999991 arithmetic_v
- assumptions: explicit assumptions pending extraction review
- excerpt: test_type,n,phi_n,prime,family,base,delta,alpha,ratio,seed,boundary_count,isolation_count,unique_phases,phi_match,runtime_ms,first_isolation arithmetic_varied,5,4,YES,arithmetic,0.3,0.02,0,0,0,28,12,4,YES,0.30,9.999999999999991 arithmetic_varied,5,4,YES,arithmetic,0.3,0.04,0,0,0,28,12,4,YES,0.10,4.999999999999996 arith

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 9.396461823534e-15
- max_rel_decimal128_vs_mpmath: 1.439036645487e-32
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 69718
- tokens_extracted: 69718
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000053

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 12

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 04_CLAIM-LRC-000054.md

# Claim Dossier: CLAIM-LRC-000054

## Metadata
- rank: 4
- review_score: 102.201
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: lrc_validation_large_1759238362541.csv
- source_path: /Users/trentpalelei/Downloads/lrc_validation_large_1759238362541.csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: test_type,n,phi_n,prime,family,base,delta,alpha,ratio,seed,boundary_count,isolation_count,unique_phases,phi_match,runtime_ms,first_isolation arithmetic_varied,5,4,YES,arithmetic,0.3,0.02,0,0,0,28,12,4,YES,0.00,9.999999999999991 arithmetic_v
- assumptions: explicit assumptions pending extraction review
- excerpt: test_type,n,phi_n,prime,family,base,delta,alpha,ratio,seed,boundary_count,isolation_count,unique_phases,phi_match,runtime_ms,first_isolation arithmetic_varied,5,4,YES,arithmetic,0.3,0.02,0,0,0,28,12,4,YES,0.00,9.999999999999991 arithmetic_varied,5,4,YES,arithmetic,0.3,0.04,0,0,0,28,12,4,YES,0.00,4.999999999999996 arith

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 9.515720220921e-15
- max_rel_decimal128_vs_mpmath: 5.27711896192e-33
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 221100
- tokens_extracted: 221100
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000054

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 12

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 05_CLAIM-LRC-000020.md

# Claim Dossier: CLAIM-LRC-000020

## Metadata
- rank: 5
- review_score: 102.177
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: lrc_boundary_set_report_2025-09-23T08-04-30.txt
- source_path: /Users/trentpalelei/Downloads/lrc_boundary_set_report_2025-09-23T08-04-30.txt
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: CLEAN BOUNDARY SET LRC ANALYSIS =============================== ARITHMETIC PROGRESSION BASELINE n | φ(n) | Speeds | Boundary | Isolation | Clustering | LRC Satisfied | Expected Phases ---|------|--------|----------|-----------|------------|
- assumptions: explicit assumptions pending extraction review
- excerpt: CLEAN BOUNDARY SET LRC ANALYSIS =============================== ARITHMETIC PROGRESSION BASELINE n | φ(n) | Speeds | Boundary | Isolation | Clustering | LRC Satisfied | Expected Phases ---|------|--------|----------|-----------|------------|---------------|---------------- 5 | 4 | [1,1.1,1.2...] | 57 | 24 | 1 | YES | 4

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 2.902023387558e-16
- max_rel_decimal128_vs_mpmath: 9.264062755926e-34
- metric_match: pass
- notation_match: pass
- float_risk: low

## Numeric Repro Details
- usable_values: 101
- tokens_extracted: 101
- extraction_method: regex_text
- extraction_truncated: False
- stable_threshold: 1e-08
- sensitive_threshold: 1e-05
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000020

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_sanity_replay
- triage_numeric_literals_detected: 2

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 06_CLAIM-LRC-000032.md

# Claim Dossier: CLAIM-LRC-000032

## Metadata
- rank: 6
- review_score: 100.69
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: lrc_statistical_validation.txt
- source_path: /Users/trentpalelei/Downloads/lrc_statistical_validation.txt
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: LRC STATISTICAL VALIDATION REPORT ===================================== Generated: 2025-09-23T01:09:32.192Z Sample size: 100 per type Significance level: α = 0.0125 (Bonferroni corrected) SUCCESS RATES BY CONFIGURATION TYPE (n=8): =========
- assumptions: explicit assumptions pending extraction review
- excerpt: LRC STATISTICAL VALIDATION REPORT ===================================== Generated: 2025-09-23T01:09:32.192Z Sample size: 100 per type Significance level: α = 0.0125 (Bonferroni corrected) SUCCESS RATES BY CONFIGURATION TYPE (n=8): ========================================== Type\Horizon T=10 T=50 T=100 T=500 T=1000 T=50

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 1.551221805285e-16
- max_rel_decimal128_vs_mpmath: 1.694023205552e-34
- metric_match: pass
- notation_match: pass
- float_risk: low

## Numeric Repro Details
- usable_values: 201
- tokens_extracted: 201
- extraction_method: regex_text
- extraction_truncated: False
- stable_threshold: 1e-08
- sensitive_threshold: 1e-05
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000032

## Measurement + Notation
- measurement_metric_match: partial
- measurement_notation_match: pass
- measurement_required_fixes: align_metric_definition
- triage_precision_plan: binary64_sanity_replay
- triage_numeric_literals_detected: 4

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 07_CLAIM-LRC-000045.md

# Claim Dossier: CLAIM-LRC-000045

## Metadata
- rank: 7
- review_score: 100.27
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: lrc_honest_validation_1759237637956.csv
- source_path: /Users/trentpalelei/Downloads/lrc_honest_validation_1759237637956.csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: test_type,n,phi_n,prime,base,delta,alpha,seed,boundary_count,isolation_count,unique_phases,phi_match,runtime_ms,first_isolation arithmetic_varied,5,4,YES,1,0.05,0,0,28,12,4,YES,0.20,4.000000 arithmetic_varied,5,4,YES,1,0.08,0,0,28,12,4,YES,
- assumptions: explicit assumptions pending extraction review
- excerpt: test_type,n,phi_n,prime,base,delta,alpha,seed,boundary_count,isolation_count,unique_phases,phi_match,runtime_ms,first_isolation arithmetic_varied,5,4,YES,1,0.05,0,0,28,12,4,YES,0.20,4.000000 arithmetic_varied,5,4,YES,1,0.08,0,0,28,12,4,YES,0.00,2.500000 arithmetic_varied,5,4,YES,1,0.1,0,0,30,12,4,YES,0.00,2.000000 arit

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 4.06633573995e-16
- max_rel_decimal128_vs_mpmath: 5.750804805759e-34
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 1410
- tokens_extracted: 1410
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000045

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 13

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 08_CLAIM-LRC-000047.md

# Claim Dossier: CLAIM-LRC-000047

## Metadata
- rank: 8
- review_score: 100.251
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: lrc_quick_validation_replicated.csv
- source_path: /Users/trentpalelei/Downloads/lrc_quick_validation_replicated.csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: generator,seed_id,n,triplets,plane_zero_frac,plane_max_bin_frac,lattice_rate_tol0,lattice_rate_tol1e3,eff_rank_lag3,sv_max,sv2,boundary_hits_eps1e-3,fragility_eps_star,fragility_base_rate,fragility_end_rate,elapsed_sec RANDU,1,200000,199998
- assumptions: explicit assumptions pending extraction review
- excerpt: generator,seed_id,n,triplets,plane_zero_frac,plane_max_bin_frac,lattice_rate_tol0,lattice_rate_tol1e3,eff_rank_lag3,sv_max,sv2,boundary_hits_eps1e-3,fragility_eps_star,fragility_base_rate,fragility_end_rate,elapsed_sec RANDU,1,200000,199998,0.0,5.000050000500005e-06,0.0,0.0,4,129.45642293534468,129.1590462425297,773,in

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 9.74048224719e-16
- max_rel_decimal128_vs_mpmath: 2.077689946611e-33
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 1445
- tokens_extracted: 1445
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000047

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 7

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 09_CLAIM-LRC-000046.md

# Claim Dossier: CLAIM-LRC-000046

## Metadata
- rank: 9
- review_score: 100.248
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: lrc_honest_validation_1759237834647.csv
- source_path: /Users/trentpalelei/Downloads/lrc_honest_validation_1759237834647.csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: test_type,n,phi_n,prime,base,delta,alpha,seed,boundary_count,isolation_count,unique_phases,phi_match,runtime_ms,first_isolation arithmetic_varied,5,4,YES,0.5,0.03,0,0,28,12,4,YES,0.10,6.666667 arithmetic_varied,5,4,YES,0.5,0.05,0,0,30,12,4,
- assumptions: explicit assumptions pending extraction review
- excerpt: test_type,n,phi_n,prime,base,delta,alpha,seed,boundary_count,isolation_count,unique_phases,phi_match,runtime_ms,first_isolation arithmetic_varied,5,4,YES,0.5,0.03,0,0,28,12,4,YES,0.10,6.666667 arithmetic_varied,5,4,YES,0.5,0.05,0,0,30,12,4,YES,0.10,4.000000 arithmetic_varied,5,4,YES,0.5,0.07,0,0,28,12,4,YES,0.10,2.8571

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 1.110627865757e-15
- max_rel_decimal128_vs_mpmath: 6.185809038465e-34
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 6720
- tokens_extracted: 6720
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000046

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 18

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 10_CLAIM-LRC-000041.md

# Claim Dossier: CLAIM-LRC-000041

## Metadata
- rank: 10
- review_score: 100.232
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: lrc_individual_isolation_1759267335152.csv
- source_path: /Users/trentpalelei/Downloads/lrc_individual_isolation_1759267335152.csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: family,n,phi_n,seed,horizon,boundary_count,runners_isolated,complete_success,avg_first_isolation,runtime_ms arithmetic,6,2,0,1000,3801,6,YES,1.666666666666665,1.80 arithmetic,6,2,0,1000,3801,6,YES,1.666666666666665,1.90 arithmetic,6,2,0,100
- assumptions: explicit assumptions pending extraction review
- excerpt: family,n,phi_n,seed,horizon,boundary_count,runners_isolated,complete_success,avg_first_isolation,runtime_ms arithmetic,6,2,0,1000,3801,6,YES,1.666666666666665,1.80 arithmetic,6,2,0,1000,3801,6,YES,1.666666666666665,1.90 arithmetic,6,2,0,1000,4401,6,YES,1.666666666666665,1.40 arithmetic,6,2,0,1000,4401,6,YES,1.666666666

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 2.263703258654e-15
- max_rel_decimal128_vs_mpmath: 1.139282179925e-32
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 9600
- tokens_extracted: 9600
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000041

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 11

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 11_CLAIM-LRC-000043.md

# Claim Dossier: CLAIM-LRC-000043

## Metadata
- rank: 11
- review_score: 100.227
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: lrc_efficiency_runtime_validation (1).csv
- source_path: /Users/trentpalelei/Downloads/lrc_efficiency_runtime_validation (1).csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: family,n,seed,prime,phi,phi_over_n,boundary_count,isolation_count,detected_phases,efficiency,runtime_ms,phi_match arithmetic,5,0,true,4,0.800000,100016,18012,1,0.180091,40.70,false arithmetic,5,1,true,4,0.800000,100018,18036,3,0.180328,23.6
- assumptions: explicit assumptions pending extraction review
- excerpt: family,n,seed,prime,phi,phi_over_n,boundary_count,isolation_count,detected_phases,efficiency,runtime_ms,phi_match arithmetic,5,0,true,4,0.800000,100016,18012,1,0.180091,40.70,false arithmetic,5,1,true,4,0.800000,100018,18036,3,0.180328,23.60,true arithmetic,5,2,true,4,0.800000,100013,18012,1,0.180097,25.90,false arithm

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 2.836580199696e-15
- max_rel_decimal128_vs_mpmath: 7.715594354474e-33
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 3456
- tokens_extracted: 3456
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000043

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 15

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 12_CLAIM-LRC-000044.md

# Claim Dossier: CLAIM-LRC-000044

## Metadata
- rank: 12
- review_score: 100.227
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: lrc_efficiency_runtime_validation.csv
- source_path: /Users/trentpalelei/Downloads/lrc_efficiency_runtime_validation.csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: family,n,seed,prime,phi,phi_over_n,boundary_count,isolation_count,detected_phases,efficiency,runtime_ms,phi_match arithmetic,5,0,true,4,0.800000,100016,18012,1,0.180091,40.70,false arithmetic,5,1,true,4,0.800000,100018,18036,3,0.180328,23.6
- assumptions: explicit assumptions pending extraction review
- excerpt: family,n,seed,prime,phi,phi_over_n,boundary_count,isolation_count,detected_phases,efficiency,runtime_ms,phi_match arithmetic,5,0,true,4,0.800000,100016,18012,1,0.180091,40.70,false arithmetic,5,1,true,4,0.800000,100018,18036,3,0.180328,23.60,true arithmetic,5,2,true,4,0.800000,100013,18012,1,0.180097,25.90,false arithm

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 2.836580199696e-15
- max_rel_decimal128_vs_mpmath: 7.715594354474e-33
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 3456
- tokens_extracted: 3456
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000044

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 15

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 13_CLAIM-LRC-000056.md

# Claim Dossier: CLAIM-LRC-000056

## Metadata
- rank: 13
- review_score: 100.182
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: lrc_validation_large_1759239075705.csv
- source_path: /Users/trentpalelei/Downloads/lrc_validation_large_1759239075705.csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: test_type,n,phi_n,prime,family,base,delta,alpha,ratio,seed,boundary_count,isolation_count,unique_phases,phi_match,runtime_ms,first_isolation arithmetic_varied,5,4,YES,arithmetic,0.3,0.02,0,0,0,28,12,4,YES,0.00,9.999999999999991 arithmetic_v
- assumptions: explicit assumptions pending extraction review
- excerpt: test_type,n,phi_n,prime,family,base,delta,alpha,ratio,seed,boundary_count,isolation_count,unique_phases,phi_match,runtime_ms,first_isolation arithmetic_varied,5,4,YES,arithmetic,0.3,0.02,0,0,0,28,12,4,YES,0.00,9.999999999999991 arithmetic_varied,5,4,YES,arithmetic,0.3,0.04,0,0,0,28,12,4,YES,0.00,4.999999999999996 arith

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 2.340998792916e-14
- max_rel_decimal128_vs_mpmath: 1.9916445453e-32
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 2201100
- tokens_extracted: 2201100
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000056

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 12

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 14_CLAIM-LRC-000057.md

# Claim Dossier: CLAIM-LRC-000057

## Metadata
- rank: 14
- review_score: 98.276
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: lrc_validation_results.csv
- source_path: /Users/trentpalelei/Downloads/lrc_validation_results.csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: Case ID,Boundary Isolated,Brute Isolated,Boundary Time,Brute Time,Speedup,Agreement 1,8,8,13.200000017881393,48.69999998807907,3.6893939334929975,true 2,8,8,6.200000017881393,30.799999982118607,4.967741918272332,true 3,8,8,5.300000011920929
- assumptions: explicit assumptions pending extraction review
- excerpt: Case ID,Boundary Isolated,Brute Isolated,Boundary Time,Brute Time,Speedup,Agreement 1,8,8,13.200000017881393,48.69999998807907,3.6893939334929975,true 2,8,8,6.200000017881393,30.799999982118607,4.967741918272332,true 3,8,8,5.300000011920929,28.19999998807907,5.320754702764289,true 4,8,8,3.5,27.200000017881393,7.7714285

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 3.009180255409e-16
- max_rel_decimal128_vs_mpmath: 2.445356081537e-33
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 600
- tokens_extracted: 600
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000057

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 19

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 15_CLAIM-LRC-000042.md

# Claim Dossier: CLAIM-LRC-000042

## Metadata
- rank: 15
- review_score: 98.272
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: LRC_Quick_Validation__methods_focus_.csv
- source_path: /Users/trentpalelei/Downloads/LRC_Quick_Validation__methods_focus_.csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: generator,n,triplets,plane_zero_frac,plane_max_bin_frac,lattice_rate_tol0,lattice_rate_tol1e3,eff_rank_lag3,sv_max,sv2,boundary_hits_eps1e-3,fragility_eps_star,fragility_base_rate,fragility_end_rate,elapsed_sec,plane_top_bins_preview RANDU,
- assumptions: explicit assumptions pending extraction review
- excerpt: generator,n,triplets,plane_zero_frac,plane_max_bin_frac,lattice_rate_tol0,lattice_rate_tol1e3,eff_rank_lag3,sv_max,sv2,boundary_hits_eps1e-3,fragility_eps_star,fragility_base_rate,fragility_end_rate,elapsed_sec,plane_top_bins_preview RANDU,200000,199998,0.0,5.000050000500005e-06,0.0,0.0,4,129.45642293534468,129.1590462

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 3.554504011286e-16
- max_rel_decimal128_vs_mpmath: 2.031432744137e-33
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 118
- tokens_extracted: 118
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000042

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 7

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 16_CLAIM-LRC-000048.md

# Claim Dossier: CLAIM-LRC-000048

## Metadata
- rank: 16
- review_score: 98.272
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: lrc_quick_validation_run.csv
- source_path: /Users/trentpalelei/Downloads/lrc_quick_validation_run.csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: generator,n,triplets,plane_zero_frac,plane_max_bin_frac,lattice_rate_tol0,lattice_rate_tol1e3,eff_rank_lag3,sv_max,sv2,boundary_hits_eps1e-3,fragility_eps_star,fragility_base_rate,fragility_end_rate,elapsed_sec,plane_top_bins_preview RANDU,
- assumptions: explicit assumptions pending extraction review
- excerpt: generator,n,triplets,plane_zero_frac,plane_max_bin_frac,lattice_rate_tol0,lattice_rate_tol1e3,eff_rank_lag3,sv_max,sv2,boundary_hits_eps1e-3,fragility_eps_star,fragility_base_rate,fragility_end_rate,elapsed_sec,plane_top_bins_preview RANDU,200000,199998,0.0,5.000050000500005e-06,0.0,0.0,4,129.45642293534468,129.1590462

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 3.554504011286e-16
- max_rel_decimal128_vs_mpmath: 2.031432744137e-33
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 118
- tokens_extracted: 118
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000048

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 7

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 17_CLAIM-LRC-000038.md

# Claim Dossier: CLAIM-LRC-000038

## Metadata
- rank: 17
- review_score: 98.26
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: Boundary-probe_isolation___sample_rows.csv
- source_path: /Users/trentpalelei/Downloads/Boundary-probe_isolation___sample_rows.csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: family,config_id,runner,n,T,detected,witness_time,boundary_time,probe_side,speeds transcendental,trans_0,1,10,100.0,True,3.146238076843286,3.1462370768432857,right,"[1.141420999839335, 1.2469799997571693, 1.3039630008400291, 1.2025860009852
- assumptions: explicit assumptions pending extraction review
- excerpt: family,config_id,runner,n,T,detected,witness_time,boundary_time,probe_side,speeds transcendental,trans_0,1,10,100.0,True,3.146238076843286,3.1462370768432857,right,"[1.141420999839335, 1.2469799997571693, 1.3039630008400291, 1.2025860009852634, 1.173205000077592, 1.2617989993711172, 1.2718280001001092, 1.31415900002102

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 6.26e-16
- max_rel_decimal128_vs_mpmath: 2.412741646308e-33
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 450
- tokens_extracted: 450
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000038

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 18

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 18_CLAIM-LRC-000049.md

# Claim Dossier: CLAIM-LRC-000049

## Metadata
- rank: 18
- review_score: 96.787
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: lrc_rigorous_validation_2025-09-24T12-45-35.json
- source_path: /Users/trentpalelei/Downloads/lrc_rigorous_validation_2025-09-24T12-45-35.json
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: { "tests": [ { "name": "coprime_residue_verification", "results": [ { "n": 3, "phi_n": 2, "expectedResidues": [ 1, 2 ], "detectedResidues": [ 1, 2 ], "perfectMatch": true, "maxError": 1.1102230246251565e-15, "avgError": 4.440892098500626e-1
- assumptions: explicit assumptions pending extraction review
- excerpt: { "tests": [ { "name": "coprime_residue_verification", "results": [ { "n": 3, "phi_n": 2, "expectedResidues": [ 1, 2 ], "detectedResidues": [ 1, 2 ], "perfectMatch": true, "maxError": 1.1102230246251565e-15, "avgError": 4.440892098500626e-16, "gridUniform": true, "isolationCount": 18 }, { "n": 4, "phi_n": 2, "expectedR

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 1.780556770795e-16
- max_rel_decimal128_vs_mpmath: 2.772749765563e-34
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 520
- tokens_extracted: 520
- extraction_method: regex_text
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000049

## Measurement + Notation
- measurement_metric_match: partial
- measurement_notation_match: pass
- measurement_required_fixes: align_metric_definition
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 8

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 19_CLAIM-LRC-000050.md

# Claim Dossier: CLAIM-LRC-000050

## Metadata
- rank: 19
- review_score: 96.766
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: lrc_rigorous_validation_2025-09-24T12-47-24.json
- source_path: /Users/trentpalelei/Downloads/lrc_rigorous_validation_2025-09-24T12-47-24.json
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: { "tests": [ { "name": "coprime_residue_verification", "results": [ { "n": 3, "phi_n": 2, "expectedResidues": [ 1, 2 ], "detectedResidues": [ 1, 2 ], "perfectMatch": true, "maxError": 1.1102230246251565e-15, "avgError": 4.440892098500626e-1
- assumptions: explicit assumptions pending extraction review
- excerpt: { "tests": [ { "name": "coprime_residue_verification", "results": [ { "n": 3, "phi_n": 2, "expectedResidues": [ 1, 2 ], "detectedResidues": [ 1, 2 ], "perfectMatch": true, "maxError": 1.1102230246251565e-15, "avgError": 4.440892098500626e-16, "gridUniform": true, "isolationCount": 18 }, { "n": 4, "phi_n": 2, "expectedR

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 4.888364258418e-16
- max_rel_decimal128_vs_mpmath: 1.277659313389e-33
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 520
- tokens_extracted: 520
- extraction_method: regex_text
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000050

## Measurement + Notation
- measurement_metric_match: partial
- measurement_notation_match: pass
- measurement_required_fixes: align_metric_definition
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 8

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 20_CLAIM-LRC-000058.md

# Claim Dossier: CLAIM-LRC-000058

## Metadata
- rank: 20
- review_score: 96.277
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: Detector___per-family_summary.csv
- source_path: /Users/trentpalelei/Downloads/Detector___per-family_summary.csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: family,configs,success_rate,median_first_time,q25_first_time,q75_first_time,median_boundary_count exact_arithmetic,30,1.0,1.4087301587301586,1.1799719887955182,1.6666666666666663,314.5 fibonacci_ratios,30,1.0,0.2916666666666667,0.2425,0.347
- assumptions: explicit assumptions pending extraction review
- excerpt: family,configs,success_rate,median_first_time,q25_first_time,q75_first_time,median_boundary_count exact_arithmetic,30,1.0,1.4087301587301586,1.1799719887955182,1.6666666666666663,314.5 fibonacci_ratios,30,1.0,0.2916666666666667,0.2425,0.34750000000000003,1287.0 harmonic_series,30,1.0,1.1,0.42500000000000004,2.000000000

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 2.893847498596e-16
- max_rel_decimal128_vs_mpmath: 1.522700642965e-34
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 30
- tokens_extracted: 30
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000058

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 23

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 21_CLAIM-LRC-000063.md

# Claim Dossier: CLAIM-LRC-000063

## Metadata
- rank: 21
- review_score: 96.277
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: detector_summary_by_family.csv
- source_path: /Users/trentpalelei/Downloads/detector_summary_by_family.csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: family,configs,success_rate,median_first_time,q25_first_time,q75_first_time,median_boundary_count exact_arithmetic,30,1.0,1.4087301587301586,1.1799719887955182,1.6666666666666663,314.5 fibonacci_ratios,30,1.0,0.2916666666666667,0.2425,0.347
- assumptions: explicit assumptions pending extraction review
- excerpt: family,configs,success_rate,median_first_time,q25_first_time,q75_first_time,median_boundary_count exact_arithmetic,30,1.0,1.4087301587301586,1.1799719887955182,1.6666666666666663,314.5 fibonacci_ratios,30,1.0,0.2916666666666667,0.2425,0.34750000000000003,1287.0 harmonic_series,30,1.0,1.1,0.42500000000000004,2.000000000

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 2.893847498596e-16
- max_rel_decimal128_vs_mpmath: 1.522700642965e-34
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 30
- tokens_extracted: 30
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000063

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 23

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 22_CLAIM-LRC-000051.md

# Claim Dossier: CLAIM-LRC-000051

## Metadata
- rank: 22
- review_score: 94.784
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: lrc_statistical_validation_2025-09-23T11-05-33-344Z.csv
- source_path: /Users/trentpalelei/Downloads/lrc_statistical_validation_2025-09-23T11-05-33-344Z.csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: test_name,statistic,value,p_value,effect_size,confidence_interval,interpretation,sample_size phi_correlation,pearson_r,0.9995,0.000000,0.9995,"[0.899, 1.099]",highly_significant,16 performance_improvement,welch_t_test,18.3513,<0.001,3.6703,
- assumptions: explicit assumptions pending extraction review
- excerpt: test_name,statistic,value,p_value,effect_size,confidence_interval,interpretation,sample_size phi_correlation,pearson_r,0.9995,0.000000,0.9995,"[0.899, 1.099]",highly_significant,16 performance_improvement,welch_t_test,18.3513,<0.001,3.6703,speedup_4.88x,very_large_effect,100 success_rate,wilson_ci_95,100.00,N/A,N/A,"[9

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 2.06925622485e-16
- max_rel_decimal128_vs_mpmath: 1.456515398845e-36
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 25
- tokens_extracted: 25
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000051

## Measurement + Notation
- measurement_metric_match: partial
- measurement_notation_match: pass
- measurement_required_fixes: align_metric_definition
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 17

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 23_CLAIM-LRC-000059.md

# Claim Dossier: CLAIM-LRC-000059

## Metadata
- rank: 23
- review_score: 94.304
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: Detector___per-n_summary.csv
- source_path: /Users/trentpalelei/Downloads/Detector___per-n_summary.csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: n,configs,success_rate,median_first_time,median_boundary_count 4,50,1.0,1.3523391812865497,432.0 5,50,1.0,1.0818713450292399,664.0 6,50,1.0,0.7874434423697448,1004.0
- assumptions: explicit assumptions pending extraction review
- excerpt: n,configs,success_rate,median_first_time,median_boundary_count 4,50,1.0,1.3523391812865497,432.0 5,50,1.0,1.0818713450292399,664.0 6,50,1.0,0.7874434423697448,1004.0

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 8.416281112969e-17
- max_rel_decimal128_vs_mpmath: 4.296768881121e-34
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 15
- tokens_extracted: 15
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000059

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 18

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 24_CLAIM-LRC-000064.md

# Claim Dossier: CLAIM-LRC-000064

## Metadata
- rank: 24
- review_score: 94.304
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: detector_summary_by_n.csv
- source_path: /Users/trentpalelei/Downloads/detector_summary_by_n.csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: n,configs,success_rate,median_first_time,median_boundary_count 4,50,1.0,1.3523391812865497,432.0 5,50,1.0,1.0818713450292399,664.0 6,50,1.0,0.7874434423697448,1004.0
- assumptions: explicit assumptions pending extraction review
- excerpt: n,configs,success_rate,median_first_time,median_boundary_count 4,50,1.0,1.3523391812865497,432.0 5,50,1.0,1.0818713450292399,664.0 6,50,1.0,0.7874434423697448,1004.0

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 8.416281112969e-17
- max_rel_decimal128_vs_mpmath: 4.296768881121e-34
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 15
- tokens_extracted: 15
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000064

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 18

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 25_CLAIM-LRC-000060.md

# Claim Dossier: CLAIM-LRC-000060

## Metadata
- rank: 25
- review_score: 94.284
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: boundary_fragility_summary.csv
- source_path: /Users/trentpalelei/Downloads/boundary_fragility_summary.csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: name,n_words,triplets,plane_onrate_baseline,boundary_fragility_epsilon,torus_boundary_hits,gen_time_s RANDU,400000,399998,2.5000125000625003e-06,0.0,12496,0.08470130199975756 PCG64,400000,399998,2.5000125000625003e-06,0.0,51930,0.0016772940
- assumptions: explicit assumptions pending extraction review
- excerpt: name,n_words,triplets,plane_onrate_baseline,boundary_fragility_epsilon,torus_boundary_hits,gen_time_s RANDU,400000,399998,2.5000125000625003e-06,0.0,12496,0.08470130199975756 PCG64,400000,399998,2.5000125000625003e-06,0.0,51930,0.0016772940002738324

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 2.066813582698e-16
- max_rel_decimal128_vs_mpmath: 2.403234151195e-34
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 12
- tokens_extracted: 12
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000060

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 16

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 26_CLAIM-LRC-000065.md

# Claim Dossier: CLAIM-LRC-000065

## Metadata
- rank: 26
- review_score: 94.274
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: pcg64_boundary_fragility.json
- source_path: /Users/trentpalelei/Downloads/pcg64_boundary_fragility.json
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: { "name": "PCG64", "n_words": 400000, "triplets": 399998, "plane_onrate_baseline": 2.5000125000625003e-06, "boundary_fragility_epsilon": 0.0, "torus_boundary_hits": 51930, "gen_time_s": 0.0016772940002738324 }
- assumptions: explicit assumptions pending extraction review
- excerpt: { "name": "PCG64", "n_words": 400000, "triplets": 399998, "plane_onrate_baseline": 2.5000125000625003e-06, "boundary_fragility_epsilon": 0.0, "torus_boundary_hits": 51930, "gen_time_s": 0.0016772940002738324 }

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 3.2603502105e-16
- max_rel_decimal128_vs_mpmath: 1.716754582918e-34
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 6
- tokens_extracted: 6
- extraction_method: regex_text
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000065

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 8

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

---

## Dossier File: 27_CLAIM-LRC-000062.md

# Claim Dossier: CLAIM-LRC-000062

## Metadata
- rank: 27
- review_score: 91.984
- tier: A_repro_verified_strong
- recommendation: promote_to_claim_dossier
- priority_note: P3_context_or_auxiliary
- source_file: boundary_set_vs_coarse_midpoint_n10.csv
- source_path: /Users/trentpalelei/Downloads/boundary_set_vs_coarse_midpoint_n10.csv
- generated_utc: 2026-02-25T23:53:25Z

## Claim Statement
- claim_type: empirical_claim
- short_statement: config_id,runner,n,T,threshold,boundary_detect,boundary_witness_time,coarse_detect,coarse_witness_time,miss_due_to_coarse,speeds 0,1,10,100.0,0.1,True,7.637065517933746,True,6.75,False,"[1.2469800001523585, 1.141420999480008, 1.069315000375
- assumptions: explicit assumptions pending extraction review
- excerpt: config_id,runner,n,T,threshold,boundary_detect,boundary_witness_time,coarse_detect,coarse_witness_time,miss_due_to_coarse,speeds 0,1,10,100.0,0.1,True,7.637065517933746,True,6.75,False,"[1.2469800001523585, 1.141420999480008, 1.0693150003752256, 1.2617990004702822, 1.2025859990244823, 1.22360699934891, 1.30396300006392

## Validation Snapshot
- adjudication_decision: needs_human_review
- adjudication_score: 0.480
- queue_status: executed
- ladder_status: stable
- max_rel_float64_vs_mpmath: 2.045174182592e-10
- max_rel_decimal128_vs_mpmath: 2.433268471902e-32
- metric_match: pass
- notation_match: pass
- float_risk: medium

## Numeric Repro Details
- usable_values: 20400
- tokens_extracted: 20400
- extraction_method: csv_cells_plus_regex
- extraction_truncated: False
- stable_threshold: 1e-09
- sensitive_threshold: 1e-06
- artifact_dir: /Users/trentpalelei/Desktop/Math Ex/reports/repro/cycle_002/CLAIM-LRC-000062

## Measurement + Notation
- measurement_metric_match: pass
- measurement_notation_match: pass
- measurement_required_fixes: 
- triage_precision_plan: binary64_vs_decimal128
- triage_numeric_literals_detected: 18

## Verdict
- repro_final_status: stable
- dossier_readiness: ready

## Required Next Actions
- Promote to claim dossier review board and attach reproducibility packet.

