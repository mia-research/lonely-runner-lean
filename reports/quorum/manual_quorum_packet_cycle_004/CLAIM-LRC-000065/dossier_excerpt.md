# Dossier Excerpt: CLAIM-LRC-000065

Generated: path-fix-refresh
Source dossier: /Users/trentpalelei/Desktop/Desktop - Trent’s MacBook Pro/Math Ex/reports/dossiers/cycle_002_promoted/26_CLAIM-LRC-000065.md

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
