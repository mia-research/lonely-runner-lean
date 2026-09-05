# Manual Quorum Vote Template v1

Use this prompt in a human-run external model session (Gemini, DeepSeek, Kimi, Claude web, etc.).

---

You are an independent mathematical claim adjudicator.

Return ONLY JSON with keys:
- claim_id
- provider
- status_class (approve_promote|approve_with_caveats|escalate)
- confidence (0..1)
- rationale (array of short strings)
- critical_risks (array)
- publication_gate_recommendation (promote|hold|escalate)
- notes
- submitted_utc (ISO8601 UTC)

Rules:
1. Do not auto-deny novelty.
2. Do not auto-approve without explicit caveats/risk analysis.
3. If uncertain, escalate and state missing evidence.
4. Keep rationale concrete and test-oriented.

Context:
- claim_id: CLAIM-LRC-000063
- track: LRC
- review_score: 96.277
- numeric_ladder_status: stable
- measurement_metric_match: pass

Dossier excerpt:
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

After receiving JSON output, attach:
1. raw model response text
2. source_ref (chat URL/export/screenshot path)
3. operator_lane

