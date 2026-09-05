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
- claim_id: CLAIM-LRC-000043
- track: LRC
- review_score: 100.227
- numeric_ladder_status: stable
- measurement_metric_match: pass

Dossier excerpt:
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

After receiving JSON output, attach:
1. raw model response text
2. source_ref (chat URL/export/screenshot path)
3. operator_lane

