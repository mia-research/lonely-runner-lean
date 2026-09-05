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
- claim_id: CLAIM-LRC-000049
- track: LRC
- review_score: 96.787
- numeric_ladder_status: stable
- measurement_metric_match: pass

Dossier excerpt:
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

After receiving JSON output, attach:
1. raw model response text
2. source_ref (chat URL/export/screenshot path)
3. operator_lane

