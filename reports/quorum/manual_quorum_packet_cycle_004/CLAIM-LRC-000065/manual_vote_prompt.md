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
- claim_id: CLAIM-LRC-000065
- track: LRC
- review_score: 94.274
- numeric_ladder_status: stable
- measurement_metric_match: pass

Dossier excerpt:
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

After receiving JSON output, attach:
1. raw model response text
2. source_ref (chat URL/export/screenshot path)
3. operator_lane

