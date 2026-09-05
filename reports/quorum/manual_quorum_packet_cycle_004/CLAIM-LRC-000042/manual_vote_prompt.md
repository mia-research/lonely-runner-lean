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
- claim_id: CLAIM-LRC-000042
- track: LRC
- review_score: 98.272
- numeric_ladder_status: stable
- measurement_metric_match: pass

Dossier excerpt:
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

After receiving JSON output, attach:
1. raw model response text
2. source_ref (chat URL/export/screenshot path)
3. operator_lane

