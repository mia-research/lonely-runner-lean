---
name: math-notation-measurement-audit
description: Audit mathematical notation consistency and metric-to-claim alignment across seeded claims or claim registries. Use when validating that experiments measure the same object described in proofs, and when detecting symbol drift before claim promotion.
---

# Math Notation Measurement Audit

Run this skill before proof promotion and before final manuscript synthesis.

## Workflow
1. Prepare an input CSV with claim text fields.
2. Run the audit script to detect notation drift and metric mismatch.
3. Route flagged claims to Notation Auditor and Measurement Auditor queues.
4. Block `A-Validated` promotion on `fail` findings.

## Expected Input Columns
At least one of these text columns should exist:
- `short_statement`
- `claim_text`
- `metric_definition`
- `experiment_metric`
- `notes`
- `filename` (fallback)

## Quick Start
```bash
python3 scripts/audit_notation_measurement.py \
  --input "/Users/trentpalelei/Desktop/Math Ex/registry/claim_seed_queue.csv" \
  --output "/Users/trentpalelei/Desktop/Math Ex/reports/notation_measurement_audit_cycle002.csv"
```

## Rules
1. Treat metric mismatch as blocking.
2. Treat notation mismatch as blocking unless explicitly resolved.
3. Escalate numeric precision concerns to the numeric stability skill.

## References
- For checks and reason codes, read `references/audit_rules.md`.
