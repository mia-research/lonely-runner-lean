---
name: numeric-stability-audit
description: Evaluate floating-point robustness for quantitative claims using precision ladder comparisons and sensitivity checks. Use when deciding whether numerical evidence is stable enough for promotion and before any A-level claim status.
---

# Numeric Stability Audit

Run this skill whenever a claim depends on numerical experiments.

## Workflow
1. Produce at least two result files for the same computation:
- baseline precision run
- higher precision run
2. Compare both outputs with the ladder script.
3. Label each claim as `stable`, `precision_sensitive`, or `unstable`.
4. Block promotions on non-stable outcomes.

## Input Format
- JSON files with numeric leaf values (nested dict/list supported).

## Quick Start
```bash
python3 scripts/precision_ladder_check.py \
  --baseline /tmp/baseline.json \
  --high /tmp/high_precision.json \
  --output /tmp/precision_ladder_report.csv
```

## Rules
1. Do not certify by plot shape alone.
2. Require explicit tolerances in every report.
3. Escalate unstable claims to Refuter + Reproducer tracks.

## References
- For thresholds and labels, read `references/stability_thresholds.md`.
