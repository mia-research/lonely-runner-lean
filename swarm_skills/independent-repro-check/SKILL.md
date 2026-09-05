---
name: independent-repro-check
description: Independently reproduce promoted experiment outputs and compare expected vs reproduced artifacts with explicit tolerances. Use before claim promotion to A-level or publication gate decisions.
---

# Independent Repro Check

Run this skill after a claim is promoted and before final acceptance.

## Workflow
1. Generate expected artifact from original run.
2. Re-run independently in a separate environment/session.
3. Compare expected vs reproduced artifact.
4. Emit `match|partial|fail` decision with discrepancy summary.

## Supported Artifact Types
- CSV (numeric comparison by column)
- JSON (nested numeric comparison)

## Quick Start
```bash
python3 scripts/repro_compare.py \
  --expected /tmp/expected.csv \
  --actual /tmp/reproduced.csv \
  --output /tmp/repro_report.json
```

## Rules
1. Treat `partial` and `fail` as blocking for A-level promotion.
2. Preserve tolerance settings in output report.
3. Always record compared artifact paths.

## References
- For status policy, read `references/repro_policy.md`.
