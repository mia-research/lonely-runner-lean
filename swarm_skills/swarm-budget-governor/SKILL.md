---
name: swarm-budget-governor
description: Enforce delegation and budget governance from cycle monitoring logs. Use when validating manager token share, premium usage, provider quota warnings, and deciding reroute or stop actions each cycle.
---

# Swarm Budget Governor

Run this skill every cycle before and after major task batches.

## Workflow
1. Read the latest cycle row from `logs/cycle_monitor_log.csv`.
2. Check manager and premium shares against caps.
3. Check provider quota warnings and governance breach counts.
4. Emit `green|amber|red` health and remediation actions.

## Quick Start
```bash
python3 scripts/check_cycle_budget.py \
  --monitor-log "/Users/trentpalelei/Desktop/Math Ex/logs/cycle_monitor_log.csv" \
  --output "/Users/trentpalelei/Desktop/Math Ex/reports/cycle_002_budget_check.json"
```

## Rules
1. Manager share > cap is a governance breach.
2. Unresolved governance breach forces red status.
3. Premium over-cap blocks non-critical premium calls.

## References
- For thresholds and actions, read `references/budget_policy.md`.
