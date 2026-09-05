# Swarm Skills Pack v1

Location: `/Users/trentpalelei/Desktop/Math Ex/swarm_skills`
Date: 2026-02-25

## Skills Included
1. `lrc-claim-catalog`
- Purpose: Seed deterministic claim queues from track registry data.
- Main script: `scripts/seed_claim_queue.py`

2. `math-notation-measurement-audit`
- Purpose: Audit notation drift and metric-to-claim mismatch.
- Main script: `scripts/audit_notation_measurement.py`

3. `numeric-stability-audit`
- Purpose: Run precision ladder comparison and stability labeling.
- Main script: `scripts/precision_ladder_check.py`

4. `independent-repro-check`
- Purpose: Compare expected vs reproduced outputs and emit match/partial/fail.
- Main script: `scripts/repro_compare.py`

5. `swarm-budget-governor`
- Purpose: Enforce cycle token/governance thresholds from monitor logs.
- Main script: `scripts/check_cycle_budget.py`

## Operational Sequence (Phase 1)
1. Seed queue:
```bash
python3 lrc-claim-catalog/scripts/seed_claim_queue.py --track-map "/Users/trentpalelei/Desktop/Math Ex/registry/track_map.csv" --output "/Users/trentpalelei/Desktop/Math Ex/registry/claim_seed_queue.csv" --track LRC --batch-size 80
```
2. Run notation + measurement audit:
```bash
python3 math-notation-measurement-audit/scripts/audit_notation_measurement.py --input "/Users/trentpalelei/Desktop/Math Ex/registry/claim_seed_queue.csv" --output "/Users/trentpalelei/Desktop/Math Ex/reports/notation_measurement_audit_cycle002.csv"
```
3. Run numeric stability check on paired outputs:
```bash
python3 numeric-stability-audit/scripts/precision_ladder_check.py --baseline /tmp/baseline.json --high /tmp/high.json --output /tmp/precision_report.csv
```
4. Run independent reproduction compare:
```bash
python3 independent-repro-check/scripts/repro_compare.py --expected /tmp/expected.csv --actual /tmp/actual.csv --output /tmp/repro_report.json
```
5. Run budget governor:
```bash
python3 swarm-budget-governor/scripts/check_cycle_budget.py --monitor-log "/Users/trentpalelei/Desktop/Math Ex/logs/cycle_monitor_log.csv" --output "/Users/trentpalelei/Desktop/Math Ex/reports/cycle_budget_check.json"
```

## Validation Note
Official `quick_validate.py` currently fails in this environment because `PyYAML` is missing. Use local structural checks until dependency is installed.
