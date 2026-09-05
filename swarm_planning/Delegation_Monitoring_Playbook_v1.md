# Delegation Monitoring Playbook v1

Date: 2026-02-25
Scope: Operational monitoring during execution cycles

## 1) Purpose
Detect and stop failure modes where the manager over-executes, token spend spikes, or provider quotas bottleneck the swarm.

## 2) Per-Cycle Monitors
Track these every cycle:
1. `manager_token_share`
2. `worker_token_share`
3. `premium_token_share`
4. `lane_active`
5. `provider_quota_state`
6. `reroute_count`
7. `governance_breach_count`
8. `deferred_due_to_quota`

## 3) Thresholds
1. `manager_token_share > 0.15` -> stop manager, reroute pending tasks.
2. `premium_token_share > 0.35` -> block non-critical premium calls.
3. any provider `quota > 0.80` -> reroute non-critical tasks.
4. any governance breach -> mark cycle as `invalid_for_promotion` until reviewed.

## 4) Cycle Health Labels
1. `green`:
- manager <= 0.15
- premium <= 0.35
- no governance breaches
2. `amber`:
- one threshold warning but resolved by reroute
3. `red`:
- threshold exceeded without remediation, or governance breach unresolved

## 5) Required Artifacts
1. `logs/cycle_monitor_log.csv`
2. `logs/run_log.jsonl`
3. cycle summary note with remediation actions

## 6) Remediation Actions
1. Switch active lane (`Lane_A` <-> `Lane_B`).
2. Lower premium allocation for next cycle.
3. Increase local-Python preprocessing before LLM calls.
4. Reduce high-impact adjudication batch size.

