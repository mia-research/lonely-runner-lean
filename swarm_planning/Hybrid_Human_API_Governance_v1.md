# Hybrid Human + API Governance v1

Date: 2026-02-26  
Scope: LRC swarm execution under quota/API constraints  
Home: `/Users/trentpalelei/Desktop/Math Ex`

## Objective
Keep research velocity high while preserving auditability and policy safety when provider quotas or credentials block automation.

## Core Principle
Human agents are first-class swarm agents.  
If automated API routing is blocked, humans can run external model votes manually and feed structured outputs back into the pipeline.

## Execution Modes
1. `API_Automated`
- Coordinator routes tasks to provider APIs/CLIs.
- Best for repeatability and throughput.

2. `Human_Delegated`
- Human runs model in provider web UI or desktop app using approved prompt packet.
- Human returns structured vote artifact.
- Coordinator validates format and merges into quorum artifacts.

3. `Hybrid`
- One vote from automated local route (for example Codex live).
- One vote from human-delegated external provider (for example Gemini/Kimi/DeepSeek/Claude web).
- Counts as cross-provider quorum only if providers are distinct and both votes are complete.

## Roles
1. `Coordinator (Codex thin manager)`
- Routes tasks.
- Enforces gate logic.
- Writes changelog and run logs.

2. `Human Operator`
- Executes blocked provider tasks manually.
- Preserves raw outputs and timestamps.
- Does not edit claim evidence silently.

3. `Verifier`
- Confirms vote schema, claim ID match, and provider identity.
- Rejects malformed or ambiguous votes.

## Security and Compliance
1. Do not store passwords in workspace files.
2. Prefer API keys for automation.
3. Use OAuth/session flows for interactive human use only.
4. Rotate/revoke exposed tokens immediately.
5. Do not share single account credentials across multiple people.
6. Respect provider usage caps and terms.

## Quorum Gate Policy
A claim passes strict publication quorum only if all are true:
1. Two independent votes exist.
2. Providers are distinct.
3. Both votes include required fields.
4. No unresolved critical theorem/measurement blockers remain.

Status mapping:
1. `executed_live` = strict gate satisfied.
2. `executed_live_same_provider` = partial only, not strict gate.
3. `blocked_provider_auth` = provider unavailable/auth blocked/quota blocked.

## Manual Vote Minimum Schema
Required fields per vote artifact:
1. `claim_id`
2. `provider`
3. `status_class` (`approve_promote|approve_with_caveats|escalate`)
4. `confidence` (`0..1`)
5. `rationale` (array or pipe-separated list)
6. `critical_risks` (array or pipe-separated list)
7. `publication_gate_recommendation` (`promote|hold|escalate`)
8. `notes`
9. `submitted_utc`
10. `operator_lane`
11. `source_ref` (chat URL, export id, or screenshot path)

## Anti-Slop Controls
1. Require claim ID echo in prompt and in returned vote.
2. Reject votes missing explicit risk statements.
3. Reject votes with empty rationale for non-trivial claims.
4. Keep raw model text as an immutable attachment.
5. If schema parse fails, mark `invalid_vote` and rerun.

## Runtime Routing Rule (Current)
1. Use Codex live for first vote.
2. If Claude CLI is quota-blocked, assign second vote to human-delegated Gemini/Kimi/DeepSeek/Claude web.
3. Once provider reset occurs, rerun blocked automated lane and replace provisional human lane only if needed.

## Changelog Requirements
Every cycle append:
1. `provider_quota_state`
2. `lane_active`
3. `deferred_due_to_quota`
4. `reroute_count`
5. `blocked_reason`
6. `manual_votes_used` (count)
7. `external_quorum_complete` (per claim)

## Immediate Next-Step Procedure
1. Build manual quorum packet for currently blocked claims.
2. Human operator runs second-provider votes with fixed prompt template.
3. Verifier checks schema and claim/provider consistency.
4. Merge votes into quorum artifacts and recompute gate status.
5. Promote only claims with strict gate satisfied.

## 8AM Reset Procedure
1. Re-test blocked provider lane.
2. Re-run live quorum on blocked claims only.
3. Replace provisional manual votes with live votes if available.
4. Keep both records for audit; mark superseded artifacts explicitly.

## Publication Safety Reminder
Novel claims are allowed to survive as `U-Unresolved Frontier` when evidence is incomplete.  
Do not auto-deny. Do not auto-promote.
