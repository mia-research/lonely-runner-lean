# Model Routing Matrix v1

Date: 2026-02-25
Scope: Planning only
Home: `/Users/trentpalelei/Desktop/Math Ex`

## 1) Objective
Prevent coordinator credit burn by enforcing thin-manager delegation and cost-aware routing.

## 2) Account Lane Topology
Use two parallel account lanes for resilience and quota balancing.

1. `Lane_A`
- Claude: Pro
- ChatGPT: Paid
- Gemini: Family access
- Kimi: Free
- DeepSeek: Free

2. `Lane_B`
- Claude: Pro
- ChatGPT: Free (if enabled)
- Gemini: Family access
- Kimi: Free
- DeepSeek: Free

Identity mapping rule:
- Lane-to-email mapping is stored outside this workspace in your secure credential manager.
- Do not store passwords in project files.
- Use API keys/session auth only.

## 3) Hard Routing Policies
1. Coordinator is routing-only; no bulk worker execution.
2. Local Python is default for parsing, transforms, and experiments.
3. Premium models are reserved for high-impact adjudication and final synthesis.
4. Two-model quorum is required only for promoted/high-impact claims.

## 4) Task-to-Model Routing Matrix

| Task | Primary | Secondary | Fallback | Notes |
|---|---|---|---|---|
| Cycle manager/orchestration | Codex (thin) | DeepSeek | Kimi | Keep manager under token cap |
| Corpus metadata extraction | Local Python | Local shell tools | None | No LLM needed by default |
| Bulk claim extraction (first pass) | Kimi | DeepSeek | ChatGPT free | High volume, low cost |
| Track classification | Kimi | DeepSeek | ChatGPT free | Route low confidence to deferred/frontier |
| Notation consistency pass | Claude | ChatGPT | DeepSeek | Medium token load |
| Proof-structure formalization | ChatGPT paid | Claude Pro | Gemini | Use on shortlisted claims only |
| Adversarial refutation | DeepSeek | ChatGPT paid | Claude Pro | Independent attack channel |
| Numeric stability interpretation | Local Python + SymPy/mpmath | ChatGPT free summary | DeepSeek summary | Computation stays local |
| Independent reproduction check | Local Python (separate run) | Local Python (second environment) | None | No shared run-state |
| Ideation branch | Gemini | ChatGPT free | Kimi | Keep separate from validation channel |
| High-impact adjudication | Claude Pro + ChatGPT paid | Claude Pro + Gemini | ChatGPT paid + DeepSeek | Must be two-model quorum |
| Manuscript drafting | Claude Pro | ChatGPT paid | Gemini | Final fact-check pass required |

## 5) Budget Envelope Defaults (Per Cycle)
1. Manager cap: 15 percent of cycle tokens.
2. Premium-model cap (Claude Pro + ChatGPT paid combined): 35 percent.
3. Budget-worker cap (Kimi + DeepSeek + ChatGPT free): 50 percent.
4. Local Python and shell work: default first whenever feasible.

## 6) Quota and Failover Rules
1. If any provider reaches 80 percent of quota, stop assigning non-critical tasks to it.
2. If provider is unavailable, shift to next fallback in matrix.
3. If both premium providers are constrained, defer high-impact adjudication and continue queue prep.
4. Always log reroute events in changelog.

## 7) Lane Assignment Pattern
1. `Lane_A` default: high-impact adjudication and final synthesis.
2. `Lane_B` default: bulk extraction/classification/refutation queue.
3. Swap lanes weekly to avoid single-lane burnout.

## 8) Stop Conditions
Stop current cycle when any occurs:
1. Manager exceeds 15 percent token cap.
2. Provider credits below safety threshold for assigned lane.
3. Governance breach: manager performed worker task without emergency flag.

## 9) Required Cycle Budget Report
Include:
1. `manager_token_share`
2. `provider_quota_state`
3. `reroutes`
4. `deferred_due_to_quota`
5. `lane_active`

## 10) Implementation Note
Reference this file from coordinator prompts as routing authority:
- `Model_Routing_Matrix_v1.md`
- `Delegation_Monitoring_Playbook_v1.md`

