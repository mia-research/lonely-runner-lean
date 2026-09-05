# LRC Swarm Plan v2

Date: 2026-02-25
Status: Active execution (Cycle 002 completed; anti-drift hardening initiated 2026-02-26)
Home: `/Users/trentpalelei/Desktop/Math Ex`
Primary Track: Lonely Runner Conjecture (LRC)
Portfolio Policy: Mandatory multi-track preservation

## 1) Mission
Build a multi-agent research swarm that can:
1. Catalog all research artifacts without discarding uncertain ideas too early.
2. Score validity, novelty, and reproducibility with transparent metrics.
3. Separate open-frontier uncertainty from actual refutation.
4. Drive a rigorous, science-grounded agenda while preserving high-upside ideas.
5. Produce publication-grade outputs with full traceability.

## 2) Governance Fixes (Locked)
1. Canonical coordinator prompt is `Master_Prompt_v1_1.md`.
2. `Master_Prompt_v1.md` is retained only for backward compatibility and marked legacy.
3. Mandatory queue taxonomy for every artifact:
- `track_assigned`
- `deferred_queue`
- `frontier_queue`
4. Classification confidence rule:
- assign to a non-frontier track only if `track_confidence >= 0.65`
- else route to `deferred_queue` or `frontier_queue` with reason code
5. No deep-track validation allowed before Phase 0 exit gate is met.

## 3) Manager Delegation Contract (Hard Rule)
1. Coordinator must not perform worker tasks except emergency fallback.
2. Coordinator output per cycle is limited to:
- routing decisions
- conflict resolution
- gate decisions
- short synthesis
3. Worker tasks must be delegated to named agents.
4. Manager token budget cap per cycle: 15 percent of total cycle tokens.
5. If manager reaches 15 percent before cycle completion:
- pause
- delegate remaining tasks
- emit budget event in changelog
6. Any cycle that violates delegation contract is flagged `governance_breach`.

## 4) Manager and Model Routing Recommendation
To prevent credit exhaustion on one provider:
1. Manager tier (thin orchestration):
- preferred: Codex or low-cost model endpoint
2. Worker tier (task-specialized):
- catalog/classification: Kimi or DeepSeek
- proof structuring and risk review: ChatGPT and/or Claude
- ideation branch: Gemini
- local experiments: Python local (no model calls)
3. Acceptance quorum:
- require two independent models only for promoted/high-impact claims
4. Escalation policy:
- if one provider quota is near limit, auto-reroute non-critical tasks to backup models

## 5) Operating Principles
1. Two-model acceptance quorum for high-impact claims.
2. No auto-denial language; uncertainty must map to explicit missing evidence.
3. Local-first computation for experiments and parsing where possible.
4. Every claim gets a status and a next action.
5. Append-only changelog for all decisions.
6. No-loss intake: no artifact may be dropped without a logged disposition.

## 6) Budget and Rate Governance
1. Define per-cycle budget envelope before starting.
2. Reserve premium-model usage for:
- conflict resolution
- high-impact adjudication
- final synthesis
3. Batch low-risk extraction/classification on cheaper models.
4. Hard stop triggers:
- manager token budget exceeded
- provider credit below safety threshold
- unresolved governance breach
5. Log each stop trigger with remediation action.

## 7) Security and Credential Policy
1. Never share passwords with agents.
2. Use API keys only.
3. Store secrets in Keychain/1Password; inject via env vars at runtime.
4. Keep only non-secret templates/config in project files.

## 8) Swarm Hierarchy (Primary track plus portfolio)

### A. Governance
1. Coordinator (thin manager)
- Routes tasks, enforces gates, resolves agent disagreements.

2. Tracekeeper
- Ensures every decision has prompt hash, model ID, dataset ID, and artifact links.

3. Portfolio Manager
- Maintains active track board and prevents non-LRC topics from being dropped.

4. Evals and Grader Engineer
- Maintains objective scorecards and regression checks across cycles.

5. Budget Governor (new)
- Enforces per-cycle token and provider-credit guardrails.

### B. Intake and Structuring
6. Catalog Agent
- Extracts definitions, lemmas, theorem claims, and experiment claims.

7. Notation Auditor
- Detects symbol drift and definition conflicts.

8. Track Classifier
- Assigns each artifact and claim to a portfolio track with confidence.

### C. Validation and Attack
9. Proof Structurer
- Converts prose arguments into explicit dependency graph.

10. Adversarial Refuter
- Searches for counterexamples and hidden assumptions.

11. Local Python Experimenter
- Runs deterministic tests with fixed seeds and runtime classes.

12. Measurement Auditor
- Verifies tested quantity matches claimed quantity.

13. Numeric Stability Auditor
- Audits floating-point sensitivity, precision drift, and numerical conditioning.

14. Independent Reproducer
- Re-runs accepted experiments independently before status promotion.

### D. Synthesis
15. Ideation Agent (Gemini suggested)
- Proposes next hypotheses constrained by validated evidence.

16. Academic Writer and Compiler
- Produces rigorous manuscript sections and reproducibility appendices.

## 9) Portfolio Track Map (Mandatory)
Every artifact must be mapped into one primary track:
1. `LRC`
2. `RH_LFunctions`
3. `Prime_Systems`
4. `Integer_Dynamics_Kaprekar`
5. `Algebra_Candidates`
6. `Cross_Domain_Methods`
7. `Frontier_Unclassified`

Rule:
- `Frontier_Unclassified` is temporary and must receive a follow-up classification pass.

## 10) Numerical Integrity Policy (Strong Floating-Point Skepticism)
Numerical claims are treated as provisional unless they pass precision stress checks.

Required checks for any quantitative claim:
1. Precision ladder test:
- run at baseline precision
- rerun at higher precision
- confirm qualitative conclusion is unchanged
2. Arithmetic cross-check:
- where feasible, validate with exact (`fractions`/symbolic) or interval arithmetic
3. Perturbation sensitivity:
- small perturbations to inputs, step size, and tolerance
- report stability window
4. Cancellation/conditioning check:
- explicitly check for catastrophic cancellation risk and ill-conditioning
5. Audit outcome labels:
- `stable`
- `precision_sensitive`
- `unstable`

Promotion rule:
- any `precision_sensitive` or `unstable` core result cannot be marked `A-Validated`.

## 11) Claim Scoring Rubric
Score 0-4 each plus confidence [0,1]:
1. Formal correctness evidence
2. Empirical support quality
3. Assumption clarity
4. Reproducibility completeness
5. Novelty plausibility
6. External consistency
7. Notation and measurement integrity
8. Refutation resistance
9. Numerical stability confidence

Statuses:
- `A-Validated`
- `B-Promising`
- `C-Underspecified`
- `D-Refuted`
- `U-Unresolved Frontier`

## 12) Mandatory Phase Workflow (No execution yet)

### Phase 0: Corpus Categorization (Required before any deep-track work)
1. Build corpus manifest for all target folders.
2. Extract lightweight metadata and topic indicators.
3. Assign every artifact to one primary track from Section 9.
4. Route low-confidence items to deferred/frontier queues.
5. Flag novelty candidates and high-risk/high-upside items.
6. Build first portfolio board with queue priorities.

Required Phase 0 outputs:
1. `registry/corpus_manifest.csv`
2. `registry/track_map.csv`
3. `registry/deferred_queue.csv`
4. `registry/frontier_queue.csv`
5. `registry/claim_seed_queue.csv`
6. `reports/phase0_portfolio_summary.md`

Phase 0 exit gate:
1. At least 90 percent of artifacts assigned to non-temporary tracks at confidence >= 0.65.
2. Deferred plus frontier combined at most 10 percent with explicit reason codes.
3. Kaprekar and algebra-candidate watchlists explicitly populated.
4. No unlogged artifacts.

### Phase 1: Primary Track Deepening (LRC first)
1. Run claim extraction and scoring on LRC set.
2. Build dependency graphs and adversarial tests.
3. Run local experiments where needed.
4. Run numeric stability audit on core quantitative claims.
5. Produce LRC risk-ranked agenda.

### Phase 2: Portfolio Rotation (Parallel preservation)
1. Keep minimum capacity for non-LRC tracks.
2. Promote non-LRC high-information candidates into validation queue.
3. Maintain monthly cross-track synthesis report.

Suggested capacity split:
1. 70 percent LRC
2. 30 percent portfolio exploration

## 13) Proposed Folder Layout (under Math Ex)

```text
Math Ex/
  swarm_planning/
    LRC_Swarm_Plan_v2.md
    Master_Prompt_v1.md
    Master_Prompt_v1_1.md
    Publication_Bar_Checklist_v1.md
    agent_prompts/
      Catalog_Agent_Prompt_v1.md
      Refuter_Agent_Prompt_v1.md
      Measurement_Auditor_Prompt_v1.md
      Numeric_Stability_Auditor_Prompt_v1.md
      Independent_Reproducer_Agent_Prompt_v1.md
      Writer_Compiler_Prompt_v1.md
    Model_Routing_Matrix_v1.md
    Model_Routing_Matrix_v1.yaml
    Delegation_Monitoring_Playbook_v1.md
    cycle_monitor_log_template.csv
  registry/
    corpus_manifest.csv
    track_map.csv
    deferred_queue.csv
    frontier_queue.csv
    claim_seed_queue.csv
    claims.csv
    evidence.csv
    notation_map.yaml
  portfolio/
    board.md
    watchlist_kaprekar.md
    watchlist_algebra_candidates.md
  logs/
    run_log.jsonl
  experiments/
    manifests/
    scripts/
    outputs/
  reports/
  papers/
```

## 14) Changelog Standard
Each entry records:
1. Timestamp (ISO8601)
2. Agent role plus model
3. Prompt hash
4. Inputs and outputs artifact IDs
5. Decision delta
6. Seeds, runtime, environment
7. Known failure modes
8. Numerical integrity outcome (`stable|precision_sensitive|unstable` when applicable)
9. Budget event fields (`manager_token_share`, `provider_quota_state`, `stop_trigger`)
10. Monitoring fields (`lane_active`, `reroute_count`, `cycle_health`)

## 15) Skills Backlog to Build
1. Claim extraction
2. Dependency graphing
3. Counterexample search
4. Deterministic experiment orchestration
5. Measurement and notation audit
6. Evidence grading
7. Track classification and portfolio ranking
8. Numeric stability audit
9. Exact/interval arithmetic cross-check
10. Independent reproduction workflow
11. Runtime and feasibility estimation
12. Budget governance and routing
13. Paper compiler

## 16) Quality Gates
A claim cannot reach `A-Validated` unless:
1. Dependency graph has no unresolved critical node.
2. No successful refuter attack in current scope.
3. Reproducible local experiment evidence exists where relevant.
4. Measurement auditor signs off.
5. Numeric stability auditor marks core quantitative evidence as `stable`.
6. Independent reproducer confirms rerun.
7. Tracekeeper confirms complete provenance.

## 17) Immediate Next Planning Outputs
1. Mark `Master_Prompt_v1.md` as legacy and `Master_Prompt_v1_1.md` as canonical.
2. Lock per-agent prompt pack, including numeric stability and independent reproducer prompts.
3. Define Phase 0 classification schema and reason codes.
4. Define Phase 0 portfolio summary template.
5. Lock publication bar checklist.
6. Define budget envelope defaults and model-routing matrix.
7. Set routing authority document: `Model_Routing_Matrix_v1.md`.

## 18) Open Decisions (To confirm before execution)
1. API enablement order.
2. Spend guardrails (soft cap plus hard fail-safe).
3. Folders included in first Phase 0 pass.
4. Publication bar for preprint-ready release.

## 19) Strict Publication Bar (Required)
A manuscript cannot be labeled preprint-ready unless all are true:
1. Core claims are `A-Validated` or explicitly marked `U-Unresolved Frontier`.
2. Every theorem-level claim has a dependency graph with no hidden jumps.
3. All computational claims link to script ID, seed policy, input dataset IDs, and output artifacts.
4. Measurement auditor confirms term and notation consistency across proofs, experiments, and plots.
5. Numeric stability auditor confirms robustness across precision ladder checks.
6. At least one adversarial pass failed to refute each core claim.
7. Related-work checks are recorded with citations for nearest known results.
8. Limitations and failure modes are explicitly stated.
9. Reproducibility appendix is drafted and internally rerunnable.
10. Changelog is complete from intake to manuscript state.
11. Portfolio provenance for manuscript claims is traceable to Phase 0 track assignment.
12. Coordinator signs release note with unresolved risk summary.

## 20) Review Rhythm
1. Weekly 60-minute adjudication: promote and demote claim statuses.
2. Weekly portfolio board refresh: prevent non-LRC drift into neglect.
3. Weekly numerical integrity review for newly promoted claims.
4. Weekly budget-governance review.
5. Monthly publication gate review: decide draft or no-draft.
6. Immediate hotfix review when any foundational claim is refuted.
