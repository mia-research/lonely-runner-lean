# Publication Bar Checklist v1 (Strict)

A document is not preprint-ready until every required item is satisfied.

## A) Claim Integrity
1. All central claims are `A-Validated` or explicitly designated `U-Unresolved Frontier`.
2. No central result depends on hidden assumptions.
3. Every theorem-level statement maps to a dependency graph.
4. Every core claim has traceable portfolio provenance (track and source artifacts).

## B) Mathematical Rigor
1. Definitions are stable and non-circular.
2. Notation is globally consistent.
3. Key proof steps are explicit and locally checkable.
4. Boundary cases and domain restrictions are stated.

## C) Computational Rigor
1. Each computational claim includes script ID and commit hash or immutable script checksum.
2. Seed policy is documented.
3. Input data provenance is documented.
4. Output artifacts are linked.
5. Re-run instructions succeed on local environment.

## D) Numerical Integrity (Floating-Point Skepticism)
1. Core quantitative claims pass precision ladder checks.
2. Exact or interval arithmetic cross-check is used where feasible.
3. Perturbation sensitivity window is reported.
4. Any `precision_sensitive` or `unstable` result is not promoted to `A-Validated`.

## E) Adversarial Validation
1. Counterexample search executed for each core claim.
2. Failed attacks are logged (negative evidence).
3. Surviving vulnerabilities are listed as open risks.

## F) External Grounding
1. Closest related work identified and cited.
2. Similar and competing claims are compared fairly.
3. Novelty scope is stated conservatively.

## G) Writing and Transparency
1. Proven facts, conjectures, and heuristics are separated.
2. Limitations section is explicit.
3. Failure modes and non-results are included.
4. Changelog is complete and append-only.

## H) Portfolio Gate
1. Phase 0 categorization exit gate was satisfied before deep-track validation.
2. Non-primary tracks were not silently dropped during development.
3. Deferred and frontier items are explicitly labeled and tracked.

## I) Release Decision
1. Coordinator signs release note.
2. Risk summary is attached.
3. Final status is one of:
- `release-now`
- `release-with-frontier-labels`
- `hold-for-validation`

