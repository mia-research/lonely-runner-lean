# Lonely Runner research and Lean proofs

This repository contains the Lean development and a source snapshot of the accompanying Math Ex research, updated on **15 October 2026**. The snapshot includes the latest local proofs and Markdown accounts; historical documents retain their original status and dates.

## Start here

- [Latest native eight-runner account, manuscript v25_3](research/docs/n8/MANUSCRIPT_v25_3.md) — a draft; **the eight-runner conjecture remains open**.
- [Manuscript of record, v21](research/docs/n8/MANUSCRIPT_v21.md) — v25_3 explicitly retains v21 as the manuscript of record pending author promotion.
- [Running research log](research/docs/n8/RUNNING_LOG_order8_v1.md) — includes the later E452–E456 findings and corrections that postdate the main draft's E451 account.
- [General-order research notes](research/docs/nN/) — source dates and corrections determine their scope.
- [Seven-runner completion record](research/docs/n7_bs/ROADMAP.md).

## Lean sources

- [Original Lean development](LonelyRunner/LRC/) — small-order proofs, cascade and construction results, and the general-order programme.
- [Fresh native development](LonelyRunnerFresh/Fresh/) — 56 modules in this snapshot, derived independently of the original development's project modules.
- [Fresh framework and open target](LonelyRunnerFresh/Fresh/Framework.lean) — `LonelyRunnerEight` is an owed proposition, not a proved theorem. An equivalence with this proposition does not prove existence.
- [Second-stage residue and cell results](LonelyRunnerFresh/Fresh/SecondStage.lean) — the later formalisation accompanying E453; universal cell existence remains owed.
- [Standalone six-runner Lean source](research/n6_lrc_lean_standalone_v1.lean).

The original development's completion records report axiom-clean integer results `intLRC_three` through `intLRC_seven`. Other modules contain conditional results, specifications, experiments, or unfinished general-order work. Read theorem hypotheses and proof dependencies when interpreting a result. This upload is a source snapshot, not a new certification of every proof or manuscript claim.

## Research documents and experiments

[research/](research/) preserves the parent project's mathematical Markdown, LaTeX, Lean and experiment sources, including earlier attempts and withdrawn drafts. Historical documents are included for provenance and can contain claims superseded by later corrections. The latest draft and running log above identify the current account.

The original repository's [experiments/](experiments/) are preserved separately from the parent project's [research/experiments/](research/experiments/) so versions with the same name are not overwritten. Regenerable build files, binary caches, and large generated datasets are excluded from the new snapshot.

## Checking the sources

The pinned Lean version is in [lean-toolchain](lean-toolchain), and the mathlib dependency is in [lakefile.toml](lakefile.toml). Use explicit module targets or the supplied gates: the default `lake build` target imports only `LonelyRunner.Basic` and does not check the entire LRC development.

The fresh development's [check.sh](LonelyRunnerFresh/check.sh) compiles its modules in dependency order and prints axiom dependencies. It expects the original project's mathlib dependencies to be available. The copied script's repository lookup has been adapted to this repository layout; the mathematical `.lean` files are copied unchanged.

[Snapshot manifest](research/SNAPSHOT_MANIFEST_2026-10-15.tsv) records original source paths, destination paths, and original SHA-256 hashes. The check script's path adaptation is the sole intentional difference from its recorded original source hash.
