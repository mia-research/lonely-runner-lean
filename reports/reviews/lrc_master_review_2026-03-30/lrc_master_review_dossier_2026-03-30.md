# LRC Master Review and Novelty Audit

Generated: 2026-03-30
Corpus roots: `/Users/trentpalelei/Desktop/Math Ex` and `/Users/trentpalelei/Documents/Claude Library`

Deliverables:
- Source ledger: `/Users/trentpalelei/Desktop/Math Ex/reports/reviews/lrc_master_review_2026-03-30/lrc_master_source_ledger_2026-03-30.csv`
- Discovery ledger: `/Users/trentpalelei/Desktop/Math Ex/reports/reviews/lrc_master_review_2026-03-30/lrc_master_discovery_ledger_2026-03-30.csv`
- Conflict ledger: `/Users/trentpalelei/Desktop/Math Ex/reports/reviews/lrc_master_review_2026-03-30/lrc_master_conflict_ledger_2026-03-30.csv`

## 1. Source Map

- Total inventoried artifacts: **1763**
- Artifacts with duplicate basenames: **611**
- Duplicate classes: identical copies = **84**, divergent forks = **527**

### Bucket counts

| Bucket | Count |
| --- | --- |
| all-n proof/preprint | 52 |
| all-n supporting theorem/memo | 168 |
| claim-validation registry | 11 |
| claim-validation report | 715 |
| coordination/planning | 15 |
| n=11 canon/draft | 103 |
| proof-pack/certifier export | 320 |
| spillover/multidiv | 112 |
| spillover/n11 memo | 137 |
| spillover/n11 route memo | 79 |
| spillover/sv56 | 37 |
| supporting material | 7 |
| tooling | 7 |

### Scope counts

| Scope | Count |
| --- | --- |
| all-n | 210 |
| branch-scoped composite/gap4 | 14 |
| branch-scoped multidiv | 117 |
| branch-scoped prime-power | 41 |
| coordination/tooling | 22 |
| empirical pipeline | 1040 |
| n=11 | 319 |

Key reading of the map:
- `Math Ex` holds the active canonical n=11 chain, the current all-n preprint chain, and the proof-pack / claim-pipeline infrastructure.
- `Claude Library` holds a larger spillover archive of n=11 route memos plus multidiv and SV56 branch material.
- Duplicate basenames occur across the two roots; the source ledger resolves these with duplicate groups and preferred copies.

## 2. Canonical Status

| Scope | Verdict | Support | Preferred source | Notes |
| --- | --- | --- | --- | --- |
| n=11 AP chain | Complete locally | proved/dependency-clean | /Users/trentpalelei/Desktop/Math Ex/lrc_n11_canonical_status_ledger_v2.md | Static front + periodicity/W_ref; SET/WIT explicitly superseded. |
| all-n preprint chain | Full proof claimed locally | proved but packaging-conflicted | /Users/trentpalelei/Desktop/Math Ex/lrc_proof_v7_8_preprint.md | Direct theorem claim exists, but older packet reviews and some status files still conflict. |
| odd prime-power Tier 2 | Closed locally | proved but packaging-conflicted | /Users/trentpalelei/Documents/Claude Library/lrc_prime_power_tier2_closure_v1.md | Later closure text conflicts with the stale v6.3 status ledger. |
| D3 finite-window certification | Certified only | exact certified empirical | /Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_d3_batch_summary_n7n11_v2.md | Strong exact evidence, but not asymptotic theorem closure. |
| multidiv finite-window certification | Certified only | exact certified empirical | /Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_multidiv_batch_summary_n13_d23_f1234_m100_v1.md | Explicitly tagged as finite-window computation only. |
| spillover route memos | Non-canonical | mechanism insight | /Users/trentpalelei/Documents/Claude Library/lrc_n11_outer_confinement_results_v1.md | Useful route compression, but not theorem authority. |

Canonical reading:
- The strongest clean local result is the n=11 AP chain in `Math Ex` after the March 27 extraction.
- The strongest broad claim is the v7.8 all-n preprint, but it sits above older open-status reviews and stale branch ledgers that still need reconciliation.
- Finite certifications remain evidence packs, not theorem closure, unless promoted by a separate analytic writeup.

## 3. Discovery Catalogue

| Claim label | Scope | Support | Novelty verdict | Source of truth |
| --- | --- | --- | --- | --- |
| DISC-N11-AP-COMPLETE | n=11 AP branch | proved/dependency-clean | candidate new theorem-grade result | /Users/trentpalelei/Desktop/Math Ex/lrc_n11_canonical_status_ledger_v2.md |
| DISC-N11-THEOREM-U | n=11 static front | proved/dependency-clean | candidate new theorem-grade result | /Users/trentpalelei/Desktop/Math Ex/lrc_n11_universalincompat_v3.md |
| DISC-N11-S2-PERIODICITY | n=11 static plus residual branch | proved/dependency-clean | candidate new theorem-grade result | /Users/trentpalelei/Desktop/Math Ex/lrc_n11_periodicity_lemma_v1.md |
| DISC-ALLN-THEOREM-A | all-n theorem chain | proved but packaging-conflicted | candidate new theorem-grade result | /Users/trentpalelei/Desktop/Math Ex/lrc_proof_v7_8_preprint.md |
| DISC-ALLN-DROPPED-RUNNER-TARGETING | all-n composite Unit-Complete branch | proved but packaging-conflicted | candidate new theorem-grade result | /Users/trentpalelei/Desktop/Math Ex/lrc_proof_v7_8_preprint.md |
| DISC-ALLN-ODD-PRIME-POWER-TIER2 | branch-scoped prime-power | proved but packaging-conflicted | candidate new theorem-grade result | /Users/trentpalelei/Documents/Claude Library/lrc_prime_power_tier2_closure_v1.md |
| DISC-GAP4-LIPSCHITZ | branch-scoped composite/gap4 | proved but packaging-conflicted | candidate new theorem-grade result | /Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_gap4_complementarity_theorem_track_v1.md |
| DISC-D3-CERT-N7N11 | empirical pipeline / one-divisible finite window | exact certified empirical | not yet novelty-eligible | /Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_d3_batch_summary_n7n11_v2.md |

High-signal discoveries by class:
- Candidate theorem-grade local results: the n=11 AP completion chain, Theorem U, the S2/periodicity closure, the all-n Theorem A claim, dropped-runner targeting, odd prime-power Tier 2, and the proved G4.A Lipschitz lemma.
- Exact-certified but non-theorem results: the D3 finite-window pack and the multidiv finite-window n=13 pack.
- Route-level structural insights: the n=11 actual-state theorem summary, outer-confinement ownership signal, and exact-pair carrier split.

## 4. Novelty Screen

Comparison corpus used for March 30, 2026 novelty calls:
- Classical journal chain already cited locally: Wills 1967, Cusick 1973, Bienia et al. 1998, Bohman-Holzman-Kleitman 2001, Barajas-Serra 2008, Renault 2004, Dubickas 2011, Goncalves-Ramos 2022, Tao 2018.
- Survey baseline: [Perarnau and Serra, *The Lonely Runner Conjecture turns 60*](https://arxiv.org/abs/2409.20160).
- Runner-count preprints verified against arXiv: [Rosenfeld, eight runners](https://arxiv.org/abs/2509.14111), [Rosenfeld, nine runners](https://arxiv.org/abs/2512.01912), and [Trakulthongchai, nine and ten runners](https://arxiv.org/abs/2511.22427).

| Claim label | Support | Novelty verdict | Action |
| --- | --- | --- | --- |
| DISC-N11-AP-COMPLETE | proved/dependency-clean | candidate new theorem-grade result | Keep as the local n=11 source of truth and package for external mathematical audit. |
| DISC-N11-THEOREM-U | proved/dependency-clean | candidate new theorem-grade result | Retain as a named theorem dependency inside the n=11 package. |
| DISC-N11-S2-PERIODICITY | proved/dependency-clean | candidate new theorem-grade result | Keep grouped with the canonical n=11 dependency chain rather than as a standalone novelty claim. |
| DISC-ALLN-THEOREM-A | proved but packaging-conflicted | candidate new theorem-grade result | Require packet-wide reconciliation and external proof checking before presenting as settled beyond the local corpus. |
| DISC-ALLN-DROPPED-RUNNER-TARGETING | proved but packaging-conflicted | candidate new theorem-grade result | Treat as one of the core candidate novel lemmas in any external all-n review. |
| DISC-ALLN-ODD-PRIME-POWER-TIER2 | proved but packaging-conflicted | candidate new theorem-grade result | Update or retire the stale v6.3 status file before promoting this beyond the local corpus. |
| DISC-GAP4-LIPSCHITZ | proved but packaging-conflicted | candidate new theorem-grade result | Separate the proved Lipschitz lemma from the still-open complementarity cap in any external catalogue. |
| DISC-D3-CERT-N7N11 | exact certified empirical | not yet novelty-eligible | Use as corroborating evidence, not as a standalone theorem claim. |
| DISC-MULTIDIV-FW-N13 | exact certified empirical | not yet novelty-eligible | Keep out of the new-knowledge section unless promoted to an analytic theorem. |
| DISC-N11-ACTUAL-STATE-THEOREM | exact certified empirical | candidate new structural insight | Promote only after a dependency-clean proof note exists inside the active n=11 package. |
| DISC-N11-OUTER-CONFINEMENT | mechanism insight | candidate new structural insight | Keep in the mechanism catalogue only; not a publication claim. |
| DISC-N11-EXACT-PAIR-CARRIER-SPLIT | mechanism insight | candidate new structural insight | Retain as a route memo and do not fold into canonical n=11 status. |

Conservative novelty verdicts:
- No locally theorem-grade claim was downgraded to `known in literature` by this baseline.
- Several strong local claims remain only `candidate new theorem-grade result` because the local corpus still contains unresolved packaging or authority conflicts.
- Empirical and route-discovery artifacts stay out of the new-knowledge section unless promoted to dependency-clean theorem text.

## 5. Conflict Register

| Issue | Type | Preferred authority | Resolution |
| --- | --- | --- | --- |
| CONFLICT-N11-001 | true conflict | /Users/trentpalelei/Desktop/Math Ex/lrc_n11_canonical_status_ledger_v2.md | Treat the March 26 ledger/audit as pre-extraction snapshots and use the March 27 v2 ledger plus v22 paper as the local canonical n=11 authority. |
| CONFLICT-N11-002 | true conflict | /Users/trentpalelei/Desktop/Math Ex/lrc_n11_canonical_status_ledger_v2.md | Keep SET/WIT as invalid or superseded historical routes; they no longer control the canonical n=11 proof chain once periodicity/W_ref is accepted. |
| CONFLICT-ALLN-001 | true conflict | /Users/trentpalelei/Desktop/Math Ex/lrc_proof_v7_8_preprint.md | Use v7.8 as the direct all-n theorem claim, but mark it packaging-conflicted until the older open-program review and trackers are reconciled or retired. |
| CONFLICT-ALLN-002 | true conflict | /Users/trentpalelei/Desktop/Math Ex/lrc_proof_v7_8_preprint.md | Treat the v6.3 status file as stale on prime-power Tier 2 and use the later closure memo plus v7.8 theorem chain for the local branch verdict. |
| CONFLICT-ALLN-003 | scope mismatch | /Users/trentpalelei/Desktop/Math Ex/lrc_proof_v7_8_preprint.md | The publication-bar report evaluates claim-pipeline readiness, not the truth of the theorem manuscript; keep both, but do not merge their verdicts. |
| CONFLICT-LIT-001 | true conflict | /Users/trentpalelei/Desktop/Math Ex/lrc_n11_ap_paper_v22.md | Do not use the cycle-003 citation notes as the sole novelty baseline; refresh the literature screen to include the 2025 survey and the 8/9/10 runner arXiv papers. |
| CONFLICT-DUP-001 | true conflict | /Users/trentpalelei/Desktop/Math Ex | Prefer the Math Ex copy when a duplicate basename exists and either matches exactly or has the lower authority rank; treat the Claude Library copy as spillover unless it is the only surviving source. |
| CONFLICT-SCOPE-001 | scope mismatch | /Users/trentpalelei/Desktop/Math Ex/lrc_proof_v7_8_preprint.md | Treat the March 4 gap-status file as a historical phi-target map; the v7.8 preprint changes the primary theorem scope to x_0(E) >= 1 with partial Tier 2 add-ons. |

Conflict pattern summary:
- The sharpest true conflicts are status conflicts: n=11 incomplete vs complete, all-n open vs full-proof claimed, and prime-power Tier 2 open vs closed.
- Several apparent conflicts are really scope conflicts: theorem truth vs governance readiness, or phi-target historical maps vs x_0>=1 theorem claims.
- Duplicate-file conflicts are manageable because the active workspace usually contains either the preferred copy or the later canonical ledger.

## 6. Promotion Queue

### Publication-ready locally
- n=11 AP chain: keep `lrc_n11_canonical_status_ledger_v2.md` and `lrc_n11_ap_paper_v22.md` as the canonical local package.
- Branch theorem candidates worth external review: dropped-runner targeting, odd prime-power Tier 2 closure, and the proved G4.A Lipschitz lemma.

### High-value but unresolved
- v7.8 all-n theorem claim: reconcile against the March 6 project review, stale gap/status files, and publication/governance reports.
- Gap-4 complementarity run cap (`G4.B`) and composite multidiv asymptotic closure remain open targets despite strong certification.
- Spillover n=11 route memos (outer confinement, exact-pair, DRWT/CPOT plans) should remain quarantined unless they re-enter the active canonical chain.

### Demote or archive
- Dynamic SET and WIT closure routes for n=11 should remain archived or clearly marked superseded.
- `lrc_proof_status.md` should be treated as a stale v6.3-era status file, not the current branch authority.
- Cycle-003 citation notes should not be reused as the current novelty baseline without refresh.
- Claude Library duplicate copies should be treated as spillover unless the source ledger marks them as preferred.

