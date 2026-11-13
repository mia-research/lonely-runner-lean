# HANDOVER v2 — n=8 campaign, second session — 2026-11-08 09:15 (session closed, ~25% budget remains)

Supersedes `HANDOVER_2026_11_07_WEEKEND_v1.md`. Read `RULES_n8_v5.md` first (rule 20). Log = `RUNNING_LOG_order8_v1.md` (18,481 lines; this session's entry **E834 is APPENDED**, fully audited). Branch `n8-fresh-2026-10-30`. **Nothing committed.** All streams stopped at handover; every open item has a resume brief below.

## The theorem, as it now exists in Lean

`Fresh/FilterAssembly.lean` (946+ lines, compiles, 26+ theorems axiom-clean `[propext, Classical.choice, Quot.sound]`) proves:

```
filterAssembly : CoverData → ClearPointOfCert → OneSidedSound → PairwiseSound
               → OutsideBelow17 → TailBelow17 → LonelyRunnerEight
```

composed with the previously proved `lonelyRunnerEight_of_allLandBelow17`. **The remaining work is exactly the six hypotheses.** Status of each:

| Hypothesis | State | What remains |
|---|---|---|
| `CoverData` M1 side (62,000 boxes) | **PROVED end-to-end** (O1: `cL_one → m1Cond_of_cL → existsGapJ → faceClear → clearPointOfCert → noCarveOfM1`) | M4 side: see C₃ below |
| `ClearPointOfCert` | **PROVED** (same chain) | — |
| `OneSidedSound` | Engine **proved** (`Fresh/SpineSound.lean`: `joinEdge_conflict`, `famRefutes`, `oneSidedSound_at`) | `SpineTotalOneSided` — data-side: lift the artifact's [T] no-exception law over the reals (per box) |
| `PairwiseSound` | Engine **proved** (same file; all 5 boxes pinned with exact integer conflict data, e.g. AP: ρ₂/ρ₆ < 33/103 vs cap 49/17) | `SpineTotalPairwise` — same data-side lift |
| `OutsideBelow17` | 4/4 certificate schemas in Lean (fixed-R₀, window-type, seam-plane, pinch); $[17,23)\cup[25,95)$ exact | `Fresh/BandNoCarve.lean` composition (O3, incomplete — resume brief below); the 4-leaf close of [49,51) as data |
| `TailBelow17` | Empirically 0 residue through ρ₇ < 95; strips ≥ 4 excluded by T2's window walks (level 2–5 all "0 survivors") | **The tail lemma** — T2's strip-class cap derivation, incomplete |

## The weekend's two structural theorems (computationally verified)

1. **Certificate-envelope closure (M2, `m4comp_summary_v1.out`)**: the leaf-certificate type space of the admission DFS is **CLOSED under the comb** — every certificate is a (rank, exit-numerator) pair from a fixed 90-type envelope (rank 2–7 × 8j+1 with entry < 7); 40 types observed; R-keyed forms = the 12 exit numerators 9, 17, 25, …, 97; each leaf's killing bound is one of three schemas (frontier-ceiling `p·B ≤ 7A`, entry-block `hi′_z ≤ A/p`, advance-block `lo′_z ≥ B/p`) — E813's product form. **This proves the certificate census is finite by structure, not by observation** — the "arbitrary → finite" property at the certificate level.
2. **C₃ = the merged U-closure kill** (same file): one exact fixpoint algorithm (states keyed (last-rank, exit-numerator), componentwise-loosest merge, kill iff fixpoint closes with no completion-check pass) replaces **10,211 of the 12,540 per-box DFS trees** (81.4%; chain controls 0/73). Uniform Lean lemma chain named: E810 monotone-chain completeness → ratio-system feasibility → projection → merge monotonicity → kill lemma + compactness. **Stage-1 admission final form: C_L ∨ 36 gap-edge forms ∨ C₃-core (one algorithm) ∨ residual DFS (2,329 trees) ∨ CHAIN.**
3. Residual rule-22'd: 2,329 boxes (18.6%) — the fine-ladder weave (value-consistency across zone levels, lost by componentwise merge; 75% at maxdepth ≥ 15; median 385 leaves vs 34). Characterized, not explained.

## Complete verified-state inventory (all exact; artifacts beside scripts)

- **J2 reduction [T 74,613/74,613, OPEN=0]**: M1 62,000 (C_L closed form + 36 gap-edge forms) + M4 12,540 (DFS; compressed per above) + 73 chain boxes. Instrument regression-validated bit-for-bit.
- **Stage 2**: 68 one-sided (implication form, `j2_cycle_v6`); 5 two-sided under the raw-edge law [T 2,522,259/0, `j2_cycle_v12`]; collapse corrected by review — every leaf reduces to a single true-forcing bound (63/63 sets, 41–64 distinct; 798,656 re-verified pairs, `review_target3_singletons.out` — artifactized, 907.9 s); kill-form census (48 direct-2-cycle / 9 node-0 / 5 i<j) — `review_*.out`.
- **Outside**: no carve of [1,7] for ρ₇ ∈ **[17,23) ∪ [25,95)** — fixed-R₀ certifier (`frontier_box_dfs_v1.c`, usage `lo hi Dmax [leaves]`; **use the 256-cap binary for ρ₇ ≥ 85** — the fe[64] array provably overflows at 85 [T 9/9, `taildeep_fecheck_v1.out`]; 256-cap source: the four array-cap lines in that file) → window types (`frontier_window_cert_v1.py`) → seam-plane splits (h₁ = ρ₇−7ρ₅, h₂ = 3ρ₆−5ρ₄) → **pinch certificates at tangency planes** (h₃ = 25ρ₇−89ρ₅; R\* = 25/ρ₅ = 89/ρ₇ clear on the plane [T 509/509]; parity refutation proves h₃ is NOT a seam cycle [T 0, `tail_h3_cycles_v1.out`]). (23,25) = X24 carve band, all carves land W₁ < 17. Tie planes: census at [49,51) = P1: 7ρ₅−9ρ₄, P2: ρ₇−7ρ₆ (E830-form); NO planes needed above 51 (all bands 0 leaves at D=64).
- **Cross-order**: ladder k=2..9 (regression-validated at k=8; `experiments/nn_schema/schema_sweep_v1.py`); n9 complete: 186 chains / 0 joints / all one-sided / 18,977 wide BUDGET residue; two-sided regime unique to k=8's five boxes; anchor law: ownership is the general law (k=4: 414/414 owned, 83% first-setter — `anchor_own_v6.out`), opener-identification is order-8 (`landing_is_opener_exit`).
- **Adversarial review**: both flagged upstream inputs SOUND (proved + 10,500-system brute force, `review_target12_fast3.out`); the collapse review (`review_target3_singletons.out`); h₃ pinch independently confirmed.

## Lean files (this campaign; all compile, all axiom-clean, verify with REAL exit codes)

`Fresh/KTaxonomy.lean` · `Fresh/FilterSkeleton.lean` · `Fresh/CarveExclusionCerts.lean` (schemas a–d; section (e) superseded) · `Fresh/PinchCert.lean` (13 theorems, parametric box schema) · `Fresh/SpineSound.lean` (17 theorems, raw-edge engine + 5-box data) · `Fresh/FilterAssembly.lean` (the assembly; O1's four closures in) · `Fresh/NativeAnchoredLandingWitness.lean` · `Fresh/NativeJ2DmaxBoxLanding.lean` · `Fresh/APLawR4_E_4_*_Fast.lean` (heartbeat repair). Compile discipline: `./check.sh Fresh/<File>.lean`; **real exit codes** (the piped-tail lie cost us once); sorry-scan grep; fresh oleans postdating sources.

## OPEN ITEMS — resume briefs, in priority order

1. **The tail lemma (T2's mission, incomplete)** — `taillemma_*` artifacts (window walks: levels 2–5 excluded in strips [25,33); tier-2 and w7-31-33 outputs at the frontier). Resume: strip-class cap derivation with the E387 assist (middle readings bounded ≈ (4.82, 5.28, 6.21, 7.10, 8.15) in every tree run — only the top reading grows; derive this bound from end-pins + seams, then the product-cap factors into absolute constants × top-links) + E830's product form + calibrators 511/31, 86989/3565. Anti-drift guard in force: finite comb arithmetic per strip class, NO density/Diophantine arguments. Target statement: for every strip class k ≥ 4, the product-cap < (8k−1)/7, so no carve with ρ₇ ≥ 25 outside X24.
2. **`Fresh/BandNoCarve.lean` (O3, incomplete)** — band totality + per-box fixed-R₀ certificates ⇒ no arrangement in the band carves. Brief in the resume message history; patterns in PinchCert/SpineSound. [PROVISIONAL: covering] tag required.
3. **The OneSided/Pairwise totality lift** — `SpineTotalOneSided/Pairwise`: per-box, lift the [T]-verified no-exception laws (j2_cycle_v6/v12) over the reals into SpineSound's defs. Data-side; mechanical per box.
4. **The fine-ladder residual (2,329 boxes)** — either extend the U-closure key (rank, exit-numerator, value-consistency triple) or accept the DFS trees for the residual (both meet the finite standard; the former meets the elegance standard).
5. **E835** — the night's results (envelope closure, C₃, window exclusions, bands to 95) await the auditor + append; E834's item-4 citation upgrade (`review_target3_singletons.out` now exists) folds in there.
6. **k=9 wide-box residue** (18,977 tuples) and **k=5..7 ownership census** — refinements, deferred.

## Operational lessons (each cost real tokens; do not rediscover)

- **Fresh narrow agents beat long sessions on Lean** (D 71M vs D2 6.9M for same-class work). Hand over working tactic patterns verbatim.
- **Bank artifacts at computation time** — the E834 audit spent ~8M chasing .outs that should have existed. No report claim without a citable artifact.
- **REAL exit codes only** — the piped-tail lie reported a red file green.
- Provider: ~1–2 streams sustain; 5 agents = concurrency max; "Start Plan busy"/EPIPE/stall = transient — resume with context intact after a pause. Harness: TaskStop lies about agents (works on local_bash); zombie wrappers survive process kills; `python3 -c` heredocs die silently — write real script files with flushes and deadlines.
- zsh: no word-splitting on unquoted vars; no `timeout` command. Exact Fractions: cap cascades (30–150 moves), count CAPs, never chase.
- Rules: new files only; `#print axioms` always; rule 22 four-questions + the no-quarantine addendum (fixes must generalize); rule 18 grading; rule 7 tags on covering steps; the anti-drift directive (owner, 2026-11-01): comb/seam/gate vocabulary only, no classical imports.

## Budget

~125M of 500M remains by the owner's last count. The remaining named work (tail lemma, BandNoCarve, totality lift, E835) fits comfortably if the fresh-narrow-agent discipline holds.
