# HANDOVER — n=8 campaign, second session — 2026-11-07 ~19:15

Written for a fresh session taking over. Read `RULES_n8_v5.md` first (rule 20). The log is `RUNNING_LOG_order8_v1.md` (18,447 lines, other session's last entry E833; this session's entry E834 is DRAFTED at `/tmp/e834_draft.md`, not yet appended — append it after a rules-audit, then renumber if the other session resumed). Branch `n8-fresh-2026-10-30`. Nothing committed.

## Where the proof stands

Target statement (E802 item 6): **the list of 14 opener–window labels is complete ⟺ every arrangement lands below 17** ⟺ `[1,7]` carved ⇒ `[9,15]` not carved. In Lean: `Fresh/FilterSkeleton.lean` proves `lonelyRunnerEight_of_allLandBelow17` — so everything funnels through **AllLandBelow17**.

**Closed and verified this weekend (exact Fractions; every claim has a script + .out in `experiments/n8/` or `experiments/nn_schema/`):**

1. **J2 box reduction, complete [T 74,613/74,613, OPEN=0]** (`j2_g1sweep_checkpoint.jsonl`, `j2_admit_cover_v1.out`). The 74,613 nearest-integer boxes of J2 split: 62,000 killed by M1 (closed-form interval certificate, `C_L` in `j2_admit_cover_v1.out`); 12,540 by M4 (certificate-DFS, `j2_admit_cert2_*`); 73 chain boxes → stage 2. Residual S characterized exactly: G_dense 68 + G_high15 4 + G_11 1 (`j2_admit_families_v1.out`).
2. **Stage 2, complete — with the corrected collapse headline (adversarially reviewed)**: 68 one-sided (IF a W₀ chain exists THEN box+join kills every W₁ word — `j2_cycle_v6.out`); 5 two-sided boxes `(2,3,4,5,6,7), (3,4,4,5,6,7), (3,4,5,5,6,8), (3,4,5,6,7,8), (2,3,4,5,6,8)` under the **raw-edge law [T 2,522,259 pairs / 0 exceptions]** (`j2_cycle_v12.py/.out` — supersedes v11 Part A, retracted for an orientation bug). **Correction by review (`review_target3_singletons.py`)**: "71 → 24 cap-form singletons" was wrong twice — under the TRUE predicate (box+bound admits no W₀ chain), **63/63 sets reduce to a single true-forcing bound (41–64 distinct) and all 7,740 leaves have one**, i.e. the collapse is STRONGER than first stated; and the kills are NOT all cap-form (5/62 pass node 0, 48/62 are direct 2-cycles, 16/23 triples have i < j — roles reversed). Both flagged upstream inputs (E810 chain reduction, `mk`/`add` exactness) reviewed **SOUND** (proved + 10,500-system brute force, 0 mismatches — `review_target12_fast3.out`). The h₃ pinch certificate and parity refutation independently confirmed sound (three ways; two enumeration gaps in the parity script closed by the reviewer, conclusion unaffected). NOTE: the 13 sweep-BUDGET tuples were later closed chainless (`j2_g1sweep_v1c`) — some reports say "13 unresolved", that is stale.
3. **Outside region exact**: no carve of `[1,7]` for ρ₇ ∈ **[17,23) ∪ [25,49)** — fixed-R₀ certifier (`frontier_box_dfs_v1.c`, usage `lo hi Dmax [leaves]`; my runs `tail_pilot_*.out`) → window types (`frontier_window_cert_v1.py`) → seam-cycle plane splits at h₁ = ρ₇−7ρ₅, h₂ = 3ρ₆−5ρ₄ → **new: tangency plane h₃ = 25ρ₇−89ρ₅ closed by the PINCH certificate R* = 25/ρ₅ = 89/ρ₇, [T 509/509]** (`tail_h3_pinch_v1.out`). h₃ is an exit-exit tangency, rigorously NOT a seam cycle (parity refutations, `tail_h3_cycles_v1.out` [T 0]). `(23,25)` is the X24 carve band; all its carves land W₁ < 17 (E827/E828). Bands `[49,75)` show 0 leaves at D=32 (`tail_state_summary_v1.out`, N's screens) — D=64 confirmation + plane census is the tail work.
4. **Cross-order instrument** (`experiments/nn_schema/schema_sweep_v1.py`): regression-validated bit-for-bit at k=8; ladder k=2..9 shows the two-window alphabet holds at every order, two-sided content only at k=8's five boxes; chains are AP-seeded everywhere. n=9 sweep at 93% (`j2_n9_checkpoint.jsonl`, 447k/480.7k — still growing under agent G).
5. **Lean, all `#print axioms` = [propext, Classical.choice, Quot.sound]**: `Fresh/KTaxonomy.lean` (14 classes, mutual exclusion, K2a/K2s1 empty, anchor law `landing_is_opener_exit`); `Fresh/FilterSkeleton.lean` (window law, `allLabelled_iff_allLandBelow17`, `FilterCompleteVia`/`BoxSpineCover` OWED, rule-7 tagged); `Fresh/CarveExclusionCerts.lean` (fixed-R₀ with decidable integer check, window types, plane splits, dyadic totality with the third-child fix `[2k, 2k+2]`); `Fresh/PinchCert.lean` (fourth schema, being written by agent D at handover); `Fresh/NativeAnchoredLandingWitness.lean` (first firing of `first_landing_of_faces`); `Fresh/NativeJ2DmaxBoxLanding.lean` (boxLanding1–6); `Fresh/APLawR4_E_4_*_Fast.lean` (heartbeat repair, originals untouched).

**Structural findings to keep:** the Nov-4 certificate systems do NOT nest (13 box guards strictly weaker than 42 envelope guards on all factors — one spine, the box spine); `ShapeAdmissible` bridge overshoots (lands-below-17 gives LonelyRunnerEight, not shape completeness); tie planes are height-dependent comb-numerator ratios, of two kinds: seam-cycle planes (h₁, h₂) and tangency planes (h₃, pinch-certified).

## Live at handover (4 of max 5 agent streams)

- **D**: formalizing `Fresh/PinchCert.lean` (fourth schema). If stalled, resume with: general TangencyPlaneCert schema + planeNoCarve via existing bridges.
- **U** (`review_*`): soundness review of E810's strict-monotone-chain reduction, `mk`/`add` exactness (M's two flagged inputs), and E's singleton collapse. **These reviews gate the computational layer — act on any unsoundness immediately.**
- **G**: n9 sweep at 93% (its agent loop survived two stop attempts — harness bug; its compute is productive, let it finish the last 7%).
- **A**: `Fresh/FilterAssembly.lean` — the four-branch Lean skeleton (M1Cond/M4Cond/OneSidedCond/PairwiseCond + bridge + totality-and-split + `CoverData → LonelyRunnerEight` with `OutsideNoCarve` explicit).

## Open items, in priority order

1. **Assembly instantiation** (A, in flight): CoverData decidable check + per-branch data lemmas.
2. **Tail ρ₇ ≥ 49**: D=64 band confirmation, per-band tie-plane census (expect more tangency planes like h₃), the height-uniform lemma. T's brief: prefix `taildeep_*`.
3. **Upstream reviews** (U, in flight): E810 chain reduction; `mk`/`add`; E812's join.
4. **M4 compression** (rule 9's next object): can 12,540 per-box certificates become a condition on n?
5. **E834 append** after rules-audit (draft ready); then the anchor-law nuance: cross-order the landing is OWNED by some reading (`landing·ρ_j ∈ 1 mod k` for some j — [T 171/171 at k=4], first-setter identification fails at k=4, so `landing_is_opener_exit` is order-8-verified, ownership is the general law).
6. **k=9 last 7%** (G finishing) then the n=9 verdict.

## Conventions that bit us (do not rediscover)

- Provider capacity: ~1–2 model streams sustain; 5 agents = max (concurrency cap); "Start Plan busy" = transient, resume later with context intact.
- Harness bugs seen: TaskStop sometimes fails silently; completed agents can show "running"; background bash can die silently (`python3 -c` heredocs — write real script files with flushes and deadlines, e.g. `anchor_law_v4.py`).
- zsh: no word-splitting on unquoted `$var` (`set -- $band` broke args twice); no `timeout` command on macOS.
- Exact Fractions blow up on long cascades: cap moves (150 is plenty), count CAPs as excluded, never chase them.
- Rules: new files only (never edit existing — multiple live sessions); `#print axioms` on everything; rule 22 four-question discipline on every exception + the no-quarantine addendum (the fix must generalize, not bucket); rule 18 grading; nothing committed.
