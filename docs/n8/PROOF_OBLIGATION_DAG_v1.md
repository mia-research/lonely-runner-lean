# PROOF OBLIGATION DAG — n=8 reduction, 2026-11-13 (v1)

The full proof = one composed theorem plus its obligation closure. Every node: **[DONE]** (Lean, axiom-clean), **[IN FLIGHT]** (agent assigned), **[DATA]** (artifact-verified, instantiation mechanical), **[OPEN]** (named, no owner yet). Terminal node: `LonelyRunnerEight` via `Fresh.FilterAssembly.filterAssembly` (all six hypotheses proved ⇒ DONE — `Fresh/FilterAssembly.lean` compiles, 16+ theorems axiom-clean).

## Layer 0 — foundations [ALL DONE, prior sessions]
`CascadeForm ⟺ LonelyRunnerEight` · landing = first fixed point · Localisation · duality Lemma 2 (clear point kills every comb-zone cover) · window law (reading 1) · `KTaxonomy` (14 labels, mutual exclusion, K2a/K2s1 empty) · anchor law `landing_is_opener_exit`.

## Layer 1 — the tropical engine [DONE]
`Fresh/TropicalCycle.lean`: `tropicalCycle_infeasible` — satisfied ratio system ⟹ no bad cycle. Instances: `joinEdge_conflict` (n=1), `composedCap_conflict` (n-hop), `twoCycle_contra` (U-table). Converse: `feasible_of_noGoodCycle` **[IN FLIGHT — TropicalConverse.lean]** — on completion the certificate space is EXACTLY characterized (soundness + completeness), closing the "missing mechanism" question at the systems level.

## Layer 2 — CoverData (the 74,613-box J2 cover)
- M1 (62,000): C_L closed form ⟹ clear point ⟹ no-carve — **PROVED end-to-end** (O1 chain: `existsGapJ → faceClear → clearPointOfCert → noCarveOfM1`).
- M4 (12,540): C₃ kill **PROVED** (`UClosureKill`: `kill_sound`, `boxAdmit_of_kill`) — consumes three lemmas now proved in-file. Residual **2,329 fine-ladder trees [DATA]**: dump v2's three witness classes map the key extension ((rank, exit-numerator, value-consistency)); mechanical.
- Box cover totality **PROVED** (`coverTuple`, `box_totality`, `box_cover_range`, `refine_cover` — third-child `[2k, 2k+2]`).

## Layer 3 — ClearPointOfCert [DONE] (O1 chain).

## Layer 4 — OneSidedSound (68 chain boxes)
- Engine **DONE** (`JoinFamComposed`: `rationalEdge_conflict`, `ChainReal`, `composedCap_conflict`).
- Data **DONE [T 68/68]** (`ComposedFamData`: `oneSidedTotalData`).
- Glue **DONE** (`OneSidedGlue`: `oneSidedSound_of_composedData` — data as theorem argument).
- Direction (a) **DONE** (`CapChainsOfCarve`: `capChainsRealized_of_chainDom` + dump-shaped `oneSided_of_dumpDom`).
- Direction (b) **DONE** (`WordCoverSide.lean`: `wordCover_demands` → `composedTotal_of_wordCover` → `oneSidedSound_of_wordCover` — carve(W₁) ⟹ family demand realized, composed with the engine to the conclusion shape; orientation finding recorded: numerator = first zone's reading, matching the census; a single zone provably cannot cover both endpoints 9 and 15). Remaining: two data-side defs — the covering refinement (`NoClearPointWordRealized`) and the dump exhaustiveness instantiation (`FamilyCoversWordEdges`, [T 73/73] mechanical).
- DumpDom correction **DONE, twice-sharpened** (`DumpDomData.lean`, 1,620 lines, green, 89 axiom-clean): spec v1 (arbitrary-U) FALSE 11/11 (empty-chain trap); spec v2 (U₀-restricted) ALSO FALSE 11/11 — all 52 caps strictly tighter than their U₀ entries (exact #eval vs uMk): **the J-half domination lives on the enumerated chains' closed trace tables, not any box-only table** — a structural fact, not a defect. Correct consumption proved: `capChainsRealized_of_chainDomU0` (chain-start at U₀, J-domination via the consumed chain's closed trace). The dump-side instantiation is now the per-chain carrier (dump v2's `attaining_chain` fields).
- Residual: 15–59 per-box totality instantiations **[DATA]** (bridge-assisted, mechanical).

## Layer 5 — PairwiseSound (5 two-sided boxes)
- Engine DONE (O2: 5 boxes pinned with exact conflict data). Totality lift **[DATA]** mechanical.

## Layer 6 — OutsideBelow17 (bands)
- Schemas 4/4 **DONE** (fixed-R₀, window, seam-plane, pinch — `CarveExclusionCerts` + `PinchCert`).
- Composition **DONE** (`BandNoCarve`: BandCertData ⟹ OutsideBelow17) + pinch data discharge (`BandPinchData`: 7 window theorems; 509/509 verified).
- SideWindowCert schema **DONE** (`SideWindowCert.lean`: the SideWindowCertV vertex-form schema + coupled-corner convexity proved + three-region composition; 43 theorems GREEN).
- 1,018 off-plane instantiations **DONE [T 1018/1018]** (`SideWindowCertData.lean`, 29,905 lines: two shared templates carrying the schema argument once, per-region bbox literals + 12 numeric facts; orientation verified two layers — data-layer exact Fractions + Lean-layer nonemptiness; the reversed side confirmed non-vacuous). Per-leaf closure folding (swc_noCarve_disj → per-leaf via sideRegions_cover_h3) **[named, mechanical]**.
- **BandCertData6 wiring DONE** (`BandCertDataExt.lean`, 1,468 lines GREEN: the sixth schema class wired into the disjunction; `bandNoCarve6 : BandCertData6 → OutsideBelow17`; **the 15 worked lines instantiated [T 15/15]** — per B1–B5 leaf × side, SideWindowCertV records + consumption theorems, all concluding `NoCarve g`; `leaves3739_discharged` proved; sign conventions pre-verified integer-exact; the Fin-atom case-helper pattern documented).
- Band data to ρ₇ < 113 **[DONE at D=32]**; exact to [25,101) at D=64; [111,113) D=64 completing.

## Layer 7 — TailBelow17 (the analytic close)
- **TAIL LEMMA CLOSED UNDER THE PIN ρ₆ ≤ 49/7** (tailrest, this campaign): (a) **anchor-classification lemma [T 105/105]** — under the pin the R=1 coverer is ∅ or the forced singleton (ρ₇, m); **corollary: every gap (8m+1, 8m+7) is carve-free under the pin at every m** (E840's named not-done closed); (b) strips 2, 3 by the exact caps (carve locus (15, 511/31) ∪ (23, 86989/3565), both attained); (c) strips 4–6 by complete chases (m=13 KILLED complete, 48.5M types; m=14 0-feasible/incomplete, honestly reported); (d) **ρ₇ ≥ 50 by TailSlowWidth.bandClearPoint_of_slow_cap17 (ρ₆ ≤ 17 ⊇ pin)** — the covering session's theorem, composed; (e) gap-regime covering kills where reached: 150/157 cone-locked (Farkas), 7 open dead system-side (K₆-nesting [T 7/7 + 15/15]; E830 product-1 cycle at band level).
- **m-cancellation theorem DONE**: monotone shortcut provably absent (edge-blind tail).
- **Middle-service sharpened**: P1 (immediate kill below J_min) proved ∀ m ≥ 4; P2 (ρ₆ budget → 0); P3 (no scalar kill). **The failing quantity = the joint interval-fixpoint collapse over ≤30 bridge nodes = R1** (E838 item 3's middle-reading bound).
- OPEN, exactly: **R1** (the all-m analytic lemma — the fixpoint collapse; **no longer load-bearing for the cap half**); **Conjecture T** (the upper pin-transport: ρ₆ ≤ 49/7 — holds [T 67/96] but 29 carves have ρ₄ covering R=7; the three-way disjunction (Theorem S) is the correct structure); R2 (exhaustive level-7 unpinned gap columns); R3 (unpinned strips 4–6, ρ₆ ∈ (7,17), ρ₇ < 50 — the residual frontier).
- Pin-removal: the pin holds for 96/96 recorded carves — the formal pin-transport is Conjecture T, not a proved lemma (the end-pin mechanism was refuted by the population: R=7 coverers are (ρ₄,4)×29, (ρ₆,6)×67, (ρ₇,21)×21 — three types, not one).
- **midsvc instruments** (m = 2..2000 verified): P1 margin closed form with the mod-8 obstruction ($r(m) \neq 0$ for every m, period 7, values {2,10,18,26,34,42,50}); $B_6$ closed form $(56-r(m))/(8J_{\min}+1)$; sliver lock + ρ₆-ladder dichotomy; corrected tail map (v1 seam-band error fixed); chase m = 15 KILLED complete (78,261,301 types, 3491.5 s); m = 14 partial (135/149 ends, 0 feasible, SIGKILLed by memory pressure — honestly reported).
- **tailcomp-v2 delivered**: Theorem S (the three-way disjunction) proved [P]; the composition under the pin proved (caps + chases + anchor classification + TailSlowWidth); Conjecture T named; the reviewer checklist (i)–(v) published. Artifacts: `tailcomp2_pincheck_v1.py/.out`, `tailcomp2_lemma_v1.out`.

## Layer 8 — the alphabet
`allLabelled_iff_allLandBelow17` + `lonelyRunnerEight_of_allLandBelow17` **DONE** (`FilterSkeleton`); 14-label completeness follows from lands-below-17 unconditionally.

## Session addendum (2026-11-13 late) — the spec-sharpening ladder
The OneSided data-side spec was falsified TWICE, each time converting a false definition into a structural theorem: v1 (arbitrary-U) died by the empty-chain/diagU counterexample; v2 (U₀-only) died by the 52-entry exact comparison — **the J-half is irreducibly chain-indexed**. The corrected consumption (`capChainsRealized_of_chainDomU0`) consumes per-chain attestation data (dump v2's `attaining_chain` fields — 109,592 caps mechanically attested [T]). This is the no-quarantine discipline operating on specs: each falsification narrowed to the TRUE structure. Per-chain carrier instantiation: IN FLIGHT (ChainDomData.lean).

## The macro statement
The oracle never falters because the duality is decidable at every scale: carve ⟺ chain ⟺ feasible ratio system ⟺ no bad cycle; not-carve ⟺ clear-point witness. The reduction theorem is the pair-exclusion: carve(W₀) ∧ carve(W₁) has no feasible point — every kill is a cycle instance of Layer 1, every accept a clear-point instance of Layer 0. The remaining obligations are: one analytic lemma (middle-service), one completeness direction (converse), one schema (SideWindowCert), two compositions (direction (b) consumption, tail-half composition), and data-side instantiations that are mechanical with the bridge.

## Session addendum (2026-11-14) — the covering half IN LEAN
`Fresh/BandTailCover.lean` (12 theorems GREEN): `anchor_classification` (the pin forces the R=1 coverer to ∅ or {(ρ₇,j)}), `gap_carve_free` (every pinned gap carve-free at every m), `pinnedTail_noCarve` (no carve with ρ₇ ≥ 25 under the pin), `pinnedCarveLocus_of_census_and_caps`. Named OWEDs: `StripChaseKill46` (data-side chases 4–6), `TailAbove50Cover` (needs re-tagging from native_decide), `PinnedTailCover` (conditionally discharged — needs Conjecture T for the full unconditional form).

## Session addendum (2026-11-14) — the tropical cycle unification
`Fresh/TropicalCycle.lean` (16 theorems GREEN) + `Fresh/TropicalConverse.lean` (28 theorems GREEN): the unifying theorem proved, three conflict lemmas recovered as instances, the converse's reduction proved lossless, the 2-cycle case proved outright. The completeness (Floyd–Warshall potential existence) named OWED with the 5-step induction sketched.

## Session addendum (2026-11-14) — Conjecture T = R2 + R3 + R4, precisely
`conjT_finite`: the (r,j)-level comb provably cannot decide T (identities I1 [T 600/600], I2 [T 400/400]; 605 exact rows; no pair forces ρ₆ ≤ 49/7). `conjT-covering`: the sketch's three central steps FALSE and replaced; the pin-free front-closure lemma proved [T 96/96]; the covering-side kill instrument (first R3 kill, 72/72 + 93/93); the residue: (T-i) nesting emptiness over (25,50), (T-ii) E852, (T-iii) V3.

## Session addendum (2026-11-14) — the tail composition IN LEAN
`Fresh/TailComposition.lean` (15 theorems GREEN): `pinnedTail` (the tail proper: self-anchor ⟹ strip j ≥ 4; split j ≤ 6 → chases, j ≥ 7 → ρ₇ ≥ 55 → width), `pinnedTailLocus` (NoCarve ∨ ρ₇ ∈ (15, 511/31] ∨ ρ₇ ∈ (23, 86989/3565]), `pinnedTailCover_of_hyp` (discharges `PinnedTailCover` from the two instruments). The honest deviation: X24 carves exist, so the conclusion is a disjunction. Named OWEDs: `Strip2Cap511`, `Strip3Cap86989` (the chase results as Lean hypotheses), `StripChaseKill46`, `TailAbove50Cover` (needs re-tagging from native_decide). TailSlowWidth deliberately not imported (its `native_decide` violates the axiom discipline; re-verification running in background).

## Session addendum (2026-11-14) — M4CertSound formalized
`Fresh/M4CertSound.lean` (525 lines, 12 theorems GREEN): `dfsWalk` (the tree-domination lemma — the pruned-tree exhaustiveness), `m4CertSound_of_forest` (delivers `M4CertSound` verbatim), `killExcl_of_m4cert` (substitutes the C₃ fixpoint kill), `boxAdmit_of_m4cert` (clear point via `boxAdmit_of_kill`'s proof shape), `m4CertSound_of_data` (consumes the banked records), `leafKeys_env90` (the key-space alignment). Named OWEDs: `DfsRootAdm` (the E810 strict-monotone side, same status as `EnvChain`) and `DfsCert` (per-box checkpoint-tree transcription). The connection MechDataBatch [T 2329/2329] → M4CertSound → boxAdmit_of_kill is complete: the M4 branch's data-to-soundness chain is formalized.

## Session addendum (2026-11-14 late) — the faithful predicate (third formulation)
`Fresh/DumpDomData.lean` (expanded to 2,945 lines): `ChainDomPerRecord` + `Attests` — the chain-indexed, per-record/whole-walk predicate. Two prior formulations falsified: v1 (arbitrary-U, empty-chain trap), v2 (U₀-restricted, caps tighter than entries). v3: per-record ∃-chain attestation, one chain per record (the intersection over hops), the empty-chain trap dead (Attests is run-conditioned). Consumption: `capChainsRealized_of_chainDomPerRecordG` + `oneSidedSound_of_chainDomPerRecordG` (glue → OneSided conclusion). One box instantiated: (1,3,4,4,5,5,7) — 14-step prefix chain, 22 transcribed trace tables. Residual: 10 boxes (8 need full-closure mk n, 2 have the datum in ChainDomData but can't re-import without a cycle).

## Session addendum (2026-11-14 late) — conjT3: the race criterion and the nesting emptiness
`conjT3_*`: **Lemma E** (carve ⟺ every K6 component in a single ρ₇-zone), **Lemma R** (the race criterion: a K6 component bounded by zone-exit (8k_L+1)/ρ_L and zone-entry (8k_R−1)/ρ_R has lap-j band live iff ρ_L/ρ_R < Φ_j; dead over [25,∞) iff (8J+1)ρ_R ≤ 25(8k_R−1)), **Lemma F** (front-closure confines comp 0), **Lemma G** (case-A front slivers only k ∈ {1,2}), **Lemma M** (the conflict sharpens with m — sliver edges, front floor strictly increase, gap-load grows by 6 per strip). Enumeration [T 11,666/11,666 exact]: 125 skeletons, 0 survivors, 0 K6-empty, negative controls pass; per-strip blocks [T 1483/1483, 1461/1461, 1495/1495, 1488/1488]; dense random [T 6000/6000]. Mechanism census: every single-component kill is race-dead over [25,∞) (19,489/19,489) — no kill needs the 50-cap; the rest are INTERSECT-DIE (band-union interlacing). **Composition: (T-i) + (T-ii) E852 close the middle branch for all ρ₇ ≥ 25 once the gap is discharged; with Theorem U (pinned), Conjecture T reduces exactly to (T-iii) V3** (ρ₆ > 17, ρ₇ ≥ 25 — open, R4 frontier). The gap: the all-boxes closure — that every chamber of the zone-boundary hyperplane arrangement over the 125-skeleton partition admits a race-dead or interlacing-killed component family — is not proved. Certificate path named: per-chamber BandCertData datasheets.

## Session addendum (2026-11-14 late) — conjT4: the middle-service generalization REFUTED
`conjT4_*`: P1 generalized to ALL m [P symbolic + T 20000/20000] — the mod-8 obstruction (gcd(40,56)=8 ∤ 54) makes the kill strict for every m. But the scalar conflict REFUTED: the feasible window [J_min(m), U(m)] WIDENS (U−J_min = 6,6,7,8,11,14 at m=13..40) — the leaf-close at j* = J_min is already pin-feasible. The conflict sharpens only in the widths, not the tail. The open content: **R1** (the joint interval-fixpoint collapse over ≤30 bridge nodes) — maximally localized, unchanged from E838 item 3. Calibration [T 58/58] across S0–S5.

## Session addendum (2026-11-15) — Theorem U named; the mirror delivery
**Theorem U** (conjT4, [T 58/58] calibration S0–S5): the pinned cap half is closed for all m by non-analytic means — anchor classification [T 105/105] + complete chases m=2..13, 15 (m=14: 0-feasible, 135/149 ends, NOT exhausted — subsumed, completion is a [P]→[T] upgrade only) + E852 for m ≥ 13. The step-3 conditional (an analytic close making the chases redundant) fails: Theorem C shows the conflict cannot be scalar. Consequence: Conjecture T reduces exactly to (T-iii) V3 (ρ₆ > 17, ρ₇ ≥ 25 — the R4 frontier), with the middle branch closing once the conjT3 all-boxes chamber gap is discharged.
**Mirror delivery** (TotalityLifts wiring): 541 mirror declarations (382 TotalityLifts + 159 banked) all standard-three axioms; D-variants + 5 pairwise instances check.sh-verified. The two data-side OWEDs entering the verbatim OneSidedSound shape, named: `NoClearPointWordRealized` (the W₁-word covering direction, box-independent) and `FamilyCoversWordEdges b (compFamOf b)` (per-box family exhaustiveness — banked families carry top-records, not full dump families, e.g. 551 chain-side edges on box (1,2,3,4,4,5,7)). Plus the per-box `JoinFam` conversion (the OneSidedGlue residual). Two agents dispatched 2026-11-15 morning: the 8-strict-box chainDomPerRecord rung (full-closure `mk n` starts) and the family-exhaustiveness quantification.
**Compile chain**: the split `ChainDomBase.lean` (U-table semantics, 1,500 lines) → `ChainDomData.lean` (per-box defs) → `SpineTotalProof.lean` sequenced; Base compiling.

## Review round (2026-11-15, external) — one false-as-written OWED caught, one statement gap sharpened
1. **`NoClearPointWordRealized` is FALSE as written** (verified here: def at `WordCoverSide.lean:235` has no domain restriction; counterexample g i = 1/16 ∀i — phases s/128 ∈ [9/128, 15/128] < 1/8 throughout W₁ = [9,15] so the hypothesis-side holds, accumulated distance 15/128 < 1 so every level is 0, and `WordRealized` requires levels ≥ 1 — no word realizes). Nothing false is proved (it is an OWED, "nothing assumes it"), but the consumption shapes `composedTotal_of_wordCover` and three sites in `SpineTotalProof` quantify it UNIVERSALLY (`∀ g : Fin 7 → ℝ`) — those shapes are unusable. REPAIR: carry the normalized domain (`1 ≤ g i` suffices: at t = s/8 ≥ 9/8, accumulated ≥ 9/8 > 1, so levels ≥ 1 on-domain and the word vocabulary is complete) into the word theorem and every consumer; the glue recovers the domain from the box facts (`FaceLo b i ≥ 1`). `FamilyCoversWordEdges` is clean (carries the box-membership hypothesis). This is the second vocabulary-completeness trap (after the empty-chain trap): a def complete on the intended domain, false universally — audit the whole word layer for domain-carrying.
2. **`TailAbove50Cover` needs a first-window conclusion** (verified: `BandTailCover.lean:270` header already documents the mismatch — `bandClearPoint_of_slow_cap17` lands in W₀ ∪ W₁ and only the s ≤ 7 branch discharges NoCarve of [1,7]; the def requires NoCarve). The planned native_decide re-tag fixes axioms only, NOT the statement: a first-window argument (or a two-window-consuming assembly, as the direct route does) is additionally owed.
3. **V3 ledger confirmed**: chamber closure completes the middle branch; V3 (ρ₆ > 17, ρ₇ ≥ 25) remains; the race census is tested-case evidence — the proof must show every admissible arrangement falls under a mechanism or already has a witness (adopted as the chamber-gap statement). R1 optional on the Theorem U route (confirmed).
Remaining checks per the review, matching our OWED list: root admissibility + forest completeness (M4: `DfsRootAdm`, `DfsCert`); every realizable word edge (chain families: `FamilyCoversWordEdges` + the per-record data); continuous coverage including boundaries (bands: datasheet discharge — boundary rows ρ₇ = band edges need explicit handling); bands through 117 not yet consumed by Lean.

## Chase completion (2026-11-15) — m=14 exhausted
`tailrest_chase14_v2.py 14` rerun to exhaustion: complete=True, feas_types=0 over 68,171,937 types (KILLED: True vs strip lower edge 111). The chase ledger is now complete for ALL m=2..15 — the m=14 partial (135/149 ends) from the conjT4 pass is discharged; Theorem U's chase component is [T] end-to-end, no subsumption asterisk remains.

## COORDINATION STATE (2026-11-15 ~12:00) — read this before compiling anything in Fresh/
**ChainDomBase.lean at HEAD does NOT compile** — two defects, both diagnosed to root cause by bisection (89-declaration march, probes GREEN through line 1451 in ~110s wall):
1. **Pathological elaboration in `trace_1_3_4_4_5_5_7` (lines 1454–1500)**: its opening `simp only [steps_1_3_4_4_5_5_7, chainRun] at hrun` unfolds ALL 19 chainRun layers at once (simp runs to fixpoint), forcing eager evaluation of every 49-branch `uAdd`/`uStep` ℚ-table on the walk — a sampled single worker task ground for 3h02m at ~10% CPU (12 sibling workers + main thread all blocked on it; RSS collapsed 1.67GB → 204MB). FIX (in `Fresh/BaseFix.lean`, staged): a `chainRun_cons'` unfolding lemma (`:= rfl`) + `rw [chainRun_cons']` one layer at a time, each hop immediately pinned by its `stepEq_i` before any table evaluation; `simp only [chainRun]` only at the end (nil case, list exhausted — terminates). Probe compiling under contention at last check.
2. **Truncated file tail (docstring at ~1517 ends mid-sentence "…is do", no def follows)**: the split boundary cut inside the `chainDom_1_3_4_4_5_5_7` docstring — that datum itself LIVES in `Fresh/ChainDomData.lean:7` (moved there correctly); Base's dangling docstring is dead weight, delete it before `end`.
**Consequence:** ChainDomData.olean + SpineTotalProof.olean are blocked on Base. The compile sequencer exited fail-closed (no olean → nothing downstream fired). Other sessions: do NOT recompile ChainDomBase.lean at HEAD (it will stall silently); apply the BaseFix.lean trace pattern if you need the file green before this session lands it.
**Also blocked:** `NoClearPointWordRealized` needs the domain-carrying repair (see review round above) before any verbatim OneSidedSound discharge — word-layer consumers carry the universal `∀ g` shape at `WordCoverSide.composedTotal_of_wordCover` + 3 SpineTotalProof sites.

## ZCode handoff (2026-11-15)

The depth-32 survey final summary extends the recorded zero-leaf coverage
through `[121,123)` (478,753,925 roots and 689,389,101 nodes).
The ordered root count was independently checked, and the integer-verifying
survey source is archived. The report is data-side evidence. The band
still needs the Lean certificate replay.

A separate V3 census draft used only `ρ₂,…,ρ₅` for the retained
components. A reading above 17 can still block in the first window
on later laps. For example, `ρ=20` blocks `R=6/5` at lap 3.
Consequently that census cannot discharge V3.

## ZCode handoff continuation (2026-11-15)

The stalled replay above is superseded. `ChainDomTrace19` checks the
19-hop trace one certified step at a time. `ChainDomData` checks all
three sparse-start boxes. `ChainDomPerRec8` checks the per-record
attestations for the other eight strict boxes from their full-closure
start tables. The aggregate theorem is `chainDomPerRecord8_data`.
All these checks use Lean 4.29.1 and the standard axioms.

The static attestations show what a chain proves from the specified
table. To consume them on an input still requires that its first-window
carve realize the starting table and admit an attesting chain.
`SpineTotalProof` now uses the box-scoped second-window word hypothesis
for its three sparse-start instances. Word extraction within those
boxes and exhaustiveness of their family edges are still premises.
The family-exhaustiveness draft remains local. The M4 replay,
band datasheets, and the V3 closure remain separate obligations.

The replay used the existing compiled dependencies. This campaign
branch shares the older native source tree with
`mia-research/lrc-n8-lean` at
`21e2912e93a9e36b51654e695451f7a0b2f80181`. To reconstruct the source
for these modules in a fresh checkout, populate missing
`LonelyRunnerFresh/Fresh/*.lean` paths from that revision and retain
the campaign versions wherever a file exists on both branches.

The two prerequisite files whose local sources differed from that
reference, `ArrangementTypesOct26` and `FastGaps`, also replayed and
are now recorded on the campaign branch.

`PinnedWordObstruction` checks that pinning the first reading at 1 and
requiring strict sorting still permits a blocked second window with no
strictly level-increasing covering word. The six covering zones all
use lap 2. This example addresses the universal second-window claim.
It leaves open the word statement for the surviving boxes with
first-window carve hypotheses.

## Synthesis of the pinned first-window walk and second-window conflict

`PinnedCarveChain` supplies the missing pinned start for the existing
`UClosure.chainWalk`. If reading zero is 1 and the first window is
carved, some other reading blocks at 1. Both strict seam inequalities
hold there, so the first step survives from any fine starting table.
The existing shrinking-frontier proof supplies the rest of an actual
walk on the same arrangement. This gives M4 its real starting zone and
gives the chain branch a walk from `(U, 0, 1)`.

The unrestricted `DfsRootAdm` interface is false for forests whose
roots are all nonbase readings. It tests even a base-row empty walk
already beyond the window. `firstWindow_of_pinned_forest` uses the
existing forest soundness theorem with roots reached by an actual
pinned opening walk. Its data still need to match those roots and
justify the soft filters.

`OpeningChainConflict.twoWindows_of_select_opening_record` consumes
one record on that actual walk. At an opening with `ρₓR = 8j+1`, a
reading still blocked at lap `k` forces
`ρₓ/ρᵧ < (8j+1)/(8k−1)`. A banked record with the same reading pair and
an upper bound at least this ratio can use the demand. The argument
works with equal laps and reduced rational ratios. The second-window
obligation on this route is to select a matching opening and a record
whose cap is certified by the same first-window walk. A full
strictly lap-increasing word and exhaustiveness for all its edges
are unnecessary for this consumer.

Exact replay on the eight full-closure boxes used the existing
`perrec8_diag_v1.py` enumerator. The componentwise-loosest table over
the completed traces still implies all their banked caps on 2,488
walks. Merging earlier by only the setter and exit numerator lost
the required information in seven boxes. Starting from the reverse
of a required cap and retaining undominated tables at each key
closed all 16 single-cap violations in the exact replay. Those
calculations motivate reusing the M4 replay for cap violations.
They are data-side checks, with the coverage and cap certificates
still to be connected in Lean. The second-window selection, V3 and
band data obligations remain open.

## Direct assembly status

The direct branch of `mia-research/lrc-n8-lean` already bypasses
the pinned M4 and chain-box obligations in this ledger.
`ChainBoxChecked.lean` covers the full pinned inside domain and
`BandBoxChecked.lean` extends the two-window coverage through 51.
The independent rational interval replay for the 73 chain roots
again checked all 73 in 380,625 nodes.

The classical target also has a combined direct assembly in
commit `c82a5ea6ea034d4f5d97ee67b6b1275e9a478716`.
Its global scale-separation theorem bounds the largest reading
by 27 times the fifth and 75 times the fourth on any unresolved
arrangement. `GlobalTailAssembly.lean` applies these bounds with
the exact rank-four kernel reduction. The capped branch needs
bounded coverage through 27 times the existential dispatch cap.
The unbounded kernel branches still need witnesses. This uses
arbitrary positive witness times on the new branches. The
independent first-two-window objective still uses its own tail
obligations.

## Chamber scoping + box-collapse v1 refuted (2026-11-15→19) — the corrected object is named
**V3 frontier census** (exact Fractions, `conjT3_v3census_v1/v2`): 91,390 tuples over ρ₂..ρ₅ grids (incl. zone-free ρ₅ > 17) vs the whole ρ₇-column [25,130): **0 ALIVE** — 85,368 COMP-DEAD + 6,022 INTERSECT-DIE, the same two mechanisms as the ρ₆ ≤ 17 case. Negative control: **98/98 recorded carves ALIVE at their own ρ₇** (narrow window) — the instrument kills nothing real. V3's empirical content is closed; what remains is the same certificate-closure question as the middle branch.
**Box-collapse v1 REFUTED** (`conjT3_boxcheck_v1`): the two-line box-uniform test (J ≤ J(q_min^box), (8J*+1)ρ_R^max ≤ 25(8k_R−1)) fails on 28.9M/32.2M observed certificates — cell boxes are too coarse (failing tuples have q=1 inside boxes whose q_min=1/7; at the box's q_min the race reopens). 
**Corrected object (v2, running)**: the chamber partition is exactly conjT3's named hyperplane set {ρ_L(8k_L±1) = ρ_R(8k_R±1)}, and within a chamber the component's boundary assignment is stable WITH the zone-edge self-bounds ρ_L ∈ [(8k_L−1)/a, (8k_L+1)/a] ∩ cell (a = the component edge), so q_min is the chamber's own hyperplane constant and death is the 2-line arithmetic test on constants. If every observed certificate is chamber-implied (0 OPEN), the middle-branch Lean object = one parametrized chamber-death lemma + a generated table — no 12K-row datasheet.
**Trace theorem status**: variants A (one-shot simp + all equations) and B (simp-staged) both kernel-timeout; variant C (pure `rw [chainRun_cons']` loop, no chainRun-simp) verified CHEAP by hop-scaling probes (3/6/12/19 hops: 10s/17s/8s/7s incl. import with sorry) — the full-file compile continues under load; the earlier grind was contention + the kernel-heavy closing.

## MERGED STATE (2026-11-19) — mechanical chain closed; word-extraction refuted universally; the two live premises
**Supersedes the stalled-replay and compile-chain sections above.** The sibling session's commits (on `hydro/blackish-zcode-mcp`, now pushed) closed the OneSided mechanical chain: `ChainDomTrace19.lean` (the 19-hop trace one certified step at a time — the pathology bypassed, not fought), `ChainDomData.lean` (all three sparse-start boxes), `ChainDomPerRec8.lean` + per-box files (`chainDomPerRecord8_data` — the 8-strict-box gap CLOSED), and `SpineTotalProof.lean` rewired to the **box-scoped second-window word hypothesis** (the false universal eliminated from the consumption shapes).
**Word-extraction REFUTED in every universal form** (`PinnedWordObstruction.lean`): the pinned counterexample ![1, 16/15, 32/27, 4/3, 16/11, 8/5, 16/9] is domain-valid (ρ₁=1, StrictMono, all ≤ 16/9), admits NO clear point in [9,15], and admits NO realized word — so `no_universal_pinned_monotone_word : ¬ (∀ g, g 0 = 1 → StrictMono g → NoClearPointWordRealized g)` is a theorem. The domain-carrying repair alone is insufficient; word extraction must be proven per-box for the spine's boxes, with the counterexample's box class routed to another instrument (chase/certificate route).
**THE TWO LIVE ONE-SIDED PREMISES** (the remaining data-side OWEDs, in the sibling's box-scoped shapes): (1) word extraction within the spine's boxes — for which boxes does no-clear-point imply a realized word, and what excludes the counterexample class; (2) family exhaustiveness for the three sparse-start boxes (`FamilyCoversWordEdges`, the ℝ-cast rewrite in `FamExhaust.lean` continues).
**V3**: exact real-box search closed for ρ₇ ≤ 34 (sibling E873–E876: the lap-4 anchor class opens at B=30→32, class (ρ₂, lap 3) at B = 713/25); grid census 0-alive through ρ₇ ≤ 130 (E877). Middle branch: chamber-level collapse v2 (`conjT3_boxcheck2_v1`) running — the corrected certificate object.
**Bookkeeping resolved**: branches unified (hydro/blackish-zcode-mcp contains n8-fresh-2026-10-30; both pushed); log numbering collision fixed (census entry → E877); agents resume 2026-11-20 04:02 on the two live premises only.

## Chamber v2 verdict + agent findings (2026-11-20)
**Chamber collapse v2 (zone-edge-bounded chambers) is INSUFFICIENT**: tally over 32.2M observed certificates — D1 85,737, D2 5,091,399, boundary 5,747,771, q-crosses-φ 24,103,521, **OPEN 2,898,013**. Example OPEN: skeleton (P,P,P,P,S1), boundary (ρ_L,k_L)=(36/5,1), (ρ_R,k_R)=(21/5,1), edges a=5/4, b=5/3, chamber q ∈ [35/27, 12/7], ρ_R^hi=27/5: threshold 81/49 ≈ 1.653 > q_min ≈ 1.296 (D1 fails), and J(q_min)=30 gives 241·27/5 ≫ 175 (D2 fails) — yet the tuples are dead. Cause: my chamber approximation used only the component's own boundary-zone edges; the true chamber partition needs ALL zone-crossing hyperplanes (conjT3's original set), after which q_min is the binding constant and the 2-line test should close. NEXT OBJECT: enumerate the true chamber partition per skeleton (the ~11.8K-signature scope), per-chamber 2-line test, count OPEN. If the true partition still leaves OPEN chambers, the death argument must mix race + INTERSECT-DIE (the column instrument) per chamber.
**Word extraction: all three spine boxes have exact counterexample CANDIDATES** (agent, quota-died pre-verification): no-clear-point + no-realized-word instances INSIDE (1,3,4,4,5,5,7), (1,3,4,5,6,6,7), (1,4,4,5,6,6,7). If verified, the box-scoped word premise is undischargeable for the spine's own boxes — the OneSided consumption needs restructuring again (W₀-window route, or chase-form demands). The candidates need exact verification (zone structure per instance) before this conclusion is firm.
**Exhaustiveness (agent, quota-died mid-rewrite)**: the banked certificate's L-tables are unusable as-is ((a) 9-entries uncapped at (8j−1)/9, (b) omitted unreachable states break loQ defaults); its recomputation with base cap + full coverage is SELF-CONSISTENT (step constraints, base, kills verified) — the corrected certificate internals exist data-side; the Lean transcription continues from them.
Bands: [129,133) COMPLETE 0 leaves — frontier [25,133) certified at D=32.
