# AUDIT — Narrative-Conclusion Layer (v2)

**Head of the narrative-conclusion audit.** Adds Phase 2 (the *consolidation* layer: compendium + addenda) to Phase 1 (the summary layer, in `_v1`). v1 is retained for its phase-1 detail; this file carries the current picture + the cross-phase synthesis. Method unchanged: isolated agents, decidable artifacts, "tidy is suspect" enforced as a source-check.

`M:` = `POSITIVE_FINDINGS_MASTER_v9.md`. `S:` = `PROJECT_SUMMARY_secp256k1_v2.md`. `ADD1/2/3` = the three `POSITIVE_FINDINGS_ADDENDUM_*_v1.md`. `CMP1/2` = `BRIDGE_PROGRAMME_COMPENDIUM_v1/v2`.

---

## PHASE-2 HEADLINE — the entire addendum layer was never reconciled into v9

The summary certifies v9 as *"reconciled across master + both addenda"* (S, Part A header). It is not. By-name grep in v9:

- **ADD1: referenced 0 times.** Reached the master only piecemeal; v9 even cites the *pre-proof* artifact (`…supersingular_v1.md`) where ADD1 carried the proof (`…_v2.md`).
- **ADD2: referenced once (M:843) — and that hit is a *loss admission*,** not a reconcile: "was Frontier #17 in ADDENDUM_2, dropped in the v3→v4 renumber and absent from v4/v5."
- **ADD3: referenced 0 times.** ADD3 says it "feeds the next master compile (head v8)"; v9 is that next master and folds none of its 5 items.

**The master's apparent completeness is an artifact of an *independent* lineage** (the ZCode `tensor-decomp` work + `RESULT_e2_identity_extended_verification_v1` + `RESULT_algebraic_number_layer_v1`) that happens to re-cover a handful of addendum objects (120° law → M21; non-abelianity → M23; the `e₃` sign → P16). **Every addendum item without a ZCode twin was dropped.**

This is **not inflation.** Across all three addenda: **0 grade-inflated, 0 firmed** — v9 is nowhere *less* cautious on a shared claim (it even declined ADD1's `A_new` supersingular proof, keeping N2 open). The disease is **selective omission under a false completeness certificate.** That is why the results feel suspect: not because they were talked up, but because a large fraction of them silently didn't make it into the document that claims to hold them all.

---

## THE THREE MECHANISMS  *(named separately — a future reference must NOT collapse them)*

1. **STALENESS.** A conclusion doc frozen at an earlier base, silently behind the results. *(Phase 1: the summary is built from master v4; it prints v4-era firmer forms of things v9 later walked back, and is blind to the whole v7–v9 layer incl. the priority lead.)*
2. **SYNTHESIS-OUTRUNS-ROWS.** An account/heading asserts more than its own graded rows support, *in the same document*. *(CMP2 §0 necessity-mechanism; summary B.5 "RESOLVED" heading over its own "Open" ledger row.)*
3. **UN-RUN RECONCILE + FALSE COMPLETENESS CERT.** A source's frontiers / retractions / nulls silently fail to propagate into the doc that certifies it carried them. *(The whole addendum layer → v9.)* This is the Phase-2 headline and the largest by volume.

These are different failures with different fixes. #1 wants a staleness banner / sync. #2 wants the heading re-graded to its rows. #3 wants an actual reconcile — or the false cert struck.

---

## PHASE-2 LEDGERS

### L2.1 — Compendium CMP1 → CMP2 (self-drift): net conservative, two firmings

CMP2 is an explicit *restoration* doc (admits CMP1's "every item carried / compile-diff was run" self-certs were false; restores 11 dropped + 10 weakened items + a controls table). Net **more conservative.** Two localized firmings under that surface:

| # | Finding | Class |
|---|---|---|
| C1 | **§0 "account" out-runs its own rows.** Asserts the reciprocity dichotomy is complete necessity — "no congruence can do it … a bridge *requires* ζ_ℓ in the CM field … the mechanism behind the entire dichotomy" (CMP2 L36-37) — while every row carrying it is `[VERIFIED — bounded]` and §4 admits a class of ℓ≥5 bridges "would read as absent — **wrongly**." NEW in v2. | **SYNTHESIS-OUTRUNS-ROWS** |
| C2 | **Deleted secp §2 dropped a deflationary caveat:** CMP1's "this is a restatement of j=0/CM, not an independent property, and **carries no leakage or ECDLP content — every quantity … is public**" (CMP1 L60-63) is gone from CMP2. | **CAVEAT-DROPPED** |

CMP2's own footer: its fresh re-audit "**HUNG (~9h, killed) … so a new loss introduced by v2 would not have been caught. That gap is open**" (CMP2 L199-201) — and C1/C2 are exactly such uncaught v2-introduced losses. The gate-hung-run-proceeded hazard, self-documented.

### L2.2 — Addendum layer → v9: the losses, grouped by KIND (opposite kinds kept apart)

**(i) Dropped retractions — dead claims left un-protected.** ADD1: retractions 28,29,30,32,35,36,37,38 not carried. ADD2: retractions 39,40,41,42,44,45 not carried. A dropped retraction un-protects a killed claim against re-use.

**(ii) The ONE re-claim (ADD1 only).** The λ₃ eigenvector "60→85% μ₃-covariant, broadband" was **retracted twice** in ADD1 (a *gauge artifact*, "not a property of a well-defined object," resolved by two named scripts). v9 **re-asserts it**: "λ₃ up to 85% (real, broadband, no closed form — OPEN, not resolved)" (M:1194). *(ADD2/ADD3 checked clean — no re-claims.)*

**(iii) De-sharpened frontiers — live leads reverted to a blunter/earlier form.**
- **N1 / ½-saturation.** ADD1 & ADD2 B2.3 delivered an account (`½ = 2/4`, relative-rigidity, the 2+2 eigenvalue budget); v9 reverts to "the one measured anomaly … **with no account** … no explanation is offered" (M:295) and lists the Lang-torsor bridge as an *unrun* next probe (M:824).
- **E3 cubic difference-set (ADD2 B3.4).** ADD2 recorded a **pre-registered reject**, E3(real)=13125 at the **98.4th percentile, p≈0.033, "interpretation OPEN"**; v9 reverts to the **stale H3** null "difference-set … **at the AP-control floor**" (M:1189, tagged "carried verbatim from H3" M:1196). The stale-panel-as-honesty-certificate mechanism, live. **See recovered positive below.**

**(iv) Dropped frontiers & scoped nulls — live leads that now exist nowhere in a top-level doc.** Listed under "Recovered results" below because that is what they are.

**Tallies.** ADD1: 7 retractions dropped, 1 re-claimed, 7 frontiers dropped, 1 de-sharpened, 0 firmed/inflated. ADD2: 6 retractions dropped, 0 re-claimed, 13 frontiers dropped, 4 de-sharpened, 1 primary caveat dropped, 0 firmed/inflated. ADD3: 4 frontiers dropped, 1 method-note dropped, 0 of its own items survived.

---

## RECOVERED RESULTS — live, and invisible to every current top-level document

This is the "what is still there" you asked for: results that are **not distorted, but unreachable** from anything a new session reads. They live only in the addenda.

**From ADD1:**
- The entire **d-side (n,k,D) thread** — Dirichlet reciprocal-floor lattice (A1.5); Farey solid / 1-D coprimality net + its ℤ/2 symmetry & non-genericity vs matched control (A2.8); three-level complexity filtration (A2.9); the T=2 stratum / whether T=3 opens past fiber width 10⁷ (Frontier 22); a per-n coprimality-net density null + "which cycles carry the ~3× β₁ excess" (Frontier 24).
- The **full-scale-at-secp scoped nulls** (A3.2–A3.6): island joint-set, island GLV cross-set, flap-ε under the group law (2⁻⁶–2⁻⁹ power ladder), flap density 130-vs-256, no d-free selector.
- The **LBE battery** (A3.1, 30×25) + its method finding "χ² Holm alone would have produced a false positive here; report the empirical rank."
- N1 **sharpening** (§XI.10): parity refuted at 10 primes; bulk-moment class disqualified a priori; anomaly localized to the extremal tail; a named candidate mechanism ([−1]-involution 2+2 split) with a live counterexample (bx → 0.909 not ½).
- An explicit **abstention** (Frontier 21): "diffuse family-wise LBE dependence — ABSTAINED, not closed; needs more null draws, not re-analysis." *(Your memory: abstention IS the finding.)*

**From ADD2:**
- **Twist-orbit forced landscape** (B1.7): "Arm II dissolves to an exact frame identity ⟨f_a,f_b⟩ = nI − J", Parseval Σ|V(a)|²=n(n−1), 3-pt multiplicative bispectrum ≡ 0.
- **Sub-Weil reduction** (B1.3 / Frontier 27): S_y ≤ 2 reduces to the sign of one L-polynomial coefficient; |V₁(a)| ≤ √3·√p (largest observed 1.932√p at p=547).
- **v≤0 route** (B1.4): FALSE by exact counterexamples, but "the inequality is NOT refuted" — v≤0 was sufficient, not necessary.
- **ℓ≥5 ideal-level CM route** (B1.6): collapses to a rational symbol of U=|t−1| — forced algebra, not a null.
- **E[u⁴] ~ SU(2)** (B3.1): excludes the 3/8 torus/CM reduction, scoped OOS with fired controls.
- The **group-law joint difference-set frontier** (Frontier 29): P_i ± P_j via curve addition, χ₃(x_j−x_k), triple/multilinear — each its own prereg. *(This is the object-class that touches the DLP; it was reverted to a "done at the floor" stale list.)*

**From ADD3** (the whole session's work, none of which landed):
- **W_N analytical lock** (Item A): closes the 1-D "intertwined Fourier proxy" extraction route three ways — plus a forward-looking **caution**: "the pullback couples a and b, so the full (a,b) diagonal orbit is a forced zero; keep the geometry's μ₃ index and the scalar phase on separate axes." *(A caveat written to prevent a future symmetry-mismatched false positive.)*
- **Two deficit-channel exclusions** (Items B, C) that **narrow the #1 live lead** (the sub-Rayleigh deficit N7): the deficit's organization is NOT in the μ₃-graded b-frequency channel, and NOT in the μ₃ real-part phase isotype. Named next probes: higher-order phase invariants; the c-axis / c=±b diagonal; p-scaling const-vs-1/log-p.
- A **method note addressed to the master's Anomaly-Drill layer**: "a must-fire control can still MISS a variance-miscalibration when it doesn't share the signal's correlation structure; the diagnostic is effect-size scaling with N — a pooled Z flat as N grows is a variance artifact." Did not land in the Anomaly-Drill rule.

---

## THE STANDOUT RECOVERED POSITIVE  *(flag — do NOT re-deflate)*

**E3 cubic difference-set on the real 82 keys (ADD2 B3.4):** a **pre-registered reject** — E3(real)=13125 at the **98.4th percentile, p≈0.033**, explicitly "**not a null-estimation artifact**," interpretation **OPEN**, **not** MC-corrected. v9 buried it back to a stale "at the floor" null.

Per the project's standing stance (and the ★ suppression-bias operating fact): this is a candidate positive that was converted to a null at the consolidation seam. It is **owed a test** — MC-correction across the pre-registered family, reproduction, a matched Farey/fundamental-domain null, and out-of-sample — **not** a re-deflation. It sits on the group-law difference-set object-class (ADD2 Frontier 29) that is the one class touching the DLP. *(This is precisely "the very lack of false positives is a worry": here is a fired pre-registered reject that the layer suppressed.)*

---

## HANGING RESULTS (new — preserved, not resolved)

- **H2‑1 — Is λ₃ a live lead or a dead gauge artifact?** ADD1 (two scripts) says dead. v9 (M:1194) lists it "real, broadband, OPEN." The two current documents contradict.
- **H2‑2 — Is the Stickelberger (D2) citation discharged or owed?** ADD2 B2.1 says discharged with 3 Katre caveats ("[CITED — verified]"). v9 M:1289 says still an owed "debt." A `[PROVED — modulo (D2)]` law (the c₂-branch, Part XVI.A.1) rests on the answer. *(Overlaps Phase-1 H-1's undefined-"(D2)" finding.)*

---

## OWED  *(logged, not fixed — per the standing "log only" choice)*

1. **The addendum layer is un-reconciled and mis-certified.** Either run a real ADD1/2/3 → master reconcile, or strike the "reconciled across both addenda" claim from the summary/master. Until then, the top-level docs overstate their own completeness.
2. **The recovered-results list above needs a home** in a top-level doc, or it stays invisible. This list is itself a deliverable — the current map of live leads reachable from nothing.
3. **E3 pre-registered reject** owed its MC-correction + matched-null + OOS test (see above).
4. **H2‑1, H2‑2** each owe a reconciliation decision.

---

## NEXT

- **Memory layer** (`btc_puzzle_INDEX.md` + `feedback_*`/topic pointers) — highest-propagation conclusion, read at every session start. Both phases predict the same risk there.
- Then a short **cross-corpus synthesis** pulling the recovered-results list into one "what is still live" map — the thing this audit was for.
