# Downloads Proof Attempt Harvest
**Date:** 2026-04-11  
**Purpose:** Double-check `/Users/trentpalelei/Downloads` for proof attempts that did not become the final proof route but still contain reusable mechanisms, diagnostics, or conceptual framing.

---

## Bottom Line

Yes: the Downloads folder contains several useful proof attempts and handoff notes.

The important pattern is that the best Downloads-only artifacts are **mechanism notes** and **audit notes**, not hidden finished proofs. They do not appear to supersede the now-complete `n=11` and `n=all` routes, but they do preserve a number of ideas that are still worth carrying forward:

- conceptual reframings that clarified what the real object was,
- local proof patterns that later arguments could reuse,
- diagnostics explaining why certain elegant-looking routes stalled,
- and skeptical audits that distinguish proof content from intuition.

---

## Most Useful Downloads-Only Notes

### 1. `lrc_deep_structural_analysis_v1.md`

**Why it matters:** one of the strongest conceptual notes in the folder.

**Reusable facet:**
- Reframes obstruction dynamics as motion on a torus / Cayley-type object rather than on a line.
- Interprets lower-band safety and complementarity as a CRT / transport phenomenon.
- Suggests a potential-function view of the obstruction deficit `D(b)`.

**Use now:** good source material for explaining why the final proof naturally wants transport, symmetry, and CRT language rather than purely interval language.

---

### 2. `lrc_v516_synthesis_2026-03-09.md`

**Why it matters:** cleanly separates architecture from execution.

**Reusable facet:**
- States the proof program as a two-layer structure:
  - outer structural/case analysis to show the safe set has positive mass,
  - inner Weyl-equidistribution step converting positive mass into the lattice-point conclusion.
- Gives an honest editorial judgment about which geometric simplifications actually simplify proof and which merely rename the same burden.

**Use now:** helpful as a high-level explanation of the `n=all` route, especially if we want a short “why the proof is shaped this way” memo.

---

### 3. `lrc_geometric_review_2026-03-09.md`

**Why it matters:** one of the best skeptical filters in the Downloads set.

**Reusable facet:**
- Distinguishes intuition from proof.
- Says the “coverage capacity paradox” and related geometric framing are useful explanatory pictures, but not themselves proof engines.
- Clarifies that reorganizing cases into prettier geometric labels does not automatically eliminate the old route splits.

**Use now:** valuable guardrail against overselling geometric narratives in the final write-up.

---

### 4. `lrc_nall_synthesis_review_plan_v1.md`

**Why it matters:** sharp map of the late-stage `n=all` search space.

**Reusable facet:**
- Explicitly asks whether a single master theorem exists or whether two structurally distinct sub-problems remain.
- Introduces the **Universal Positivity Lemma (UPL)** idea as a genuine unifier candidate.
- Separates the landscape into:
  - a within-band composite-`n` problem centered on non-unit `z=0` / coset essentiality,
  - an outside-band prime-`n` problem centered on `Xi_tr` residual safe mass.

**Use now:** useful retrospective on how the search decomposed, even if the final proof ultimately took a different closure route.

---

### 5. `LRC_Trapped_Branch_Session_Handoff.md`

**Why it matters:** preserves constructive witness anatomy that would otherwise be easy to forget.

**Reusable facet:**
- Identifies concrete witness families in trapped-branch situations.
- Clarifies that several “framework failures” were scope failures, not mathematical failures.
- Separates early-time witnesses from middle-zone witnesses instead of trying to force one template to capture both.

**Use now:** strong explanatory note for why earlier witness frameworks looked incomplete without actually refuting the theorem.

---

### 6. `files (15)/LRC_Lemma_BR_Trapped_Handoff.md` and `lrc_lemma_br_proof_state_2026-03-06.md`

**Why they matter:** these are among the clearest diagnostics on the Lemma BR bottlenecks.

**Reusable facet:**
- Gives a precise account of what the trapped regime means structurally.
- Shows how the old Case-B search reduced to concrete existence and window gaps rather than vague “hardness.”
- `lrc_lemma_br_proof_state_2026-03-06.md` is especially useful because it isolates the sharp counting bottleneck and explains why the naive size bound lands exactly on the edge.

**Use now:** good historical record of which combinatorial obstacles were real and where the old framework ran out of room.

---

### 7. `lrc_g4b_nz0_backprop_proof_v1.md`

**Why it matters:** probably the best compact local-mechanism note in the folder.

**Reusable facet:**
- Introduces a back-propagation argument for non-unit `z=0` exits.
- Instead of trying to solve the exit fibre directly, it tracks an uncovered residue backward from `b_exit` to the last obstructed fibre.
- This is a clean example of replacing heavy subgroup bookkeeping with a causality argument.

**Use now:** worth preserving as a standalone proof pattern, even if the final proof does not quote it verbatim.

---

### 8. `files (10)/lrc_g4b_nonunit_z0_summary_v1.md` and `files (10)/lrc_g4b_nz0_audit_report_v1.md`

**Why they matter:** they contain a real correction, not just a restatement.

**Reusable facet:**
- Correct the local event criterion from an `Enter_e` viewpoint to a `Leave_e` viewpoint.
- This is mathematically meaningful: the right signal at a non-unit `z=0` exit is what the runner stops covering, not what it starts covering.
- The audit also records a plausible alternative lower-band route and documents exactly what remained analytic versus only certified.

**Use now:** useful if we want to explain how the local exit anatomy became conceptually correct.

---

### 9. `lrc_g4ot_b3_closure_v1.md`

**Why it matters:** shows a successful shift in proof style.

**Reusable facet:**
- Moves from local witness-hunting to a global safe-fibre count argument.
- Uses the `Z0S.3 + U-FORCE` style of reasoning to show positivity directly.

**Use now:** good example of when global counting dominated local construction.

---

### 10. `lrc_subcase_i_analysis_2026-03-09.md`

**Why it matters:** preserves lower-band / period-1 intuition in a useful form.

**Reusable facet:**
- Highlights that per-period isolated events can be too sparse on their own, while lower-band safe mass still accumulates linearly.
- Gives a concrete “lower band / Period 1” route that avoids some resonant-pair complexity.

**Use now:** helpful for explaining why some local periodic effects were supportive but not individually decisive.

---

### 11. `lrc_proof_state_2026-03-06.md`

**Why it matters:** good corrective note on witness taxonomy.

**Reusable facet:**
- Corrects the earlier LL-heavy picture.
- Records that many true `k=2`-only witnesses were of mixed type rather than the naive symmetric type.
- Helps explain why the old search kept needing more than one constructive family.

**Use now:** useful historical correction when summarizing the witness-search stage.

---

## Useful Audit / Skepticism Notes

### `lrc_v5_16_proof_audit.md`

**Why it matters:** strongest skeptical audit in the Downloads folder.

**Reusable facet:**
- Distinguishes what was analytically closed from what was only sketch-level or computationally supported.
- Flags specific proof obligations that looked “basically done” but were not yet theorem-grade.
- Keeps the Tier 1 / Tier 2 distinction honest.

**Use now:** strong source when we want to explain why some old drafts felt close but still were not publication-ready.

---

## 2025 Layer

The 2025 Downloads material is noisier and more overclaimed than the March 2026 notes, but it still contains several genuinely useful precursor ideas. The right way to read it is as an **origin story for later mechanisms**, not as a trustworthy proof state.

### Strongest 2025 takeaways

#### 1. Early dimensional stratification already mattered

Files:
- `A Structural Reduction of the Lonely Runner Conjecture v4.txt`
- `lrc_three_tier_proof.md`
- `lrc_standalone_proof.md`

**What survives:**
- The torus reduction and dimension-based case split were already central.
- There was already a strong instinct to separate:
  - generic / equidistributed behaviour,
  - resonant higher-dimensional behaviour,
  - and the genuinely hard 1D resonant remainder.

**Why this matters now:** even though those drafts overstate what was proved, they show that the later proof architecture did not come from nowhere; the search had already converged on “dimension + structure class” as the right organizing language.

---

#### 2. The project already knew how to distinguish evidence levels

File:
- `lrc_three_tier_proof.md`

**What survives:**
- Clear separation between empirical success, partial analytic machinery, and actual theorem-grade closure.
- An unusually honest statement that the generic case was clean while the resonant case remained incomplete.

**Why this matters now:** this note is one of the best 2025 artifacts because it preserves intellectual discipline. It is a good reference for how the project learned to separate “strong evidence” from “finished proof.”

---

#### 3. The hard core was already being isolated as a finite / explicit remainder

Files:
- `A Structural Reduction of the Lonely Runner Conjecture v4.txt`
- `LRC_Paper_Gap_Analysis.md`

**What survives:**
- A strong reductionist instinct: try to push everything easy into resolved strata and leave one explicit obstruction functional or overlap inequality.
- The overlap-mass / boundary-set viewpoint is not the final all-purpose proof, but it is a real early attempt to name the hard object precisely.

**Why this matters now:** this is one of the first places where the search stops treating “the conjecture” as a single blob and instead asks for a sharply defined residual target.

---

#### 4. The d=1 shift from “cover the bad set” to “prove the good set has mass” is conceptually valuable

File:
- `lrc_d1_resonant_rigorous.md`

**What survives:**
- The old naive covering argument failed because it tried to sum forbidden lengths too crudely.
- The replacement move was conceptually better: focus on the positivity of the good set instead.

**Why this matters now:** even if the specific Fubini/transversality argument in that file is not something to trust as final, the strategic flip is important. It anticipates later proof habits where positivity of the safe region is the right object, not a brittle upper bound on the bad region.

---

#### 5. The project was already learning to treat failures as artifact classes to be explained, not just counted

Files:
- `lrc_d_ge2_failure_findings.md`
- `LRC_GAPS_RESOLUTION_SUMMARY.md`

**What survives:**
- Classification of failures into rank issues, precision issues, and insufficient-horizon issues.
- A strong norm that every failed certification should be anatomised.

**Why this matters now:** even where the resulting “all resolved” conclusion is too optimistic, the diagnostic style is good. It helped build the later habit of separating a mathematical obstruction from an implementation artifact.

---

#### 6. Some 2025 synthesis notes are useful precisely because they are overambitious

Files:
- `discovery_02_lrc_solution.md`
- `lrc_gect_master_outline.md`

**What survives:**
- They gather many project themes in one place:
  - torus language,
  - ergodic coverage,
  - arithmetic progression exceptionalism,
  - fragility / resonance dichotomies,
  - and computational methodology.

**What does not survive:**
- They routinely promote conjectural or partially justified arguments to “complete proof” too early.
- Some frameworks, especially the A9 / GECT language, function better as explanatory overlay than as proof engine.

**Verdict:** useful as intellectual archaeology and vocabulary source, not as proof authority.

---

### 2025 notes with the best current value

If I had to keep only a small 2025 subset for future understanding work, it would be:

1. `lrc_three_tier_proof.md`
2. `A Structural Reduction of the Lonely Runner Conjecture v4.txt`
3. `LRC_Paper_Gap_Analysis.md`
4. `lrc_d1_resonant_rigorous.md`
5. `lrc_d_ge2_failure_findings.md`

Together these preserve:
- the early architecture,
- the explicit hard remainder,
- the positivity flip,
- and the habit of rigorous failure triage.

---

## Lower-Trust but Still Informative Notes

### `lrc_nall_closure_integration_v1.md`

**What survives:**
- a useful proof-tree / dependency-table style summary,
- an attempted unification around safe-fibre counting.

**What does not survive:**
- status labels are too aggressive; too many branches are marked as fully closed.

**Verdict:** useful as dependency mapping, not as a truth source.

---

### `lrc_g4ot_proof_v1.md`

**What survives:**
- decent subcase decomposition,
- some local structural claims around interval behaviour and floor-change separation.

**What does not survive:**
- closure claims are ahead of the actual argument in places.

**Verdict:** useful as scaffolding, not as a trusted finished proof.

---

## Overall Assessment

The Downloads folder did contain additional mathematical value, but mostly in the form of:

- **mechanism extraction** rather than final closure,
- **search-space decomposition** rather than theorem completion,
- **local proof patterns** rather than end-to-end manuscripts,
- and **audit honesty** rather than polished exposition.

The most reusable facets are:

1. the torus / CRT / transport interpretation,
2. the outer-structure plus inner-Weyl two-layer architecture,
3. the split between true proof content and merely geometric intuition,
4. the trapped-branch witness-family diagnostics,
5. the non-unit `z=0` back-propagation and `Leave_e` correction,
6. and the shift from local witness search to global positivity counting.

---

## Recommendation

If these notes are going to inform the final package, the best next move is **not** to import the Downloads drafts wholesale. The right move is to distill them into a compact mechanism atlas tied to the final `n=11` and `n=all` proofs:

- “What conceptual object did this note identify?”
- “What local mechanism did it isolate?”
- “Did that mechanism survive into the final proof, get replaced, or remain only intuition?”

That would preserve the mathematical insight without inheriting the status drift and overclaiming from the old drafts.
