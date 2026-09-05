# RETROSPECTIVE — the interpretation-phase suppression audit (v1)

**Date:** 2026-08-04
**Mandate (user, this session):** find leak/structural signal — *or, more accurately, possible
signal* — that the documented **one-way suppression bias** may have glossed over, downgraded, or
demoted. Explicit licence: **promoting false positives is acceptable** here; they are caught later by
replication/OOS. The suspect object is the inverse — a **null built on a "perfect" negative** (a sweep
that came back clean with *no* 1.5–2σ blips to chase). A calibrated search throws off several; a search
that throws off none is the fingerprint of pre-test suppression.

**Reframe carried through the whole audit (user):** the goal was **never an ECDLP break.** It is leak or
structure that either (a) **proves** invulnerability rather than *declaring* it, or (b) could help
**construct a reduction.** Therefore the sentence *"this does not equal a break of ECDLP, so it is a
null"* is itself a bias expression, not a verdict — banned as a demotion in this audit.

---

## 0. Why this audit is a NEW layer (not a repeat)

Three prior de-bias attempts each fixed a real layer and left this one open:

| layer | fix | what it left open |
|---|---|---|
| **experiment DESIGN** | pre-registration (`experiment-designer` gate, 131 PREREG files) | the **interpretation** of a result the prereg permitted — Bonferroni choice, OOS gate choice, "washed out", "CM-driven", control adequacy |
| **the RULES** | `RULES_AUDIT_dogma_vs_guidance_v1.md` (found unearned closures *in the rules*: §1 no-PRNG "scope + unearned closure"; §8 "the pattern across §1–5") | the closures *in the results themselves* |
| **nulls-as-guidance** | `feedback_closure_grade_2026_07_28` (a closure is a graded claim) | the graded-closure bar is applied at write-time; it does not re-audit results already filed as nulls |

Pre-registration governs the coin flip. **The bias re-enters when the coin is read.** This audit targets
the read: every place a real-or-possible effect was turned into a null *after* the data was in.

---

## 1. The audit protocol — 4 triage questions (the decidable artifact)

For each demoted/nulled/bounded item, ask — each answer is a check that can be *run*, not a judgment:

- **Q1 — Perfect-null tell.** Did the sweep come back with **zero** cells to chase (no 1.5–2σ blips)?
  A calibrated search on a real target throws off several. Zero ⇒ suspect the cells were pre-killed or
  the statistic is forced-flat. *(user's own base-rate tell)*
- **Q2 — Control adequacy.** Did the control that killed the positive **share the signal's forced
  symmetry** (wrong-null), or is it **forced to the same value for any target** (a saturating statistic
  validates nothing)? A firing control validates a *channel*, not a *cell*.
  *([[feedback_positive_control_forced_zero_offchannel]], [[feedback_wrong_null_shared_by_controls]])*
- **Q3 — Magnitude-as-nothing.** Was a **bounded magnitude** (√p, 1/√n, a φ-power-floor, a %-coupling)
  read as "no structure"? The structure lives in the **eigenvector / isotype / subspace**, not the
  scalar. *([[feedback_negative_bias_enlarge_nulls]])*
- **Q4 — Interpretation move.** Was the kill an analysis *choice* rather than a measurement? —
  multiple-comparison penalty on a **pre-specified** channel; an **OOS AND-gate** with no power against a
  sub-detection effect; "CM-driven ⇒ not a signal"; "washed out at larger n" **without checking the
  larger-n test kept power**; "doesn't touch ECDLP".

A "yes" on any Q flags the item for a **re-test that allows false positives** — not a re-adjudication.
Per the core memory, *same-model gates do not catch suppression*; the ranked worklist below is for
**user (external) oversight** to steer, and each re-test's spec goes through `experiment-designer`
(mandatory) — noting that gate catches mechanical/frame defects, not the suppression itself.

---

## 2. Mechanical harvest (corpus scan, `demotion_harvest_v1.py`)

329 files (`RESULT_*`, `PREREG_*`, `SYNTHESIS_*`, `ANALYSIS_*`) → 3,827 demotion-lines.
Diagnostic classes (the small, high-signal ones read exhaustively):

| class | hits | reading |
|---|---|---|
| `ecdlp_frame` | 101 | **mostly HEALTHY** — disclaimers attached to a bound to prevent *over*-claim ("this bounds \|U\|, not ECDLP"). The dismissal-direction cases (χ₂(y)-supersingular "bound-irrelevant") were already caught → retraction #26. |
| `at_floor` | 116 | magnitude bounds → Q3 candidates |
| `washed_out` | 33 | read all → 4 substantive leads (below) |
| `control_kills` | 19 | read all → 2 substantive leads (below); the rest are prereg void-conditions (healthy) |

**Meta-finding:** the corpus is heavily disciplined. Suppression is **not** in bare hedge-words (they are
banned and largely absent); it is in a handful of **subtle interpretation choices**. The ledger below is
those choices.

---

## 3. THE RANKED SUSPECT LEDGER

Grade key on each: the ORIGINAL demotion, then the triage flag, then the re-test. No item here is
re-adjudicated as "still nothing" — each is a **lead to re-test**.

### Cluster α — the χ₂(y) / joint-(x,y) / supersingular complex  *(highest recoverable value)*
This cluster holds the project's one exact unexplained anomaly, its self-declared #1 open lead, and the
one dismissal-by-"not-ECDLP" it already had to retract. The named next probe (**D2**, the Lang-torsor
twist bridge) is **untouched**.

- **S1 — the ½-saturation anomaly (N1 / M3 / VII.5).** χ₂(y) (dim 4) saturates **0.470→½** of its 4√p
  ceiling while the **same-dimension** additive bx+cy saturates **0.876** — a 1.86× systematic gap at
  identical dimension that "a max-over-frequencies artifact cannot produce"; effectively **2 of 4**
  eigenvalues carry weight-1 mass (the 2+2 splitting). Status in master: *"the one measured anomaly with
  no account… twice attempted, twice not closed; no explanation is offered."*
  → **Not demoted — PARKED.** An exact, reproduced structural anomaly on the DLP-relevant sum, left
  unexplained. Under the asymmetric stance this is the strongest thing in the set and should be pushed,
  not filed. **Re-test:** run **D2** (does the √p·ζ supersingular rigidity survive L_{χ₂(y)} ⊗ L_{χ_a},
  giving V(a) exact algebraic values structured in a?) — the named, untouched next probe.

- **S2 — the joint (x,y) shadow, ρ=0.93 (M14 / Part VI / §XI.1), the self-declared #1 OPEN lead.**
  Killed as a *separation* claim by the **scalar-fidelity control**: phase-only reconstruction gives
  0.999 for the leaking character **and** 0.999 for a random function of d ⇒ "does not separate."
  → **Q2 flag.** A phase-only reconstruction that saturates to ~1.0 for *any* target is a **statistic
  forced to the same value regardless of signal** — it cannot separate anything, so its failure to
  separate is uninformative about whether the 0.93 carries a character. The exact surviving part (even/odd
  U(−a,b,c)=U(a,b,−c)) is real. **Re-test:** replace the saturating scalar-fidelity statistic with one
  that is **not** forced equal across targets — e.g. the **isotype/frequency-support pattern** of which
  (b,c) carry the alignment (master itself lists this as "set up, NOT YET RUN").

- **S3 — the χ₂(y)-supersingular "not-ECDLP" dismissal (retraction #26).** Already caught and reversed:
  *"supersingularity IS the classical ECDLP lever (MOV / Frey–Rück)"* and *"cover-based transfer
  (GHS/Weil descent) is a real attack family; C→E is exactly a cover."*
  → **Confirms the Q4 mechanism is live in this project.** The reversal reinstated **Route 3** (cover
  transfer into Jac(C), N4/§XI.13) and **D2** as OPEN — but neither has been *worked* since. **Re-test:**
  treat Route 3 as an active reduction-construction lead (its own worklist), not a parked "OPEN".

### Cluster β — real-key anomalies (rare; closest to the actual target)
Most findings are scale-free curve arithmetic. These few are about the **actual 82 puzzle keys** — higher
interest per the project's real goal, and correspondingly higher cost if suppressed.

- **S4 — the E3 diffset-cubic anomaly (`RESULT_diffset_cubic_cmvanishing_v1`).** Real 82 keys on secp:
  cubic-residue concentration of pairwise X-differences at the **98.4th percentile, p≈0.033** vs a
  matched-key null; on non-CM E' they are typical (67th). Labeled *"CM-driven… a j=0 curve fingerprint,
  **not a d-fingerprint**."*
  → **Q4 flag (half-truth demotion).** Random keys on secp are **also** null (mean 3274) — so the anomaly
  needs the **real keys AND** the CM curve. It is a **joint (keys × CM-curve)** property — precisely the
  "joint property of the set" CLAUDE.md names as the only thing that survives the scramble. "CM-driven,
  not a d-fingerprint" states one leg and drops the other. **Re-test:** (i) what does the **constructed
  known-MT set** give on secp for E3? (separates key-structure from bit-length-pipeline structure — the
  `test_on_both_sets` discipline was not applied here); (ii) is the effect stable across sibling diffset
  statistics, or a 1-in-N pop? (iii) if it is genuinely (real-keys × j=0), that is a curve-conditioned
  key structure, not a closed avenue.

### Cluster γ — sub-detection leads demoted by a low-power gate
- **S5 — the cside `pow7` pooled tilt (`RESULT_cside_pooled_tilt_settlement_v1` §5).** Z_pool = **−2.73,
  calibrated p=0.0058, Holm-significant** over the secondary family, 18/28 negative — demoted "not
  promoted" by a **two-fold OOS AND-gate** (one fold significant, one null).
  → **Q4 flag.** A two-fold AND-gate has **structurally low power against a sub-detection effect** (a
  weak-but-real signal is *expected* to clear one fold and miss the other), so "OOS FALSE" does not
  separate "no effect" from "real but weak". **Re-test:** the properly-powered form the inv-map got —
  permutation pooled p over **more primes / more folds combined by pooling, not AND** — before this is a
  null. *(Note: the primary `inv` tilt was legitimately settled to null under a proper permutation pooled
  test; `pow7` did NOT get that treatment.)*

- **S6 — the χ₃ weight-1/2 sub-threshold tilt (M20).** Combined **p≈0.08** at small n, "washed out at
  larger n (pR 0.31–0.55) — resolved, not a signal."
  → **Q4 flag (washed-out without a power check).** A p≈0.08 that fails to confirm at larger n could be
  real-but-sub-detection if the larger-n statistic **lost power** on the small effect. **Re-test:**
  confirm the larger-n readout retained ≥80% power against an effect of the small-n size before "resolved".

### Cluster δ — a real diffuse effect, de-localized then dropped
- **S7 — the sub-Rayleigh deficit (`feedback_wrong_null_shared_by_controls`).** The **locus** was a
  wrong-null artifact (correctly caught). But *"the AGGREGATE ~−0.1% **survives** (REAL but DIFFUSE, no
  locus)."*
  → **Q3 flag.** A real diffuse deficit is a **magnitude**, not "no structure" — it has a symmetry type
  even without a locus. **Re-test:** characterize the −0.1% aggregate against the **symmetry-matched**
  null (which was the fix that killed the *locus*): is the diffuse residual isotype-structured?

### Cluster ε — retracted σ-shadows: check for matched-null residual
- **S8 — retractions #6 / #15 (the 6–7σ and 5.80/5.33/7.91σ shadows).** Retracted as μ₆/μ₂ null-mismatch;
  #15 *"collapses to z ∈ [−1.05, 2.34]"* against the matched null.
  → **Q2/Q3 flag (low priority).** The retractions are *directionally correct* (matched null is the right
  fix). But 2.34 is not 0, and "collapses to a range" is not "collapses to null". **Re-test (cheap):**
  confirm the matched-null residual across readouts is centered at 0 with no systematic sign, i.e. the
  +2.34 is a genuine 1-in-N and not a residual lean (the exact miss that the R3 autocorrelation 1.5σ was
  in the 2026-08-02 evidence).

---

## 4. Appendix-A "perfect nulls" — the Q1 sweep (systematic, not yet done)
Appendix A of the master lists ~20 scoped empirical nulls. The `test_on_both_sets` note already found
**one** ("the exposed-pubkey relations null had NO firing control and was uninformative"). The Q1 pass —
**for each Appendix-A null, did the sweep throw off any cells to chase, or was it suspiciously clean?** —
is **the systematic half of this audit and is NOT yet done**. It is the natural continuation: walk the
~20 nulls, flag every one that came back perfect.

---

## 5. Worklist (ranked; a list is the decision — work top-down)
1. **S2** — re-test the #1 lead with a non-saturating separation statistic (isotype/frequency-support of the joint readout). *[the master already set this up, "NOT YET RUN"]*
2. **S1 / S3 / D2** — run the Lang-torsor twist bridge (D2); pushes S1 and the reinstated cover-lever together.
3. **S4** — E3 on the constructed known-MT set + sibling-statistic stability (cheap, real-keys, high interest).
4. **S5** — pow7 pooled OOS by pooling not AND-gate (cheap).
5. **S6, S7, S8** — the power-check / diffuse-characterization / residual-lean re-tests (cheap).
6. **§4** — the systematic Q1 sweep of all Appendix-A nulls.

**Every re-test's spec → `experiment-designer` prereg first (mandatory). Grade every outcome. A
recovered signal faces the full finds bar (matched null sharing forced symmetries, firing control, OOS,
exact arithmetic). Promoting a false positive here is acceptable; it dies at that bar. A perfect null
that dodged the bar is the thing we are hunting.**
