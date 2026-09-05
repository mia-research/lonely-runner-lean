# RULES AUDIT — which project rules shut down enquiry, and are their conclusions correct?

**Date:** 2026-07-30. **Scope:** root `CLAUDE.md`, `btc_puzzle_investigation/CLAUDE.md`,
`memory/MEMORY.md`, the 23 `feedback_*` memories. **Not** a finding about the curve — nothing
here moves a grade on any curve claim.

**Criterion (decidable).** A rule is flagged only if BOTH hold:
1. it terminates a line of enquiry (bans a topic, bans a conclusion, or mandates a frame), AND
2. the *stated justification* is wrong, unverified, or self-contradicting against another rule.

A categorical rule with a correct object-level justification is not dogma — it is a theorem with
an imperative mood. Those are listed in §7 and kept verbatim.

**Trigger for this audit.** Two load-bearing statements in `PROJECT_SUMMARY_secp256k1_v1.md`
failed scrutiny the same way: neither was computed. Retraction 9 ("no reduction in hand") filed a
refutation as an absence of proof; "DLP-cost" used a cryptographic label in place of an operation
count (the object is `Θ(n)`, not `√n`). Both are *termination speech-acts with no artifact behind
the number.* The audit primitive that catches them is not lexical — it is: **for each
load-bearing quantitative or closure claim, name the artifact that computed it.** Applied to the
rules themselves below.

---

## §1 — `feedback_no_prng_generation_side_2026_07_14` ★ STRONGEST FINDING

**Status: the RULE is legitimate. The JUSTIFICATION is a closure the ledger already retracted.**

The memory says the generation side "**says nothing about the curve**", "reveals nothing about
the curve", is a "waste of time", and closes with:

> "If a generation-side idea seems relevant, it is not — drop it."

Three defects, each decidable:

**(a) It contradicts the OVERRIDE file it is supposed to enforce.**
`btc_puzzle_investigation/CLAUDE.md` states the same boundary correctly:

> "We do not study how the puzzle integers were selected (the PRNG / generation mechanism) — a
> deliberate research-interest boundary, **not a claim it is uninformative.**"

The CLAUDE.md version is a scope choice (guidance). The memory version is a scope choice plus an
unearned closure (dogma). They disagree, and the memory is the one loaded into context by recall.

**(b) The load-bearing phrase is a retracted move.** Retraction 42, in the same project's ledger:

> 42. the `E3` "unliftable ceiling / no control can move it / **says nothing about the curve**" →
>     RETRACTED (null→closure failure mode); interpretation is OPEN.

The exact phrase carrying this memory's justification is on the retraction list as an instance of
the null→closure failure mode.

**(c) It fails the project's own closure-grade bar.** Per `feedback_closure_grade_2026_07_28`,
writing that an avenue is uninformative requires OBJECT + CLASS of observable/algorithm + POWER +
SCOPE. "Reveals nothing about the curve" names none of the four.

**(d) The last sentence is unfalsifiable by construction.** *"If a generation-side idea seems
relevant, it is not"* instructs the reader to discount the evidence of relevance. This is the only
sentence in the corpus that pre-empts its own counterevidence.

**Proposed reframing — keep the boundary, delete the closure.**
- KEEP: the boundary itself, at full strength. It is the user's research-interest call, stated
  repeatedly and emphatically, and it does not need a mathematical justification to be binding.
  A scope decision is not a claim.
- DELETE: "says nothing about the curve" / "reveals nothing about the curve" / "waste of time" /
  "if it seems relevant, it is not."
- ADD the carve-out that (b) implies: a joint-SET property is **out of scope, not refuted.**
  Record it with its grade and move on; do not discard it and do not cite the boundary as evidence
  against it. (`RESULT_diffset_cubic_v1.md`'s E3 is the live instance — a joint property of the
  pubkey set, pre-registered reject at nominal `p≈0.033`, non-significant at Bonferroni ×7,
  interpretation OPEN per retraction 42.)

---

## §2 — `feedback_conditional_negatives_phrasing` ★ BLOCKS TRUE NEGATIVES

**Status: correct for search-based negatives. Wrong for refutation-by-counterexample.**

The rule bans, unconditionally: `closed, settled, resolved, definitive, flat, dead, ruled out,
no leak`, and "never … 'is not' / 'impossible' / 'nothing'". Every null must be bound to
method + sample + floor.

That is right for a negative resting on a **failed search**. It is wrong for a negative resting on
an **exhibited witness**, and the difference is not cosmetic:

| negative type | evidence | correct grade | correct phrasing |
|---|---|---|---|
| failed search | no hit at floor `ε`, power `P` | scoped null | "not observed under T, sample S, floor ε" |
| exhibited counterexample | a witness object | `[PROVED]` | **"is FALSE"**, flatly |

A refutation-by-counterexample is a *positive result wearing a negative sentence*. Hedging it
into "not observed under this method" is not caution — it is a downgrade of a proof to a null, and
it destroys the content.

**This is not hypothetical — it is the R9 defect, and the rule would reproduce it.** Retraction 9
files `"no concentration ⟺ ECDLP hard"` as "withdrawn (`⟹` has no reduction in hand)" — i.e. as an
absence of proof. Worked on the objects, **both directions are false by example**:
- `flat ⇒ hard` is FALSE — a small-embedding-degree curve has the same square-root cancellation in
  every complete character sum and a subexponential DLP via Frey–Rück/MOV. (The record already
  uses MOV as this reference point in retraction 32.)
- `hard ⇒ flat` is FALSE — GLV `μ₆` **is** concentration, exact and not statistical: the readout
  is constant on `{±d, ±λd, ±λ²d}` (C.1's M16 barrier, phase-rigid to std 0.000), on a curve
  believed hard, for a `√6` constant factor.

Under this rule as written, neither sentence above may be written in its true form.

**(e) It also now contradicts a later, better-reasoned rule.** `feedback_closure_grade_2026_07_28`
replaced the ban with **fill-or-downgrade**: a closure is *permitted* if it names object + class +
power + scope. `conditional_negatives` is a hard word-list ban. The two disagree; closure_grade is
later and is derived from worked examples.

**(f) The same patch has already been applied elsewhere, and skipped here.** `COUNTERPRIOR…v1.md`
patch P2 moved `feedback_negative_bias` from a word list to a sentence-function trigger, on the
grounds that both 2026-07-28 errors used words *not on the list*. `conditional_negatives` is the
other word-list rule and never received P2.

**Proposed reframing.**
- KEEP: the whole rule for search-based negatives — method + sample + floor is the content.
- KEEP: **"CLAUDE DOES NOT CLOSE FINDINGS — THE USER DOES."** This is an authority rule, not an
  epistemics rule, and it stands. Scope it explicitly to *findings*: it does not extend to
  mathematical refutations, which are results, not adjudications.
- ADD the counterexample carve-out (table above): a negative with an exhibited witness is
  `[PROVED]`, is stated flatly, and takes no hedge. Name the witness in the same sentence.
- REPLACE the word list with closure_grade's fill-or-downgrade, per P2.

---

## §3 — `feedback_curve_positive_framing_2026_07_14` ★ MANDATES TRUST IN A DEGRADED DOCUMENT

**Status: the framing half is correct. The "trusted frame" half is the mechanism that hid the
frontier liquidation.**

The rule says:

> "Lead from `POSITIVE_FINDINGS_HANDOVER_v3.md` in the first instance — the user has already
> filtered negative bias out of that corpus, so **treat it as the trusted frame**."

**Object-level problem.** `DEGRADATION_AUDIT_H3_TO_MASTER_v1.md` (and
`feedback_verify_external_critiques_2026_07_17`) found that **H4 deleted 4 of H3's 5 live
frontiers and the master dropped the 5th — live frontiers 5→0** — and that *tag-count audits
cannot see this* because the master retained a stale panel list that kept the token counts flat.

So the instruction "treat the positive-findings document as the trusted frame" is precisely the
instruction under which frontier deletion passes unexamined: if the lead document is trusted, its
**omissions** are invisible. Trust is the wrong primitive for a document whose known failure mode
is silent subtraction.

**(g) It also contradicts a standing rule.** `feedback_verification_claim_needs_artifact_2026_07_24`
— *a document cannot witness its own audit* (the COMPENDIUM_v1 defect). "Treat as trusted" asks a
document to do exactly that.

**(h) The pointer is stale.** `POSITIVE_FINDINGS_HANDOVER_v3.md` is not the current lead; the
lineage runs through `POSITIVE_FINDINGS_MASTER_v4.md` to `PROJECT_SUMMARY_secp256k1_v1.md`.

**Proposed reframing.**
- KEEP, unchanged: do not editorialize with security-negative framing ("the wall", "ECDLP-secure",
  "no key leak"). That correction is real, is the user's, and is well-evidenced as training-reflex
  leakage. Keep fence→gate.
- REPLACE "trusted frame" with: lead from the positive corpus **for framing**; the *frontier list*
  is load-bearing and must be diffed against its predecessor (`compile-diff`, already mandatory in
  root `CLAUDE.md` §2) before being leaned on. Framing is inherited; content is verified.
- UPDATE the pointer to the current lineage.

---

## §4 — `feedback_anomaly_drill_protocol_2026_07_17` — body fixed, headline still dogma

**Status: §4c landed correctly. The description line did not get the patch.**

The body now carries the symmetric burden (§4c): *"A null used to CLOSE is itself a claim; it takes
the closure-grade, a matched null sharing forced symmetries, and a fired control."* That is the
right construction and it resolves P3.

But the `description:` frontmatter — **the line that actually propagates**, since it is what recall
surfaces into a future session's context — still reads *"output is a characterization …, **never a
verdict**"*, and line 27 still lists flatly *"Banned conclusions: safe/generic/benign/tautological/
obstructed/at-the-floor-therefore-…"*.

So the graded rule is in the body and the categorical ban is in the headline. A session that reads
only the index sees the dogma.

**Proposed reframing.** Align the description with §4c: *never an **ungraded** verdict; a closure
is permitted at the closure-grade bar (object + class + power + scope) and takes the symmetric
checks.* Same edit to line 27 — reframe "banned conclusions" as "conclusions requiring the closure
grade".

---

## §5 — root `CLAUDE.md` §2b — a quantitative claim with no artifact

> "Instruction-based correction has a measured track record on this project of ~0."

This is the same defect class the audit was triggered by: a number stated as **measured**, with no
artifact naming the measurement. It is load-bearing — it justifies the entire four-agent
architecture — and read literally it implies the 23 `feedback_*` memories are worthless, which
would license deleting the corpus this audit is reviewing.

It is also self-undermining: if instruction-based correction has a track record of ~0, §2b is an
instruction.

Note this may well be **true**. The `self_cert_words` recurrence (a session violating that memory
while writing the ban into a document) is a real, documented instance. The objection is to
"measured … ~0" as a computed figure with nothing computing it.

**Proposed reframing.** Either (a) produce the artifact — the list of feedback memories with a
dated recurrence instance for each, which is a half-hour grep and would make the claim genuinely
load-bearing — or (b) restate as: *"several documented recurrences, including `self_cert_words`
being violated by the session writing it; instruction alone has not been sufficient."* Same
fill-or-downgrade the corpus applies to every other claim.

---

## §6 — Structural: a mandatory gate with no unavailable-branch

`experiment-designer` is a **mandatory** pre-data gate (root `CLAUDE.md` §2). Per
`AUDIT_prereg_incomplete_shortscalar_SELFAUDIT_v1.md` it failed twice — org access disabled, then
weekly limit — and **arms are held indefinitely**.

The precedent invoked there is correct and should stand: *"a run that did not complete is a run
that did not happen, not a run that passed."* What is missing is the branch for **gate
unavailable**, as distinct from gate failed. Without it, an infrastructure outage converts a
quality gate into an open-ended moratorium on enquiry — enquiry-shutting by accident rather than by
doctrine, but with the same effect.

### RESOLVED 2026-07-30 — user decision

**Policy adopted: provisional run, gate owed.** Written into root `CLAUDE.md` §2a. Arms may run
under `[PROVISIONAL — <gate> unavailable]` subject to four conditions (grade-slot tag; self-audit
with its uncovered sections named; gate recorded as owed with attempt date and failure reason; no
grade promotion until it clears). The branch covers **infrastructure, never inconvenience**.

**Refinement carried into the policy — what a self-audit can discharge.** §2b names *context
isolation* as the mechanism. The 2026-07-29 self-audit is evidence about that claim: with no
isolation, it found a severe power defect in the spec it was auditing. So isolation is load-bearing
against **frame** errors (a spec presupposing its answer) and buys nothing against **mechanical**
errors (a simulator or grep decides; the frame cannot corrupt the number).

| layer | sections | self-audit sufficient? |
|---|---|---|
| mechanical | statistic, power, exactness, plant-fires | yes, with the artifact |
| frame | object/disjointness, matched-control adequacy, scope, falsification, pre-commitment | no |

A `[PROVISIONAL]` tag must name which frame layers went unaudited.

**Correction to the self-audit's coverage claim.** It lists §1 (object) as covered. §1 is a *frame*
layer — disjoint construction is exactly the retraction-24 tautology trap. §2 and §5 are genuinely
discharged; **§1 moves to the uncovered list.**

### ⚠ The short-scalar arms do NOT lift under this policy

This resolves the *infrastructure* blocker. It does not resolve the *spec* blocker, and the two were
being conflated. The short-scalar hold rests on a **found defect**, which is the gate-FAILED case,
not gate-unavailable: `T_dev` saturates at ≈0.19 power while the demoted per-law test reaches 0.98
at `δ=0.05`. A found defect blocks regardless of gate availability.

Completion condition for that hold — executable, no agent required:
1. Invert §2 (per-law `G_ℓ` permutation + Holm over 4 laws as PRIMARY; `T_dev` demoted to
   characterization), re-issue as `PREREG_incomplete_shortscalar_v2.md`.
2. Run the ≥10⁴-rep calibration of whichever statistic ends up primary (the two existing runs
   disagree: FPR@.05 of 0.0493 vs 0.074, ≈3σ apart).

---

## §7 — Checked and NOT flagged  *(stating the clean result plainly is a valid output)*

Listing these matters: a review that flagged everything would be manufacturing.

| rule | why it survives |
|---|---|
| **NO FLOATING POINT** (btc `CLAUDE.md`) | Categorical, and correctly so. The justification is object-level and exact: IEEE double has a 52-bit mantissa; every puzzle key with `N>53` loses the low bits where `D` lives. Enforced by `check_no_float.sh`. A categorical rule with a proof is a theorem. **Keep verbatim.** |
| `feedback_residue_vs_component_tautology` | Categorical ban, backed by a specific measured artifact (spurious MI `z≈+5000` that the shuffle control cannot expose). Justified. |
| `feedback_closure_grade_2026_07_28` | This *is* the anti-dogma layer. Fill-or-downgrade, with explicit GUARDs against manufacturing positives and against banning scoped nulls. Well constructed. |
| Counter-prior (btc `CLAUDE.md` Statement of intent) | Correctly separates "prior on the existence of a target" from "prior on any candidate", and does not lower the bar on finds. |
| `feedback_proof_not_test` | Upward grading discipline; the downward half now exists in closure_grade. No conflict. |
| `feedback_no_local_agents`, `feedback_versioning` | Operational preferences. The user's call; no enquiry claim attached. |
| `feedback_wrong_null_shared_by_controls` | Object-level and specific. |

---

## §8 — The pattern across §1–§5

Four of the five content findings share one shape: **a legitimate instruction with an illegitimate
justification bolted on.** The instruction is the user's to make (scope, framing, authority) and
needs no defence. The justification is a mathematical claim that was never checked, and it is the
justification — not the instruction — that does the enquiry-shutting, because a scope boundary lets
you record an out-of-scope fact while a closure makes you discard it.

The generalizable repair: **separate the imperative from the warrant.** Where the user has made a
call, state it as a call. Where a claim is doing work, it takes a grade like any other.

---

## §9 — Gate on acting on this

I have not edited any memory. Root `CLAUDE.md` §2b makes `memory-drafter` **mandatory** before
writing or revising any `feedback_*` memory, and here the gate's stated mechanism — context
isolation — genuinely applies: I formed these views, so I am the wrong reviewer of my own patches.

The **audit** above did not need isolation, because every finding rests on a decidable artifact
(retraction 42's text, the CLAUDE.md/memory contradiction, the H3→master frontier count, the
closure_grade/conditional_negatives conflict) rather than on a judgment. The **patches** do need
it.

Recommended order:
1. §1 and §2 first — they are the two that actively cost work.
2. §3 and §4 are text realignments to rules whose bodies are already correct.
3. §5 is a half-hour grep that either upgrades a claim or downgrades it.
4. §6 needs a decision from the user, not an agent.
