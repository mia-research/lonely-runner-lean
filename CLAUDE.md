# Math Ex Project — Claude Instructions

These OVERRIDE default behaviour for this project. Most important rules first.

## Driver: substrate independence

**`~/.claude/CLAUDE.md` §0 is the overarching driver and governs here.** In short: a
construct carried across disciplines gets a **verification demand** (exhibit the
isomorphism -- which state space, which constraints, is it additive) and never a **type
objection** ("entropy is physical, that is a metaphor"). Mathematics is the substrate;
thermodynamics is substrate-independent mathematics discovered in heat engines, not a
theory about them. Lineage and citations live in the canonical file -- do not restate
them here, and do not let this file drift from it.

In this project specifically:

- The LRC proof runs on measure and equidistribution arguments. Equidistribution is a
  maximum-entropy statement over a state space, and Theorem 5.2's CRT measure
  factorisation is a counting result before it is a measure-theoretic one. Framing them
  that way is legitimate and usually clarifying, not a loosening of rigour.
- When delegating a second opinion, ask the subagent **which axiom of the mapping fails**,
  not whether the analogy is "valid". The second phrasing invites a type objection back.

---

## 0. Tooling: Claude Code only

**No local LLM agents.** Qwen, DeepSeek, Gemma, and Codex subagent scripts
(`tools/qwen_subagent.py` etc.) are retired. Do NOT invoke them. Use Claude Code
primitives: built-in subagents, the lean4 plugin, the bundled `code-review`
skill, and MCP servers. Historical `[Qwen|DeepSeek|Codex] says:` checkpoint
lines in memory are archival — do not produce new ones.

## 1. File access discipline

- Proof files (`lrc_proof_v*.md`, `lrc_n11_ap_paper_v*.md`) are large. **Never
  Read the whole file** to answer a question about one section — use
  `offset`/`limit` or grep for the section heading first.
- **Never paste proof content inline** in conversation. Read → Edit in place →
  done. The diff is the artefact.
- **For proof status questions**: read `memory/MEMORY.md` and
  `memory/lrc_proof_status.md` only, not the proof file itself.
- **Versioning is mandatory** — never overwrite a `.tex` / `.md` paper or
  report file. Save as next version (e.g. `lrc_proof_v11_9.md` →
  `lrc_proof_v11_10.md`). The Lean tree (`LonelyRunner/*.lean`) is the
  exception: edit in place, commit per change.

## 2. Subagent routing (Claude Code built-ins)

Default to the main conversation. Delegate when the work would flood context or
needs an independent eye.

| Situation | Use |
|---|---|
| "Where is X defined?" / single file lookup | Direct `Read` / `Grep` via Bash |
| Codebase search spanning 3+ queries, naming variants, or directories | `Agent` with `subagent_type: Explore` (read-only, Haiku, fast) |
| Designing a multi-step implementation strategy | `Agent` with `subagent_type: Plan` (read-only research) |
| Open-ended investigation with reads + edits + multiple tools | `Agent` with `subagent_type: general-purpose` |
| Reviewing the current diff for correctness | bundled `code-review` skill (`/code-review`) — fresh-context reviewer |
| Independent second opinion on a proof section, plan, or refactor | `Agent` with a self-contained prompt: state the claim, what to check, what counts as a finding |
| Routine prose/threshold/dedup checks | inline in the main conversation — no special agent needed |
| **A claim rests on a citation** (`[CITED]`, `[PROVED\|KS]`, any literature bound) — **mandatory before a grade moves up on a citation's strength** | **`citation-verifier`** |
| **Promoting any consolidated / handover / master / summary document** — **mandatory, before promotion** | **`compile-diff`** |
| **ECC work only** (`btc_puzzle_investigation/`, `secp256k1_arithmetic/`): **before running any leakage test, sweep, scan, or anomaly drill** — **mandatory, pre-registration**. Not for LRC or any other work (owner: *"you don't need prereg, that was just for the ECC work"*, 2026-09-24; *"prereg is only for ecc work"*, 2026-09-26) | **`experiment-designer`** |
| **Writing or revising any `feedback_*` / `project_*` memory** — **mandatory** | **`memory-drafter`** |

Trust-but-verify: a subagent's summary is what it intended to do, not always
what it did. After a subagent writes or edits, spot-check the diff.

### 2a. When a mandatory gate is UNAVAILABLE  *(decided 2026-07-30)*

A gate that cannot run must not become an open-ended moratorium. Distinguish two
cases — they are not the same and only one licenses proceeding:

- **Gate FAILED** (it ran and reported a defect) → the defect blocks. Fix it.
- **Gate UNAVAILABLE** (it could not run at all — org access, rate limit,
  outage) → the work may proceed **PROVISIONALLY**, under all four conditions
  below. The standing precedent is unchanged and still governs the *failed*
  case: *a run that did not complete is a run that did not happen, not a run
  that passed.*

**Conditions for a provisional run — all four, or the hold stands:**
1. Tag every output `[PROVISIONAL — <gate> unavailable]`. Not a footnote; in the
   grade slot, where a reader looks for the grade.
2. Attach a self-audit that names its own **uncovered** sections explicitly.
   Absence from a self-audit is not clearance.
3. Record the gate as **owed**, with the date it was attempted and why it failed.
4. **No grade promotion** until the gate clears. A provisional run produces
   evidence; it cannot move a claim up a grade.

**What a self-audit can and cannot discharge.** §2b names *context isolation* as
the mechanism. Isolation is load-bearing against **frame** errors — where a spec
quietly presupposes its answer — and buys nothing against **mechanical** errors,
where a simulator or a grep decides and the frame cannot corrupt the number.
Evidence (2026-07-29): a self-audit with no isolation found a severe power defect
in the very spec it was auditing.

| layer | pre-reg sections | self-audit sufficient? |
|---|---|---|
| **mechanical** | statistic, power, exactness, "does the plant fire" | **yes**, with the artifact |
| **frame** | object/disjointness, matched-control adequacy, scope, falsification, pre-commitment | **no** — isolation is the mechanism |

A provisional run therefore carries the most risk on the frame layers; the
`[PROVISIONAL]` tag must name which of them went unaudited.

**This branch covers infrastructure, never inconvenience.** "The gate is slow /
I am confident / the spec is simple" is not unavailability.

### 2b. The four specialist agents — why they exist and the rules that bind them

Defined in `.claude/agents/`. Rationale and evidence:
`btc_puzzle_investigation/AGENT_DESIGN_ANALYSIS_v1.md`.

**The premise.** There are 17 `feedback_*` memories, each precisely describing a
failure mode. **Every one of those failure modes recurred anyway** — including
`self_cert_words` being violated by the same session that was writing that very
ban into a document. Instruction-based correction has a measured track record on
this project of ~0. These agents are **not** "the same work done more carefully."
A subagent made of this model has this model's prior. They work only because of
two structural properties, and **if either is dropped, expect the failure to
return**:

1. **Decidable artifact.** Each agent emits a script, diff, count, quote, or spec
   — never a judgment. "This looks overclaimed" is not a finding; "the claim's own
   script grades it CITED, the document says PROVED" is.
2. **Context isolation.** Never hand an agent the session narrative or the
   document's framing — only the raw material plus the criteria. The frame is
   invisible from inside; isolation is the mechanism, not care.

**The refinement that matters: mechanical is not enough — it must be OBJECT-level.**
A tag-count audit of the master was mechanical *and wrong*: it reported the
document healthy (more `[PROVED]` tags than its source, same `[HEURISTIC]`) while
five open frontiers had been liquidated, because a stale panel list kept the token
counts flat. It measured a **proxy**. Every agent must name the object it tracks
and check that object — never a correlate. Any number an agent emits must name
what it counts and list the misses individually.

**Do NOT build a general adversarial reviewer.** An external model asked to find
overclaiming produced four confident, well-structured, entirely false findings —
while being right in thesis. §3 already names this: *reviewers asked for issues
will manufacture them*. Every agent above is therefore instructed that it is **not
scored on problems found**, and that a clean result stated plainly is a valid
output.

**Refuting a mechanism ≠ refuting a claim.** When an agent (or a critique) is wrong
in its particulars, that says nothing about its thesis. Check the two separately,
thesis first.

## 3. Verification pattern (use before declaring "done")

Adapted from Claude Code's "give Claude a check it can run" principle and the
Writer/Reviewer pattern.

1. **Define the check up front.** For Lean: `lake build` exits 0 *and*
   `#print axioms <decl>` shows only the expected axioms. For analytical
   proofs: an explicit list of claims to verify + a numerical witness script if
   applicable. For empirical claims: a brute-force or independent-sampler
   script.
2. **Implement** in the main conversation or via a subagent.
3. **Adversarial review** in a fresh context: spawn a subagent with only the
   diff/section and the criteria. Tell it to "report only gaps that affect
   correctness" — reviewers asked for issues will manufacture them. The
   bundled `/code-review` skill does this for code diffs.
4. **Iterate** until the check passes. Show evidence (build log,
   counterexample search result, test output), not assertions.

For sustained autonomous runs, set the check as a `/goal` so Claude keeps
working until it holds.

## 4. Lean 4 workflow (lean4-skills plugin)

Plugin installed at user scope (`lean4@lean4-skills`). Lean tree:
`LonelyRunner/`. Build: `cd LonelyRunner && lake build`.

**Slash commands (all `/lean4:<name>`):**

| Command | Use when |
|---|---|
| `/lean4:learn` | Exploring mathlib or learning a tactic |
| `/lean4:draft` | Skeleton-only formalization of an informal claim |
| `/lean4:formalize` | Draft skeleton + guided prove cycles, statements editable |
| `/lean4:autoformalize` | Autonomous, with a stop budget |
| `/lean4:prove` | Fill sorries; declaration headers frozen |
| `/lean4:autoprove` | Unattended sorry-fill loop (max cycles / wall-clock / stuck) |
| `/lean4:review` | Read-only quality review |
| `/lean4:refactor` | Pull mathlib, extract helpers, simplify |
| `/lean4:golf` | Shorten / clarify proofs |
| `/lean4:checkpoint` | Per-file + project build, axiom check, commit |
| `/lean4:doctor` | Diagnostics |

**Canonical session flow:**
`draft → prove → review → refactor → golf → checkpoint → git push`

**MCP**: `lean-lsp-mcp` is configured (user scope). Gives sub-second goal /
mathlib search / multi-tactic-attempt feedback instead of 30s+ `lake build`
cycles. Tools include `lean_goal`, `lean_local_search`, `lean_loogle`,
`lean_multi_attempt`, `lean_hammer_premise`, `lean_diagnostic_messages`.

**Decompose proofs into small lemmas.** Targets that fit in a single agent
context (~300 lines, no auto-compaction) get higher effective thinking budget
and lose less to compaction. Whole-proof autoformalize attempts burn tokens.

## 5. Math research workflow (n-LR proof work)

**Source-first. Read the paper's argument for THIS step before anything else.**
We are *verifying a published proof* (BHK 2001 = `/tmp/bhk.txt` / `bhk_2001.pdf`;
Bienia, Renault, Barajas-Serra likewise). The argument for the exact lemma/case
is in the paper — find it (grep the Case/Lemma/Table number, read it, transcribe
it) and try it BEFORE any empirical de-risk, investigation, or invention. Three
separate times a "hard/research-grade" obstacle dissolved the moment the paper's
own treatment was read (e.g. (1,±2) → BHK Cases 5.2.9/5.2.11, a plain pigeonhole).
De-risk scripts and structural sweeps come AFTER the source, and only for the
gaps the source genuinely glosses — not as the first move.

**No editorializing — state facts, not difficulty verdicts.** Do not label steps
"research-grade", "hardest piece", "biggest chunk", "huge", "great news", or rank
difficulty before (or after) doing them. Those value judgments are predictions
dressed as facts; they have repeatedly been wrong and they distort the
perspective on the actual work. Report only what the source says and what a build
/ script / `#print axioms` actually verified.

**Plan-first for non-trivial proof steps.** Enter plan mode (`Esc` → plan
mode), let the Plan subagent gather context, draft the approach, edit it with
Ctrl+G if needed, then exit and implement.

**Investigation > sharpening.** The methodology memory in `memory/MEMORY.md`
section "Understand Exceptions + Apply Translation Lens" is load-bearing — read
it at the start of any proof session. The two compounding failure modes
(sharpen-and-narrow; direct-only check) cost us the v11.7→v11.9 cascade.

**Empirical ordering — AFTER the source.** Once the paper's argument is in hand,
if a general-n structural question remains, run a diverse-sampled empirical sweep
to identify the order needed (pairwise / k-wise). Lexicographic iteration
biases — shuffle + per-G caps. Empirical sweeps confirm or fill the source; they
do not replace reading it.

**Adversarial review at section level.** Before promoting a proof section
("draft" → "proved"), spawn an independent subagent with only that section and
ask: "What would have to be true for this to be wrong? List concrete attacks."
Treat its findings as candidates, not verdicts.

## 6. Pipeline workflow (LRC claim adjudication)

```
Formalization packages → /reports/formalization/CLAIM-LRC-XXXXXX/
Quorum votes           → /reports/quorum/manual_votes/cycle_NNN/
Pipeline flags         → /reports/pipeline_flags/
Investigations         → /reports/investigations/
```

Numerical thresholds: **stable 1e-09**, **sensitive 1e-06**.

Source integrity: SHA-256 every claim.

## 7. Submission pipeline (pre-arXiv)

1. **Adversarial section sweep** — for every theorem/lemma in the target
   version, spawn a `general-purpose` subagent: claim + proof + criteria. Fix
   findings until clean.
2. **Diff review** — `/code-review` on the full version-vs-previous diff.
3. **LaTeX conversion** — `latex-document-skill` plugin if present, else
   manual: convert canonical `.md` to `.tex` with theorem/proof environments.
4. **Compile + visual review** — `pdflatex` (or `latexmk`), open the PDF,
   confirm equations and references render correctly. The Read tool can read
   PDFs.
5. **Citation + related-work sweep** — `claude-scientific-writer` plugin if
   present; otherwise inline verification of every `\cite{}`.
6. **arXiv upload** — manual; user uploads after filling SHA-256 and repo URL
   in Data Availability.

## 8. Current project state

- **Canonical general-n manuscript**: `lrc_proof_allN_v11_8.md` (latest on
  disk). The v11.9 Slot-Residue Theorem work lives in
  `lrc_v11_9_sr_proof_to_verify.md` + memory topic files — NOT yet folded
  into a manuscript version (no `lrc_proof_allN_v11_9.md` exists).
- **n=11 paper**: `lrc_n11_ap_paper_v30.md` FROZEN, preprinted Zenodo
  2026-03-27 — do not modify. The journal-submission LaTeX lineage
  (`eleven_lonely_runners_v3*.tex/md`, `ct-submission-v50/`) is separate
  and post-dates the freeze.
- **Lean tree**: builds clean (2703 jobs). **✅ n=6 LRC COMPLETE
  (2026-06-25)** — `#print axioms intLRC_six` = `[propext, Classical.choice,
  Quot.sound]`, zero `sorry`; the entire n=6 BHK proof (incl. `exc_open` and
  both Prop 11 cores) is formally verified, axiom-clean. The remaining Lean
  sorries (Weyl fine-cell, real-speeds reduction, n=7 hard case) are the
  general-n / other-small-n frontier and were never part of the n=6 work —
  see "Lean Formalization Status" in `memory/MEMORY.md`.
- **Naming conventions (v7+)**: Unit-Complete (not U-FORCE), CG1/CG2 (not Cond
  1/2), floor-reset event (not z=0 event).
- **✅ n=7 COMPLETE (2026-09-07)** — `#print axioms intLRC_seven` =
  `[propext, Classical.choice, Quot.sound]`, zero `sorry`, no `native_decide`.
  Barajas–Serra 2008 fully verified, §7 included. See §11 for the done-check.
- **No active frontier.** n=3,4,5,6,7 are done; the remaining Lean `sorry`s
  (`Theorem52_Weyl`, `Theorem121_Main`, `IntLRC_4_Bienia` Path B) belong to the
  general-n programme, not to any small-n closure.

## 9. Decisions Claude makes alone (no need to ask)

- Escalation calls, pipeline flags, dedup judgments
- Novel proof step proposals and structural architecture
- File I/O and pipeline state changes
- Choice of which built-in subagent to spawn

## 10. Decisions that need confirmation

- Anything that overwrites a versioned paper file (see §1)
- `git push`, force-pushes, branch deletions
- Modifying the Lean tree's `lakefile.lean` or mathlib pin
- Deleting files outside `archive/` or `logs/`

## 11. n=7 (Barajas–Serra) project

**Source = Barajas–Serra 2008**, *The Lonely Runner with Seven Runners*, EJC 15
R48 — on disk `sources_barajas_serra_2008.txt` (SHA-256 in
`docs/n7_bs/source_integrity.md`). This is a **Prime Filtering** argument with
`p=7` (7-adic valuation `ν`, position `q`/`r`, multiplier sets `Λ_j`) — a finite
residue-chasing proof, **structurally unrelated to BHK 2001**. Do NOT try to
reuse the n=6 BHK geometry; it does not transfer.

- **Status board: `docs/n7_bs/ROADMAP.md`** — the completion box at the top is
  current; everything below it is the pre-completion working record.
- **Done-check: `LonelyRunner/scripts/n7/gate.sh`.** Run it before trusting any
  change here. It purges cloud-evicted `.olean` files, builds the explicit module
  targets, inventories `sorry`, scans for `native_decide`/`unsafe`/`admit`, and
  runs the axiom check.
- **⚠ Plain `lake build` is NOT a gate.** `LonelyRunner.lean` imports only
  `LonelyRunner.Basic`, so the default target never enters `LRC/` and reports
  success (2485 jobs) without compiling n=6 or n=7 at all. The real target is
  `lake build LonelyRunner.LRC.SmallN.IntLRC_7` (3368 jobs). Historical
  "build clean, N jobs" notes predating 2026-09 did not exercise this tree.
- **The project sits under `~/Desktop`, which is iCloud-synced**, so build
  artefacts get evicted: a dataless `.olean` reads as `invalid header` while
  lake's traces still call it up to date. Gate step [0] handles it; expect
  recurrence.
- **`§7` (`m = 1`) is not in `Case_A5.lean`.** `five_avoid_m1` was deleted, not
  proved — the statement is false. `five_avoid`/`five_band` require `2 ≤ m`, and
  `m = 1` is handled in `Reduction.lean` jointly with `d₆` via `five_band_m1` →
  `m1_six_witness`. `bs_discrete_q` returns a general modulus `7·P` because BS
  resolve §7 at `N' = 98`, which is not a power of 7.
- **Module layout:** `SmallN/IntLRC_7_BS/`. Edit Lean in place, commit per
  change. Keep one heavy kernel `rfl` per module — `lake build` also emits C and
  overflows the elaboration stack where `lake env lean` does not.
- **No local LLM agents** (restates §0): `delegate`/`gemini`/`proof-check`/
  `model-status` skills exist in this environment but are FORBIDDEN — Claude Code
  primitives + the lean4 plugin only.
