# Math Ex Project — Claude Instructions

These OVERRIDE default behaviour for this project. Most important rules first.

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

Trust-but-verify: a subagent's summary is what it intended to do, not always
what it did. After a subagent writes or edits, spot-check the diff.

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
