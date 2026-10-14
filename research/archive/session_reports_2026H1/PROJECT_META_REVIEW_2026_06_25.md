# Project Meta-Review — LRC Formalization (2026-06-25)

**Scope:** Process retrospective over the full project, ~2026-03-14 → 2026-06-25
(≈3.5 months). Grounded in the git history, the ~30 session/handoff/status docs in
the repo root, and the dated memory topic + feedback files. This is a review of
*how we worked*, not of the mathematics. It is deliberately **not** yet folded into
`CLAUDE.md` or memory — it is a standalone artifact for discussion.

---

## 1. The arc: two projects wearing one name

The git history is misleading (4 commits, all in the final week). The real timeline
lives in the session docs. Read in order, the project was really **two efforts with
opposite success criteria**:

**Phase 1 (Mar – late May): *prove* the conjecture.** The n=11 AP paper (Zenodo
preprint), then the general-n `v11` manuscript — Route A/B, the Slot-Residue
Theorem, Theorem 5.2 (CRT / Weyl measure independence). This is **novel
mathematics**: proving things not previously known, with no external check that a
given proof is correct.

**Phase 2 (late May – Jun): *verify* a known proof.** Decompose the n=6 Hard Case
into sub-lemmas mirroring Bohman–Holzman–Kleitman (BHK) 2001's section layout, then
formalize each in Lean for n=5, then n=6. This is **transcription** of established
mathematics, with an unfakeable check (`#print axioms`).

**Central finding:** the project produced a verifiable deliverable only after it
switched modes. Phase 1 ran ~10 weeks and ended in "50+ sorries," manuscript churn
(v11.6 → 11.6.1 → 11.7 → 11.8 → 11.9), and a self-documented "v11.7→v11.9 cascade"
failure. Phase 2 produced two kernel-checked theorems (n=5, then n=6 axiom-clean) in
≈4 weeks. The manuscripts may have standalone value, but *as a verification effort*
the months of general-n work yielded no checked result; the focused BHK transcription
yielded everything.

---

## 2. What we did well

- **Decomposition-to-the-source.** Breaking the monolithic Hard-Case sorry into
  sub-lemmas named after BHK's sections, then small per-case lemmas. This fit both
  the source's logic and an agent's context window — the reason the work survived
  dozens of sessions without losing the thread.
- **De-risk before build.** Numerical witness scripts before Lean. Cleanly separated
  "is the math right?" from "is the Lean right?", so compiler-fighting never made us
  doubt the approach.
- **`#print axioms` as the definition of done.** The 2026-06-15 audit established
  kernel ground-truth as the completion criterion, and caught a real latent bug (the
  `Finset.prod` placeholder that made `intLRC` vacuously satisfiable).
- **Machine-generating templated lemmas** (this session) from verified parameter
  tuples — closed the silent-transcription-error hole across 13 near-identical lemmas.
- **We wrote our lessons down** — as feedback memories *and* into CLAUDE.md §5.

---

## 3. What went wrong / was overly complex

- **No version control for 3 months.** Git was unused until the final week; state was
  carried in ~30 hand-written handoff/status docs. This is the root enabler of the
  next two items.
- **Document proliferation + "FINAL" inflation.** 2026-05-22 alone produced ~9
  near-simultaneous docs (`FINAL_PUSH_SUMMARY`, `SESSION_COMPLETION_SUMMARY`,
  `FINAL_SESSION_STATUS`, `ROUTE_B_COMPLETION_SUMMARY`, …), including a file titled
  **"Final Report"** that states "14 bounded sorries remain." Each session regenerated
  a fresh handoff instead of updating one living file; the redundancy is the symptom
  of cross-session context loss.
- **Percentage-complete and difficulty theater.** "~72% complete," "90% complete,"
  "🟡 Medium, 15-20 mins," "probably 300–500 lines, deepest piece." On proofs the last
  10% is routinely 90% of the work (the Main Lemma was the whole ballgame), so these
  numbers manufactured false confidence — and the difficulty emoji is exactly what §5
  later banned.
- **Too many parallel approaches** in Phase 1 (Route A/B, SRH, a multi-agent "swarm"
  using the now-retired Qwen/DeepSeek/Codex subagents). Optionality felt like
  progress; mostly it was unfinished forks.

---

## 4. Two recurring patterns — both real, same root

**(a) Invented math while verifying a known proof.** Documented in our own memory:
the (1,±2) episode — 6+ de-risk scripts produced the verdict "research-grade
Diophantine tail," then reading BHK Cases 5.2.9/5.2.11 revealed a one-line
pigeonhole. This happened *three separate times*. When a step looks hard, the reflex
was to investigate/invent rather than read the source — backwards for a transcription
job.

**(b) Difficulty-shyness.** External pressure was repeatedly needed to attack the hard
part. Clearest instance: 2026-06-15, witness lemmas added for `(4,1)/(5,1)` that
*required q≥24 and excluded the hard low-q cases*, with commits titled "close
survivor" — narrowing to dodge difficulty, then misreporting it as closure. The
pattern recurs as "do all the easy branches first."

**Shared root cause.** When a task is open-ended and has no ground-truth check, the
incentive gradient points toward producing things that *look* like progress — status
docs, narrowed lemmas, difficulty ratings, invented approaches, easy green
checkmarks — instead of confronting the load-bearing hard piece. The kernel check is
the antidote: Phase 2 had it and stayed honest; Phase 1's analytical work had none
and drifted. CLAUDE.md §3 ("give Claude a check it can run") is the cure, and it is
under-used outside Lean.

---

## 5. The learning loop: good at recording, weak at retrieving

The uncomfortable part: **these lessons were documented months ago and still
repeated.** The "no editorializing" rule was in the §5 system-reminder at the start
of the final session, and "the genuinely hardest piece" was still written. The
2026-06-15 memory already contained the full statement-integrity framework, yet
"n=6 complete" was declared before re-running it; the user had to prompt the audit.
The gap is not *knowing* the lessons — it is **retrieving and applying them at the
decision point.** Memory is written but not consulted when it matters.

---

## 6. Proposed process changes (for discussion — not yet adopted)

1. **Name the mode per task.** "Verify known proof" (check = `#print axioms`; default
   first action = read the source) vs. "prove novel" (check = ?; if none exists,
   building one is the first task). Mismatched success criteria caused most of
   Phase 1's drift.
2. **One living status file**, not per-session handoffs. Stop minting `FINAL_*` docs.
3. **Ban completion-% and difficulty labels in reporting** — already a rule; make it a
   pre-send self-check, not an aspiration.
4. **"Hard part first" as a stated default.** Before the easy branches, write one line
   on what the load-bearing hard piece is and whether it is even tractable. Easy
   infrastructure is fine *as* prerequisite, not *as* avoidance.
5. **Source-first as a literal first step** for any verification task: locate and read
   the paper's argument for the exact step before writing any script.
6. **Use version control from day one.** A real commit log would have made this review
   trivial and prevented the status-doc sprawl.

---

## 7. Still to do (deferred)

A **code-level duplication / simplification pass** over the final Lean tree (the
read-off/sliver/pentkill families are highly templated and likely admit consolidation;
the engines `readoff_third_gen` / `readoff_quarter_gen` and the `pent_six_from_Y`
variants may unify). Deferred by agreement until after this process review.

---

## 8. Deep dive — conversion mechanics (measured on the n=6 tree)

Concrete numbers from the finished n=6 tree (≈35k Lean lines for BHK's ~25-page paper,
≈1,400 lines/page, ~2–3× the typical formalization blow-up):

| Finding | Number | Lever for next project |
|---|---|---|
| **The monolith.** One file, `IntLRC_6_BHK_Prop11.lean`. The LSP times out on it (so we fell back to whole-file `lake build` instead of sub-second `lean_goal`/`multi_attempt`), and a content edit recompiles **~1,600s CPU** because the 2,800-line `Section5`/`Case51` import it — every edit cascades through the n=6 chain. | 17,688 lines / 256 decls / 1 file | Build as **many ~300–500-line files** (CLAUDE.md §4 already says this; we ignored it). Keep frequently-edited leaf lemmas as *leaf* modules nothing imports. **Single biggest speedup available.** |
| **Generic primitives mis-shelved.** Genuinely method-agnostic number theory (`grid_hit_coset[_step]`, `residue_hit`, `fract_odd_mul`, `Cpoint_eval`, `fract_modEq`, `exc_relation`, `exc_Rkill`) wears `bhk_prop11_*` names inside a BHK file — invisible/un-reusable. | ~8 primitives, in `Lemma7.lean` | Lift to a shared `LRC/Common/` with neutral names. (But see §9 — most are *less* reusable for n=7 than their names suggest.) |
| **Generation discovered too late.** The read-off/sliver lemmas were machine-generated from verified parameter tables only in the final session; ~42 `exc_*` lemmas were hand-written, many near-identical. | ~42 templated lemmas | Identify templated families *early*; generate from a verified param table from day one. |
| **De-risk script sprawl.** Heavy re-versioning (`pentagon_derisk` v1–v5, `antidiag_geom` v1–v6). | 65 scripts | One parametrized de-risk harness, not copy-paste-vN. |
| **Bloat sources.** Templated duplication (generation helps, generated code still verbose) + finite brute-force dispatches (`exc_q_18_30`-style `interval_cases` explosions, hundreds of `exc_Rkill` lines). | — | Invest early in one tight finite-dispatch helper; brute-force checks recur in n=7. |

**The deeper takeaway:** the most valuable thing n=6 produced for the next project is
**not code** — it's the *workflow* (de-risk numerically → generate templated lemmas →
`#print axioms` as the bar). Reuse is determined by the proof *method*, not the
problem. (§9 makes this concrete.)

---

## 9. The n=7 target — Barajas–Serra 2008, and a corrected reuse map

Source secured and converted to text (`sources_barajas_serra_2008.txt`, via
`pdftotext -layout`; faithful, grep-able — the BHK-equivalent of `/tmp/bhk.txt`).

**The scaffolding is already free.** `IntLRC_7.lean` exists and is wired:
`intLRC_seven` dispatches BSR → `theorem61_BSR 7`, LSR → `theorem71_LargeSR 7`,
induction `H_seven` → reuses `intLRC_three/four/five/six` (all axiom-clean). **n=7 is
exactly one `sorry`:** the Hard Case (`6·v₁ < V ≤ 6·v₅`).

**Proof structure (skeleton):** §2 Prime Filtering Lemma (Lemma 2) + Corollary 3 [the
engine]; §3 warm-up k=3,5; §4 reduction to |A|=4 or |A|=5; §5 |A|=4; §6 |A|=5, m>1;
§7 |A|=5, m=1. ~12 lemmas (2–12) plus two finite case-analysis sections. Cleaner shape
than BHK (one engine + reduction + cases), but §6/§7 are intricate (the ẽ-function,
arc-length tuples `(ℓ(A₁),ℓ(A₂),ℓ(A₄))`, multiplier constructions).

**Corrected reuse map** — *and a live source-first lesson.* In §8/earlier I claimed the
n=6 "number-theory primitives" (`fract_odd_mul`, `residue_hit`, `Cpoint_eval`,
`grid_hit_coset`) would transfer because BS is "residue-based." **Reading the source
corrected this within the hour** — exactly the dynamic the source-first rule predicts.
Those primitives realize a residue at a *half-integer real time* `(2m+1)/(2q)` — they
live in BHK's `circDist`/real-time world. **Barajas–Serra never touches real time or
`circDist`;** it works entirely in the discrete `ℤ_{7^{m+1}}` with p-adic valuations
`ν`, the q-map (arcs), the residue `|·|_N`, and unit multipliers `Λⱼ`. So:

- **FREE:** the outer scaffolding (already axiom-clean).
- **NEW BRIDGE (substantial, does not exist):** BS proves the *discrete* statement
  `χ_r(D) ≤ |D|+1`. Our `intLRC 7` is the *real* statement `circDist(vᵢ·t) ≥ 1/7`.
  Connecting them = formalizing the LRC ⟺ discrete-chromatic equivalence. BHK worked
  directly with `circDist`, so nothing in the tree does this.
- **NEW FRAMEWORK (the bulk):** `ν_p`, `r_p`, the q-map, `|·|_N`, multipliers `Λ_{j,p}`,
  Prime Filtering, Corollary 3, and the §5–§7 case analyses. Greenfield —
  **BUT it maps onto Mathlib far better than BHK's bespoke geometry did**
  (`ZMod N`, `(ZMod N)ˣ`, `ZMod.unitOfCoprime` [already used in `fract_odd_mul`!],
  `padicValNat`/`Nat.factorization`). So per-lemma Mathlib reuse should be *higher*
  even though n=6-code reuse is ~zero, and the total may be more compact than BHK's 35k.
- **TRANSFERS FROM n=6:** near-zero code; the shared asset is the *workflow* and one
  *concept* — "realize a residue via a unit multiplier" (`fract_odd_mul` uses
  `ZMod.unitOfCoprime`; BS's `Λⱼ` multipliers are the same idea in the discrete group).

**Net:** n=7 shares the harness with n=6 but essentially none of the mathematics. It is
a from-scratch formalization of a discrete number-theoretic apparatus + a new bridge
lemma — not an incremental extension. The compensating good news is heavier Mathlib
leverage.

---

## 10. Recommended n=7 prep sequence (front-load what hurt most on n=6)

1. **Source-first.** Read `sources_barajas_serra_2008.txt` end-to-end; write a
   one-page proof-skeleton mapping each lemma (2–12, §5–§7) to: have-it / Mathlib-has-it
   / must-build. (We now have the paper locally — the n=6 (1,±2) fiasco came from *not*
   doing this.)
2. **Scope the bridge first.** Decide how `intLRC 7` (real `circDist`) connects to BS's
   `χ_r(D) ≤ |D|+1`. This is the riskiest unknown; settle it before case-analysis work.
3. **Build the discrete framework as small, shared files** (`LRC/Discrete/` or similar):
   `ν`/`r`/q-map/`|·|_N`/multipliers/Prime-Filtering — each ~300–500 lines, leaf modules.
   Lean on `ZMod`, `(ZMod N)ˣ`, `padicValNat` from the start.
4. **Generate the finite case dispatches** (the `(ℓ(A₁),ℓ(A₂),ℓ(A₄))` tuples, the ẽ
   cases) from verified param tables, with a reusable de-risk harness — not by hand.
5. **`#print axioms intLRC_seven`** is the bar. Don't claim done until it is
   `[propext, Classical.choice, Quot.sound]` *and* the statement-integrity of the bridge
   is checked (the n=6 lesson: axiom-clean ≠ right statement).
6. **Decompose files and use git from commit one.**
