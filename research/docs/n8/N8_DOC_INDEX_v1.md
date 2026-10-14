# n = 8 — Documentation Index

**T. Palelei.** v1, 2026-09-18. Entry point for the two documentation files written this session.

---

## The bottom line, in one paragraph

The framework fixes one runner at a time, reads the other seven against it, and runs a **cascade**
fixed by the speeds from the instant `1/(8·d_min)`. Two of its three outcomes are **proved and
machine-checked**: a fixed point of the cascade is a lonely instant and the *first* one
(**Construction**), and every lonely instant lies at or after every cascade step and is matched by an
opening of one of the subject's own disparities (**Localisation**). The third — **Existence**, that
the cascade reaches a fixed point at all — is **open at order 8**, and the Lonely Runner Conjecture at
eight runners does not follow from anything here. The Lean kernel contains **no `sorry`** and every
theorem in it depends on `propext`, `Classical.choice` and `Quot.sound` only — witnessed 2026-09-18 at
commit `919b944`, **4,752 of 4,752 clean** (`experiments/n8/cascade_gate_919b944_v1.out`). Existence is
absent from it not as a hole but as an unproved `Prop` in the specification, and the cascade gate fails
if a declaration naming it appears in the artefact.

**One caveat on that witness, stated here rather than buried.** That gate run ends **GATE FAIL**, on
check [6] alone: `MANUSCRIPT_v9_6.md` records 4,748 theorems at digest `d8ceb5ad`, and the tree now
carries 4,752 at `56696dd9`. The failure is **documentation drift, not a defect in the Lean** — checks
[0] through [5] all passed. See `N8_LEAN_KERNEL_v1.md` §5.4.

---

## The seven files

Written as one set for a NotebookLM notebook. Each is self-contained: where a document cites
material outside the set, the content is inlined rather than pointed at.

| file | covers | read it for |
|---|---|---|
| **[`N8_FRAMEWORK_CHEATSHEET_v1.md`](N8_FRAMEWORK_CHEATSHEET_v1.md)** | **read this first.** The positive list of objects, the three outcomes, every ban with its substitution, the four decidable tests, and the word collisions that survive a grep | what the framework is, and what does not belong in a discussion of it |
| **[`N8_GLOSSARY_v1.md`](N8_GLOSSARY_v1.md)** | every framework term defined once, with the object it names — and §5, the words that name two different objects | what any term means |
| **[`N8_PROOF_v9_3_DOC_v1.md`](N8_PROOF_v9_3_DOC_v1.md)** | the mathematics of `MANUSCRIPT_v9_3.md`, every numbered result with its grade, the firewall, the open register, v9.3's known defects, and §D — the full delta to v9.6 and beyond | what is claimed, and at what grade |
| **[`N8_PROOF_ARGUMENTS_v1.md`](N8_PROOF_ARGUMENTS_v1.md)** | the arguments themselves: the scale recursion, Construction's four parts, the finiteness argument, the nearest-integer walk, the flank calculus, the `n > 2k` potential, the order-5 certificate | how a result is proved |
| **[`N8_WHY_OTHER_ROUTES_FAIL_v1.md`](N8_WHY_OTHER_ROUTES_FAIL_v1.md)** | the object register (28 imported constructs), the objection ledger (tested, not argued), the false blockers, and the four routes that cannot close it | why some other approach does not apply |
| **[`N8_LEAN_KERNEL_v1.md`](N8_LEAN_KERNEL_v1.md)** | the Lean trees module by module, the two gates check by check, the axiom position, the three gate defects found in production, and §6 — the command for every figure | what is machine-checked, and how to re-derive it |
| **[`N8_LITERATURE_AND_HISTORY_v1.md`](N8_LITERATURE_AND_HISTORY_v1.md)** | Rosenfeld 2025 step by step, Barajas–Serra, the line to thirteen runners, how this framework differs by type, and the v7-to-v9.6 version history | where this sits in the literature |

---

## Which document is the record

| | |
|---|---|
| **Manuscript of record** | `MANUSCRIPT_v9_6.md` (2026-09-18) |
| **Documented body here** | `MANUSCRIPT_v9_3.md` (frozen 2026-09-17, superseded the same day) |
| **The Lean target** | `LRC.Spec.LonelyRunnerAt8` — the conjecture on an arrangement `v : Fin 8 → ℝ`, injective (amended 2026-09-18) |
| **Off the path** | `LRC.Spec.ExistenceAt8` — the difference-set form. Retained and still proved **sufficient**, but not the target |

These two files are **documentation, not manuscript versions**. They do not supersede anything and
carry no grade of their own. Where they and `MANUSCRIPT_v9_6.md` disagree, the manuscript governs on
the mathematics and **the tree governs on the figures** (recompute; never quote).

---

## What is open

Every item below is the same obligation seen from a different side, except the last two.

| item | where |
|---|---|
| **Existence at order 8** — the cascade reaches a fixed point for every arrangement and runner | proof doc §6.7 |
| equivalently, the cascade's instants are uniformly capped (`CascadeCapped`) | `Spec/Target.lean` |
| equivalently, each runner is in the subject's way at finitely many steps (`DoorFAM`) | `Spec/Doors.lean` |
| equivalently, some flank of the subject hosts a lonely opening (`DoorFlank`) | `Spec/Doors.lean` |
| **sufficient, not equivalent**: the cascade never passes `1/e`, one lap of the nearest runner (`DoorFirstLap`). Measured `τ ≤ 33/56` exhaustively over 170,213 primitive 7-subsets of `[1, 22]`; **the cap is not proved** | `Spec/Doors.lean` |
| equivalently, the moving short gap misses both flanks of runner `i` at some instant | proof doc §4.6 |
| how the AP fit feeds each runner's reading | proof doc §2.3 |
| five disparities at `n = 6 … 10`; Existence at order 5 | proof doc §7.2 |

---

## Grade discipline

Grades are reproduced from the sources and never raised. `[PROVED]` means a proof exists;
`[VERIFIED — scope]` means exhaustive or exact computation over a stated finite range and is **not** a
substitute for a proof; `[EMPIRICAL]` is a measurement; `[OPEN]` is stated and unproved;
`[WITHDRAWN]` is retracted with the reason recorded. Nothing in these two files promotes a claim.
