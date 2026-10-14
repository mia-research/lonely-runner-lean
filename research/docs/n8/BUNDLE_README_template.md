# Eight Lonely Runners — a bounding framework

T. Palelei, 2026-09-17.

---

## What this is, and what is not claimed

This is a framework for the Lonely Runner Conjecture at eight runners (seven speed
differences, threshold `1/8`), with a Lean 4 artefact that machine-checks it.

**The conjecture is not proved here.** The open statement is named, stated precisely in
Lean, and left open. It is called **Existence**: that for every arrangement the cascade
reaches a fixed point. `MANUSCRIPT_v9_3.md` §6.7 marks it `[OPEN]`, and the verification
gate **fails** if anyone states it as a theorem in the artefact.

This is a framework and a partial result, offered for criticism. It is not a claimed proof
of LRC(8), and it is not a replication of Rosenfeld's 2025 computational verification —
it is an independent, analytic line.

## Start here

| file | what it is |
|---|---|
| `MANUSCRIPT_v9_3.md` | the manuscript of record |
| `lean/LonelyRunner/LRC/Spec/Target.lean` | **the open problem, as a Lean `Prop`** — read this first if you want the mathematics without the prose |
| `docs/CORRECTIONS_2026_09_17_v2.md` | what was withdrawn on 2026-09-17 and why |
| `docs/OBJECT_REGISTER_v1.md` | the register of imported assumptions, and which do not apply |

`Target.lean` is the shortest route to the actual question. It defines `ExistenceAt8`,
proves three formulations equivalent, and reduces the whole remaining obligation to a single
statement, `CascadeCapped` — with **both directions proved**, so it is the obligation
restated rather than weakened.

**There is no `sorry` in the artefact.** `ExistenceAt8` is a `def ... : Prop` — a statement
of what would have to be true, with nothing asserting it. That is deliberate: a `sorry`
would be an unproved claim, and there are none.

## What is in `lean/`, and what is not

The Lean tree here is the **exact transitive import closure of the n=8 artefact**: @MODULES@-module artefact plus its
dependencies, computed rather than hand-picked.

| included | why |
|---|---|
| `LRC/Cascade/` (@MODULES@ modules) | the artefact itself. 2.5 MB of it is `CensusBatch` and `PinnedBatch1–4` — 4,475 fully-pinned census families, one declaration each. Large because it is a machine-checked enumeration |
| `LRC/Construction8/`, `LRC/ConstructionN/` | imported by the cascade |
| `LRC/Spec/Target.lean` | the frozen target |

Deliberately **absent**, and their absence is not an oversight:

- **The general-`n` line** (`Theorem52_Weyl`, `Theorem121_Main`, …). That is separate work and
  still contains `sorry`. Excluding it is why **every file in this tree is `sorry`-free** and
  why a plain `lake build` here cannot appear to implicate it. `LonelyRunner.lean` has been
  replaced with a root scoped to the n=8 artefact; the full repository's root imports more.
- **`LRC/SmallN/`** — the completed n=3…7 results. Unrelated to this framework; n=7 is
  Barajas–Serra, structurally different.
- **Build logs and `.lake/`.** Mathlib is not bundled: `lake exe cache get` fetches it,
  pinned to `v4.29.1` in `lake-manifest.json`.

## Verifying it yourself

Requires Lean 4 with `elan`; the toolchain is pinned in `lean/lean-toolchain` and mathlib
in `lean/lake-manifest.json`.

```
cd lean
lake exe cache get        # fetch mathlib's prebuilt oleans
bash scripts/cascade/gate.sh
```

The gate builds all 19 cascade modules, inventories `sorry`, scans for `native_decide`,
`unsafe` and `admit`, runs `#print axioms` on **every** theorem, and checks that Existence
is not stated. It takes about 12 minutes warm, almost all of it the per-theorem axiom check,
and prints per-step timings.

Run against **this bundle's tree**, compiled from source. The deposited runs are
`experiments/cascade_gate_v9_3_v1.out` (the full repository) and, if present,
`experiments/cascade_gate_bundle_v1.out` (this tree). Those files are the witness; the
figures below are regenerated from the tree at build time, not typed.

```
GATE PASS: @THEOREMS@ theorems, axiom-clean (coverage @THEOREMS@ of @THEOREMS@ on disk).
           Existence at order 8 is NOT proved -- it remains open and unstated.
```

Cascade: **@MODULES@ modules, @THEOREMS@ theorems** — of which **@STRUCTURAL@ structural** and
@GENERATED@ generated census instances. Digest `@DIGEST@`, commit `@COMMIT@`.

**Read the split, not the total.** @GENERATED@ of the @THEOREMS@ are the census: one generated
theorem per arrangement, each the same one-line application of `lonely_of_band_list` with a
different seven-element list. They are a machine-checked enumeration, not @GENERATED@ distinct
results. The mathematical content is the **@STRUCTURAL@ structural** theorems.
The gate has six checks; [6] fails if the manuscript's recorded figures ever disagree with
the tree, which is why the numbers here and in the manuscript cannot drift apart.

`experiments/cascade_gate_v9_3_v1.out` is the same gate run in the full repository (718 s).
The difference is build state, not content: both report @THEOREMS@ theorems, all axiom-clean.

**One scope note on the gate.** Its `sorry`, hygiene and axiom checks cover `LRC/Cascade/` —
the artefact — not `Construction8`, `ConstructionN` or `Spec`. Checked separately across all
40 files of this tree: **no `sorry`, `native_decide`, `unsafe` or `admit` in code anywhere**.
The word `sorry` appears twice as prose, in the docstring of `LonelyRunner.lean`, explaining
why the general-`n` line is excluded.

"Axiom-clean" means every theorem depends on `propext`, `Classical.choice` and `Quot.sound`
only — no custom axioms, no `sorry`. Cascade digest
`@DIGEST@`, repo commit `@COMMIT@`.

A plain `lake build` is **not** a check: the default target does not enter `LRC/`.

## How claims are graded

Every claim in the manuscript carries a tag. This is stricter than the usual convention,
which has only "theorem" and "conjecture":

| tag | means |
|---|---|
| `[PROVED — <declaration>]` | proved in Lean; the declaration name is given and resolves |
| `[VERIFIED — n cases]` | computed exhaustively in a stated range; not a proof |
| `[DERIVED]` | proved in the text, not formalised |
| `[OPEN]` | not proved, and said so |

25 numbered results. Scripts behind every computational claim are in `experiments/`, each
with its deposited output.

## Where the difficulty is

Two negative results bound the remaining routes. Both say where *not* to look; neither says
Existence is false.

- **Move counting cannot reach n=8, k=7.** Capping the cascade by charging each move its
  growth cost yields `log G · (1 − 2k/n) ≤ C`. At `n=8, k=7` the coefficient is `−0.75` —
  vacuous, wrong sign. Not an artefact of one lemma. (`experiments/move_count_ceiling_v1`)
- **The flank route needs uniformity in the denominator.** Shadowing is governed by ratio
  denominators (47% at denominator 2, 0.11% at 17), **not** by the number of non-integer
  ratios, which peaks at 4 and falls at 6. Seven random reals are trivial (median `k = 0`).
  (`experiments/flank_what_predicts_v1`)

## Known defects, disclosed

- `MANUSCRIPT_v9_3.md` Appendix A cites `PROOF_DEV_v1` Part V, which sits in a separate
  working tree and is **not in this bundle**. The passage is quoted verbatim in
  `docs/LOST_FUNCTIONS_v1.md` §E, which is, so the step is checkable here. The manuscript
  marks it as "stated there, not derived … recorded as a direction, not a result", so nothing
  rests on it.
- `exhaustive_exact.py`, cited in §10, sits in a separate working tree and is not here.
- The §5 nativeness pass is scoped to each version's *additions* and is a claim about what
  they **cite**, not that the artefact imports nothing. `LRC/Cascade/Irrational.lean`
  imports number theory and analysis deliberately, to exhibit that irrational speeds work.

## What criticism would be most useful

1. **`Target.lean`** — is `ExistenceAt8` the right statement of LRC(8) at threshold `1/8`,
   and is `CascadeCapped` genuinely equivalent to it rather than weaker?
2. **`docs/OBJECT_REGISTER_v1.md`** — it argues 26 items are not this framework's
   requirements. That is a claim about what the framework is, and no gate can settle it.
   Disagreement here is the most valuable kind.
3. Anything graded `[DERIVED]` or `[VERIFIED]` that you think is being read as `[PROVED]`.
