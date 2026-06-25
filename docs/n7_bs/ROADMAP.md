# n = 7 LRC — Barajas–Serra 2008 formalization ROADMAP

**Live status board for the n = 7 project.** Update the Status column as files
land. Ground truth for "done" is always `#print axioms` + build warnings, never
this table.

## What we are verifying

- **Conjecture target:** `intLRC 7` (6 moving runners + observer, gap `1/7`).
- **Source:** Barajas & Serra, *The Lonely Runner with Seven Runners*, EJC 15
  (2008) R48. On disk: `sources_barajas_serra_2008.txt` (830 lines, extracted).
  SHA-256 pinned in `docs/n7_bs/source_integrity.md`.
- **Method:** Prime Filtering with `p = 7` — a finite, number-theoretic,
  residue-chasing argument (7-adic valuation `ν`, position function `q`/`r`,
  multiplier sets `Λ_j`). **Structurally unrelated to the BHK 2001 geometry that
  closed n = 6** — the n = 6 BHK lemmas do not transfer.

## The single gap

`LonelyRunner/LonelyRunner/LRC/SmallN/IntLRC_7.lean` already wires the full
reduction. `intLRC_seven` splits into:
- **BSR** (`theorem61_BSR`, `V ≤ 6·v₁`) — done.
- **Large-SR** (`theorem71_LargeSR`, `6·v₅ < V`) — done.
- **Hard Case** `6·v₁ < V ≤ 6·v₅` — the **single `sorry`**, = Barajas–Serra
  main result. Closing it (axiom-clean) closes n = 7.

`H_seven` (the `m < 7` recursion) is complete and uses `intLRC_six`.

## Module layout (`SmallN/IntLRC_7_BS/`)

Mirror of the `IntLRC_6_BHK_*` split. Files created with frozen-header stubs
during the `draft` step, then filled `prove → review → refactor → golf →
checkpoint`. Source line refs are into `sources_barajas_serra_2008.txt`.

| File | Content | Source lines | Status |
|---|---|---|---|
| `Defs.lean` | 7-adic apparatus: `ν`, `q`/`r`, `Λ_j`, `D₇(i)`, `A_s` residue classes, length `ℓ(X)`. Reuse `LRC/Defs.lean` (circDist, badSet, intLRC). | 40–128, 239–264 | not started |
| `PrimeFiltering.lean` | **Lemma 2 (Prime Filtering)** + **Corollary 3** — the reduction engine, conceptual core. | 129–169 | not started |
| `Reduction.lean` | §4 overview: `|D₇(i)| ≤ 3 ⟹ Cor 3`; reduce to `|D₇(0)| ∈ {4,5}`, `(A)₇ ⊂ {1,2,4}`; eqn (7). | 237–264 | not started |
| `Lemmas.lean` | Supporting Lemmas 4–9 (multiplier existence / `ν`-coloring). | 364–505 | not started |
| `Case_A4.lean` | §5 `|A| = 4`: Case 1 `|A_s|=4` (L287), Case 2 `|A_s|=3` (L299), Case 3 `|A_s|=2` (L319). Finite mod-7 chase (eqns 7–12), candidates for `interval_cases`/`decide`/`omega`. | 267–363 | not started |
| `Case_A5.lean` | §6 `|A| = 5`: 6.1 `|A₁|=5` + Lemma 10 (L509); 6.2 `|A₁|=4` (L547); 6.3 `|A₁|=3,|A₂|=1,|A₄|=1` + Lemma 11 (L569); 6.4 `|A₁|=3,|A₂|=2` + Lemma 12 (L667); 6.5 `|A₁|=3,|A₄|=2` (L698); 6.6 `|A₁|=2` (L743). Likely splits further. | 507–830 | not started |
| `Main.lean` | Assemble into the Hard-Case lemma; rewrite the `sorry` in `IntLRC_7.lean`. | — | not started |

Keep each file ≤ ~300 lines; split greedily (n = 6 lesson — small files keep the
effective thinking budget high and lose less to compaction).

## Order of attack (source-first per file)

1. `Defs` + `PrimeFiltering` — nail `ν`/`q`/`Λ` against mathlib
   (`padicValNat`, `ZMod 7`) so finite residue arithmetic is `decide`-friendly.
2. `Reduction` — `|D₇(i)|≤3 ⟹ Cor 3`; pin to `|A| ∈ {4,5}`, `(A)₇ ⊂ {1,2,4}`.
3. `Lemmas` (4–9) as needed by the cases.
4. `Case_A4` — finite, explicit mod-7 chases.
5. `Case_A5` — the involved case (Lemmas 10–12, 6.1–6.6).
6. `Main` — assemble → rewrite `IntLRC_7.lean`'s `sorry` → confirm
   `#print axioms intLRC_seven` = `[propext, Classical.choice, Quot.sound]`.

## Verification bar (the `/goal`)

`cd LonelyRunner && lake build` exits 0 **and** `#print axioms intLRC_seven` =
`[propext, Classical.choice, Quot.sound]` with zero `sorry` — same bar that
certified n = 6. Per-lemma: confirm each open `sorry`'s *statement* matches the
source; adversarial fresh-subagent review before promoting draft → proved.

## Discipline (carried from n = 6)

- **Source-first.** Read Barajas–Serra's argument for the exact case (grep its
  Lemma/Case number in `sources_barajas_serra_2008.txt`) before any de-risk,
  sweep, or invention.
- **No editorializing.** State what the source says + what a build / script /
  `#print axioms` verified. No difficulty value-judgments.
- **"Proved" ≠ "closed."** A conditional lemma that drops required cases narrows,
  not closes. Audit via `#print axioms` on the TOP theorem, not grep.
- **Machine-generate** templated lemmas from verified param tuples (Python in
  `experiments/`) to kill transcription error.
