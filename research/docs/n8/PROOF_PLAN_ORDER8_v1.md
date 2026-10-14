# Order eight: plan to complete the proof

2026-09-26. Owner's direction: *"any gap can be closed by taking the type of arrangement, permuting it via the cascade to
map what and how the deformation works."* Every open case below is worked that way:
1. **Map.** Perturb arrangements of the case's type and read the cascade exactly.
2. **Law.** Extract the exact law of where the isolation moves.
3. **Lemma.** State the law as a lemma about the slowest runner's readings.
4. **Prove.** Prove it in Lean, or certify it exactly and then move it to Lean.

Running record: `docs/n8/RUNNING_LOG_order8_v1.md`, E36–E55. Paths below are relative to `LonelyRunner/` unless they
start with `docs/`.

---

## 1. The proof's shape (links already proved in Lean, axiom-clean)

```
LonelyRunnerAt8                                   (every runner of every real arrangement)
  ⇐ lonelyRunnerAt8_of_slowest                    EndRunnerN   [PROVED]
     "the slowest runner of every arrangement of 8 distinct positive whole-number speeds is lonely"
     (every runner's differences are the slowest runner's in (1, 1+d₁, …, 1+d₇); at most 6 distinct → order 7;
      reversing the speeds swaps the ends — the owner's "runner 1 is runner 8's neighbour")
```

So **only the slowest runner remains**. Its readings are the running sums of the speed gaps:
`d_j = g₁ + … + g_j`, `d_min = g₁` (its own gap), `d_max = W = g₁ + … + g₇` (the spread), `S = W/g₁`.
The owner's shapes (evenly spaced; clumped with outliers; evenly spaced with a clump) are shapes of the gap vector
`(g₁, …, g₇)` up to scale, and the case split is on it.

## 2. The case split for the slowest runner

| case | condition | status | by |
|---|---|---|---|
| **A** | `g₁ ≥ W/7` (its own gap at least the mean) | **PROVED, Lean** | R1: `lonely_eight_of_spread`, `ratio_condition`; Thm 4.9 |
| **B** | `W/22 ≤ g₁ < W/7` | **VERIFIED, not Lean** | exact box certificates: event by `R = 15` (E49, E50, E52, slabs to 22) |
| **C** | `g₁ < W/22` (its own gap small against the spread: the subject is in a close pair) | **open** | see §3 |

The split is exhaustive by construction. Every clump *elsewhere* (not touching the subject) falls in A or B, because
those cases constrain only `g₁` against `W`. That matches the 52 late events: all had a close pair **not** including
the subject (E54/E55, `late_gap_ratio_v1`). The B/C boundary moves up as the slabs run (currently 22).

## 3. Case C: the subject in a close pair

For the slowest runner `g₁` small means runner 2 is close to it. At the subject's own scale every other reading is
large (`s_j = d_j/g₁`). The subject's nearest runner must be at least `1/8` round the circle, so the event is at
`t ≥ 1/(8g₁)`, a long time on the others' scale, during which they lap many times. The structure available:

- **Core `{g₁}` by lower order** (`SplitChainN.lonely_of_split`, u = 1): runner 2 is clear at `1/8` on a window of
  `3/(4g₁)` around `t = 1/(2g₁)`. In laps of `d₂` that window is `(3/4)·s₂`: large.
- **So Case C reduces to a window statement for the other six:** in any window of `K` laps of `d₂`, some instant has
  all six clear. It closes where `(3/4)·s₂ ≥ K`.
- The six have their own shape, the gaps `g₂ … g₇`, and it sub-splits the same way:
  - **C-sep** (the six separate into levels by large gaps): nested windows. `SplitChainN.nested` is PROVED; it needs
    only the chain conditions.
  - **C-compact** (a tight clump among the six): collapse. `TrainCollapseN` is PROVED at ratio 56, and
    `SyncBlockN` gives the free phase.
  - **C-even** (the six comparably spaced): the **window constant `K₆`** for a bounded-shape block. **Owed.** This is
    the piece the certificates and the chain do not supply. E31 measured `κ ≤ 2.76` laps for non-synchronised blocks.

## 4. Work packages (in order)

**WP1 — the skeleton, restated on the slowest runner (Lean, small).**
- State Cases B and C as named OWED Props on the slowest runner's gap vector, registered on the Spec gate.
- Prove `LonelyRunnerAt8 ⇐ CaseB ∧ CaseC`, with Case A discharged by R1.
- *Check:* gate PASS; `#print axioms` on the top theorem shows only the three.
- *Output:* the proof's exact remaining shape, in Lean.

**WP2 — map Case C by the cascade** (owner's method).
- Families: the slowest runner with `g₁ < W/22` and the rest (a) evenly spaced, (b) clumped with outliers, (c) evenly
  spaced with a clump.
- Perturb one and two runners along paths, exact. Record the event, its pinners, the core's window and the six
  runners' first clear instant inside it (in laps of `d₂`), and every jump of scale.
- *Output:* the law of where the isolation moves when the subject's own gap is small, and a measured `K` against
  `(3/4)·s₂`, with controls.

**WP3 — the window constant `K₆` for bounded-shape blocks.**
- Exact cell enumeration with a free starting phase: the climb-cell method in the block's own coordinates (readings of
  the six, a phase variable). This gives `K` exactly on the bounded shape region.
- Positive control: the measured κ values of E31.
- *Then:* a Lean lemma `block_window` (hypotheses: shape bound; conclusion: every window of `K` laps holds a clearing
  instant) and `lonely_of_split` generalised to a block with a window constant (the present form needs the chain
  conditions).

**WP4 — Case C assembled.** C-sep (nested windows), C-compact (collapse) and C-even (WP3) are joined by a case split on
the six runners' gaps, with thresholds chosen where WP2 shows the rules overlap. Each boundary is checked exactly
against the cascade.

**WP5 — Case B into Lean.** Owner's decision after measuring:
- **B1, certificate export.** Each pruned cell gets a Farkas vector and each event cell a witness instant; Lean checks
  them (generated files, as `PinnedBatch` did for 4,413 census families). *First:* measure the size. The slabs
  explore about 2 × 10⁵ to 4 × 10⁵ cells each, which may be too many to check file by file. Merging cells that share
  a witness form may shrink it.
- **B2, the law.** Map the band-0/band-1 structure by the cascade (the late template of E41 and E47), and prove the
  bound analytically.
- **B3.** Raise the A boundary: prove a wider first-lap rule (e.g. the split-chain or −7 opening in gap form), which
  shrinks B.

**WP6 — slabs** (running in the background, `run_slabs_band1.sh`). Each slab moves the B/C boundary up, which shrinks
Case C. The script stops at 24; it can be extended.

**WP7 — tight points** (only if the deformation theorem becomes load-bearing). Discharge local stability at
genuinely tight configurations with the two-pinner lemma (`TwoPinnerN`, whole-number pinners), generalised. The WP2
map shows margin everywhere along crowded-slot paths (E55), so this is needed only at special whole-number
arrangements.

## 5. What "done" means

`LRC.Spec.LonelyRunnerAt8` is proved in Lean with **no hypotheses**, and `#print axioms` shows exactly
`[propext, Classical.choice, Quot.sound]`, under the Spec gate with its Prop register clean. Until then the top
theorem carries the remaining cases as explicit OWED hypotheses, so the gap is always visible.

## 6. Working rules for every package

- Exact arithmetic only (`Fraction`, `gmpy2.mpq`); no floating point in any decision.
- Positive speeds; nobody at rest.
- Boundary Set Method: cells decided by interior points, boundary points separately.
- Long runs under `caffeinate` from the start, with checkpoints, a progress file, and early positives written at once.
- Every enumeration gets a positive control that can fire; every zero is reported with its control.
- Every script and output saved and committed; the running log gets a dated entry per result.
- Results are graded PROVED / VERIFIED / EMPIRICAL; no difficulty labels.
