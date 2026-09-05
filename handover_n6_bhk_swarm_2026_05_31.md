# Handover — n=6 BHK swarm proof session (2026-05-31)

## What landed this session

Genuine proof progress on the n=6 BHK Hard Case via 4-agent swarm
coordination (file-split + parallel worktrees). All work landed in the
nested `LonelyRunner/` repo, 3 commits.

### Proved sorry-free (axioms: `propext, Classical.choice, Quot.sound`)

| Theorem | File | Notes |
|---|---|---|
| `BHK.block_length_bound` | `IntLRC_6_BHK_Lemma4.lean` | Closed `Icc a b ⊆ unsafeOf i` ⇒ `b - a < 1/(3 v_i)`. Strict bound via explicit `t* = (k+1/6)/v_i` witness. |
| `BHK.not_mem_unsafeOf_iff_in_gap` | same | `t ∉ unsafeOf i ↔ ∃ k, k+1/6 ≤ v_i t ≤ k+5/6`. |
| `BHK.not_mem_unsafeOf_of_in_gap` | same | Explicit gap point exclusion. |
| `BHK.gap_piece_bound` | same | Closed sub-interval in 4-gap region forced into `unsafeOf 4`, length `< 1/(3 v_5)`. |
| `BHK.bhk_lemma_4_weak` | same | **The 45-block bound assuming `2 v_4 ≤ v_5` (BHK regime).** Useful directly in all but the marginal `v_5 < 2 v_4` slice. |
| `BHK.bhk_case_v1_large` | `IntLRC_6_BHK_Cases.lean` | **Proven dispatcher** for §8: case-splits on `5 v_3 < 7 v_2` (= `x_4 > 5/7`) then on secondary thresholds, into the 4 named §8 sub-cases. |

### Proved modulo small residuals

- `BHK.bhk_lemma_4`: 3 of 4 cases (A, B1, B2-first) unconditional;
  Case C residual extracted to standalone `bhk_lemma_4_case_C`.
- `BHK.bhk_corollary_5`: proved modulo `bhk_lemma_4`.
- `BHK.bhk_theorem_2`: proven dispatcher modulo case branches.

### Structurally decomposed

`bhk_case_v1_large` (one opaque sorry) → 4 named sub-theorems matching
BHK paper §8.1.1, §8.1.2, §8.2.1, §8.2.2. Each carries the explicit
de-normalised inequality conditions (e.g. `5 * speeds ⟨3⟩ < 7 * speeds ⟨2⟩`
for "x_4 > 5/7"). Future work can target each independently.

## Architecture changes

Split monolithic `IntLRC_6_BHK.lean` into 4 sibling modules:

```
IntLRC_6_BHK_Defs.lean      (115 lines)  bhkB, unsafeOf, bridges, structural
IntLRC_6_BHK_Lemma4.lean    (680 lines)  Lemma 4 helpers + proof + Corollary 5
IntLRC_6_BHK_MainLemma.lean  (54 lines)  Main Lemma + Corollary 6 (still sorry)
IntLRC_6_BHK_Cases.lean     (154 lines)  4 case branches + §8 decomposed
IntLRC_6_BHK.lean             (17 lines) Re-export shim
```

This enabled the parallel agent work and makes future single-file
sessions targeted (rather than the original 296-line monolith).

## Build status

```
lake build              → 2485 jobs OK
Project sorries (13):
  IntLRC_6_BHK_Lemma4.lean    1  (bhk_lemma_4_case_C — named residual)
  IntLRC_6_BHK_MainLemma.lean 2  (Main Lemma + Cor 6, unchanged)
  IntLRC_6_BHK_Cases.lean     7  (§5 + §6 + §7 + 4×§8 sub-cases)
  IntLRC_7.lean               1  (n=7, pre-existing)
  Theorem121_Main.lean        2  (DI-MOD + real, pre-existing)
IntLRC_6.lean sorries  → 0 (Hard Case dispatched to intLRC_six_hard)
```

Net sorry change: 10 → 13 (one opaque sorry replaced by 5 *structured*
ones plus 2 new sorry-free theorems). The structural sorries are each
explicitly tied to a BHK paper reference.

## Swarm coordination notes

- **3 parallel agents spawned** initially (lean4:sorry-filler-deep for
  Lemma 4, general-purpose × 2 for Cases §8 and Main Lemma). Session
  limit hit during the first run; 1 agent landed partial work (the
  helpers + an `rw [le_div_iff₀]`/`div_le_iff₀` swap bug I fixed
  manually).
- **2 parallel agents respawned** after session reset (sorry-filler-deep
  for Lemma 4 continuation, general-purpose for §8 decomposition). Both
  completed successfully.
- **Main Lemma**: untouched this session. It's the largest unproved
  piece (BHK §3, ~3 pages of Minkowski-style line-segment argument).

## Suggested next-session work order

1. **Easiest first**: BHK §8.2.1 (`bhk_case_8_2_1`). BHK derives
   `x_1 > 275/91` from `(6j-1) x_5 < x_1 < (6j+1) x_5` with `j ≥ 1`,
   then contradicts `hlarge` (x_1 ≤ 3 < 275/91). Short Lean proof
   once a "5-block length bound" helper is in.
2. **BHK §8.1.1**: similar shape to §8.2.1. ~1 session.
3. **`bhk_lemma_4_case_C`**: the genuine BHK k≥2 residual. Requires
   showing a 5-gap fits inside the 4-block forces `2 v_4 ≤ v_5`. A
   modular-alignment proof — likely ~200 Lean lines. Once closed,
   `bhk_lemma_4` becomes unconditional, `bhk_corollary_5` becomes
   unconditional, and `bhk_lemma_4_weak` becomes a corollary.
4. **§8.1.2, §8.2.2**: longer BHK sub-cases. Defer until shorter ones
   are in to confirm the formalisation pattern.
5. **`bhk_main_lemma`**: deep. Plan a full session, possibly with two
   agents (Step 1: Minkowski-style covering; Step 2: minimality
   refinement) plus a foundations agent.

## Methodology applied

- **CLAUDE.md §3 "check it can run"**: every agent had targeted
  `lake build <module>` + full `lake build` as exit criteria.
- **CLAUDE.md §2 swarm**: file-split before spawning agents so each
  owned one file → zero merge conflicts despite parallel work.
- **CLAUDE.md §3 "trust but verify"**: caught the agent's swap bug
  (`le_div_iff₀` ↔ `div_le_iff₀`) on Lemma 4 by running build before
  declaring success.
- **CLAUDE.md §5 sharpen-and-narrow avoidance**: when the agent
  couldn't close Lemma 4 fully, didn't add a fake constraint to the
  main theorem — instead extracted `bhk_lemma_4_weak` (BHK regime
  conditional) and isolated the residual as a separate named sorry
  with its own type. Main `bhk_lemma_4` statement is unchanged.

## Source artefacts

- `bhk_2001.pdf` (49 pages, in repo root) — full BHK paper, including
  the long Proposition 11 (§5, p17–40) for `bhk_case_v1t0_zero`.

## Commits (in nested `LonelyRunner/` repo)

- `d206b01` refactor(n=6): split IntLRC_6_BHK into modules
- `5bc392a` feat(n=6 BHK): add 4 helper lemmas toward Lemma 4
- `7472a1e` feat(n=6 BHK): swarm proof progress — Lemma 4 partial +
  §8 decomposed
- `0b32414` feat(n=6 BHK): add arithmetic kernels for §8.1.1 and §8.2.1
- `fb82762` feat(n=6 BHK): add §8.1 step 1 arithmetic kernel
- `b14ef65` feat(n=6 BHK): narrow §8.2.1 structural sorry via block_containment
- `3157a61` feat(n=6 BHK): add §8.1 step 1 find_65 lemma

## Session continuation (2026-05-31 ctd)

Two BHK §8 sub-cases further decomposed via the **arithmetic-kernel pattern**:
each main case now reduces to a single structural sorry (the BHK gap-geometry
derivation) followed by a sorry-free arithmetic kernel.

| Kernel | Inputs | Arithmetic contradiction |
|---|---|---|
| `bhk_case_8_2_1_kernel` | `j ≥ 2`, `(6j-1) v_4 < 7 v_5`, `5 v_5 < (6j+1) v_3`, `h821`, `hlarge` | `24 j < 46` ⟂ `j ≥ 2` (mirrors BHK's `x_1 > 275/91 > 3`) |
| `bhk_case_8_1_1_kernel` | `(65) 5 v_1 < v_5`, `(70b) 5 v_4 < 19 v_1`, `(71b) 29 v_5 < 37 v_4` | `725 v_1 < 185 v_4 < 703 v_1` ⟹ `725 < 703` |
| `bhk_8_1_step1_kernel`  | `j ≥ 2`, `(6j-1) v_1 < v_5`, `5 v_5 < (6j+1) v_4`, `h81`, `hlarge` | `24 j < 46` ⟂ `j ≥ 2` (identical structure to §8.2.1; forces `j = 1` giving BHK (65)) |

Both kernels close with a single `nlinarith` after positivity setup,
axioms = `[propext, Classical.choice, Quot.sound]`. The structural sorries
in `bhk_case_8_2_1` and `bhk_case_8_1_1` are now *typed, named* gaps: an
existence statement of the form `∃ j ≥ 2 ∧ ...` (8.2.1) or a conjunction
of three structural inequalities (8.1.1). Subsequent work can target each
geometric derivation independently.

**Sorry count**: 13 → 13 (kernels are new proven lemmas, not sorries).

**Updated next-session priority:**

The arithmetic kernel + find_x decomposition pattern is now established. Each §8
sub-case becomes a 3-layer stack: `find_x` (inclusion → structural inequalities
via `block_containment` + impossibility kernel) → arithmetic kernel
(inequalities → False).

1. **Refactor §8.1.1** to use `bhk_8_1_step1_find_65`: introduces the 1234-gap
   inclusion as a separate sorry; the remaining (70b)/(71b) gap derivations
   need their own find_x lemmas (123-gap → (70), 1235-gap → (71)).
2. **Write more find_x lemmas** for the §8.1.1 / §8.1.2 / §8.2.2 inclusion
   patterns (123/1234/1235-gap, 13-gap, 1345-gap). Each follows the
   `block_containment` + kernel template.
3. **Attack the geometric inclusions** directly: these are the remaining
   structural sorries. Each is a statement like
   `[a, b] ⊆ unsafeOf k` where `[a, b]` is a sub-interval of a 123-gap and
   `k` is determined by which other runners' blocks don't intersect.
   The argument uses `h_no_lonely` + 4-block / 5-block geometry to exclude
   `unsafeOf k'` for `k' ≠ k`.
4. **`bhk_lemma_4_case_C`** (closes `bhk_lemma_4` unconditional;
   `bhk_lemma_4_weak` becomes a corollary).
5. **§8.1.2, §8.2.2 arithmetic kernels** (8.2.2 has two integers `j < k`).
6. **Main Lemma** (BHK §3, deep — plan a dedicated session).
