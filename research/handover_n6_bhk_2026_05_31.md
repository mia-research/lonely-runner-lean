# Handover — n=6 BHK scaffolding (2026-05-31)

## What landed this session

Created `LonelyRunner/LonelyRunner/LRC/SmallN/IntLRC_6_BHK.lean` (~265 lines)
that decomposes the single Hard-Case `sorry` in `IntLRC_6.lean` into a
structured set of 7 sorries mirroring BHK 2001's section layout.

### Proved (no sorry)

- `BHK.mem_bhkB_iff` — bridge from BHK's interval formulation
  (`x ∈ ⋃_k (k − 1/6, k + 1/6)`) to our `circDist x < 1/6` form. Proved via
  `circDist_eq_infDist` (forward) and `min(fract, 1−fract)` (reverse).
- `BHK.mem_unsafeOf_iff` — trivial transport, `t ∈ unsafeOf speeds i ↔
  circDist (v_i · t) < 1/6`.
- `BHK.bhk_corollary_5` — **modulo `bhk_lemma_4`**. Contradiction argument:
  if Icc a b is a 123-gap of length ≥ 2/(3 v_3) but no lonely time, then
  Icc a b ⊆ unsafeOf 3 ∪ unsafeOf 4; Lemma 4 bounds this length
  < 2/(3 v_4) < 2/(3 v_3), contradiction.
- `BHK.bhk_theorem_2` — **modulo the 4 case branches + Main Lemma + Lemma
  4**. Dispatches on `speeds ⟨2⟩ ≤ 3 · speeds ⟨0⟩` (large `v_1`) then on
  `{t_0}`, `{v_1 · t_0}` zero/nonzero.
- `intLRC_six_hard` — exported alias of `bhk_theorem_2`, called from
  `IntLRC_6.lean`'s Hard Case.

### Stated with `sorry` (7 structured sub-theorems)

| Sorry | BHK ref | Notes |
|---|---|---|
| `bhk_lemma_4` | Lemma 4 | 45-block size bound `< 2/(3 v_4)`. Elementary; case split `k ≤ 1` vs `k ≥ 2` on # of 5-blocks. Probably 100–200 lines. |
| `bhk_main_lemma` | Main Lemma | Cyclic subgroup `G ⊆ T` of order `n` intersects every `α × β` rectangle with `αβ ≥ 1/n`, modulo 2 exceptions. Deepest piece — Minkowski-style argument with line segments parallel to L_g. Probably 300–500 lines. |
| `bhk_corollary_6` | Corollary 6 | Direct consequence of Main Lemma with `K` chosen as a strip. ~50 lines once Main Lemma is in. |
| `bhk_case_v1t0_zero` | §5 | `{v_1 t_0} = 0`, small `v_1`. Specialised Main Lemma application. |
| `bhk_case_t0_zero` | §6 | `{t_0} = 0`. Different Main Lemma application. |
| `bhk_case_v1_small_generic` | §7 | Generic small `v_1` with both fracs nonzero. Direct Main Lemma. |
| `bhk_case_v1_large` | §8 | `v_3 ≤ 3 v_1`. Ad hoc, no Main Lemma. Probably easiest case branch. |

## Build status

```
lake build              → 2485 jobs OK (same as n=5 closure)
Project sorries         → 10 total:
                          7 in IntLRC_6_BHK.lean (this session, structured)
                          1 in IntLRC_7.lean (pre-existing, n=7 Hard Case)
                          2 in Theorem121_Main.lean (pre-existing, DI-MOD + real)
IntLRC_6.lean sorries   → 0 (Hard Case dispatched to intLRC_six_hard)
```

## Suggested next-session work order

The order respects logical dependencies:

1. **`bhk_lemma_4`** first — elementary, unblocks `bhk_corollary_5` axiom-wise
   (currently uses `sorry` transitively through Lemma 4). The argument
   doesn't need any new infrastructure, just careful interval-counting on
   the `unsafeOf` periodic structure.
2. **`bhk_case_v1_large`** (§8) next — the only case branch not gated on
   the Main Lemma. Standalone ad hoc argument.
3. **`bhk_main_lemma`** — the big one. Plan to spend a full session purely
   on it, possibly extracting the line-segment / projection machinery into
   a separate Lean module since it's pure 2-torus theory.
4. **`bhk_corollary_6`** — falls out once Main Lemma is in.
5. **§§5, 6, 7 case branches** — mostly Main Lemma applications, fall in
   order once Corollary 6 lands.

## Architecture notes / gotchas

- The skeleton uses inline interval predicates rather than a separate
  `isSBlock` definition. This avoids `def ... := sorry` which would have
  polluted `#print axioms`. If you need a richer block predicate later,
  introduce it locally.
- `bhkB` is the open ball-style `∃ k : ℤ, |x − k| < 1/6` set; matches
  BHK's "B" exactly. `bhkRectangle` is also from the paper directly.
- The 4 case-branch statements assume the BHK reduction `gcd(speeds) = 1`
  is in hand. We have this from `intLRC` defn. No additional rationality
  reduction is needed (speeds are integers from the start).
- Strict-mono ordering: `speeds ⟨2⟩` = paper's `v_3`, `speeds ⟨3⟩` =
  paper's `v_4`, etc. (0-indexed Fin 5).

## Source artefacts

- `bhk_2001.pdf` — 10-page Bohman–Holzman–Kleitman 2001 paper, in repo root
  for offline reference.
- `/tmp/perarnau_serra_survey.pdf` — Lonely Runner Conjecture turns 60
  survey, §6.4 has the high-level BHK summary.

## Methodology applied

- Followed CLAUDE.md §3 "give Claude a check it can run": each structural
  decomposition was followed by `lake build` to confirm integration.
- Followed §3 "adversarial review": before committing, verified the
  dispatch logic in `bhk_theorem_2` by inspection (no missed cases:
  `v_3 ≤ 3 v_1` vs `3 v_1 < v_3` × `{v_1 t_0} = 0` ∨ `{t_0} = 0` ∨ neither).
- Did NOT apply §2.5 "sharpen-and-narrow" anti-pattern: the case branches
  are stated for the FULL BHK scope (e.g., `3 v_1 < v_3`, not artificially
  tightened to `4 v_1 < v_3`), to avoid losing the cases where they need
  to be applied.
