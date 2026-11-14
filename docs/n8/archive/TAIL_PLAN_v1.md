# Tail plan v1 — `TailBelow17` by fast gaps (2026-11-09)

New file. Target: `Fresh.FilterAssembly.TailBelow17` — every arrangement with a normalised disparity past 49 lands below 17. Readings are normalised by d_min: `1 = ρ₁ ≤ … ≤ ρ₇`, `ρ₇ > 49`.

Owner objects used: R8 (`lonely_of_fast_runner`, native, `LRC/Spec/FastRunnerN.lean`, ported as `Fresh/Nv_FastRunnerN.lean`); windows W₀, W₁ and n* (this session); the negative-cycle closure (`m4_negcycle_v2.py`, `chain_cover_k_v1.py`); the two-block template (E646–E669).

## The split

| case | condition | status |
|---|---|---|
| A | `ρ₇ > 7ρ₆` (fast top) | `Fresh/TailFast.lean`: `tailFast_of_nstar` [L], given `NStarAtMostOne` [OWED] |
| B | `ρ₇ ≤ 7ρ₆`, so `ρ₆ > 7` | open |

**Case A.** R8's proof places the lonely instant in the cell `[τ − δ, τ + δ]`, `δ = 1/(56 ρ₆)` in `θ = R/8` units. So a 1/7-clear instant of the six slower readings in reading 1's 1/7-range of W₀ or W₁ gives a 1/8-clear instant of all seven at `8x ∈ [1,7] ∪ [9,15]`, and `cascadeLandsBelow17_of_clearPoint` applies. `fast_cell_clear`, `cascadeLandsBelow17_of_fast` and `tailFast_of_nstar` are [L], axioms `[propext, choice, Quot.sound]`, 0 sorry.

`NStarAtMostOne` (every six readings have a 1/7-clear instant in W₀ ∪ W₁) has this record: no six with `ρ₆ ≤ 32` violates it [T, `nstar_two_decision_v1.out`; PROVISIONAL: covering, open cover ⇔ no clear instant; PROVISIONAL: counting tool, finite chain list]. For `ρ₆ > 32` it is open.

## Next steps, in order

1. **`NStarAtMostOne` with a fast top of the six (`ρ₆ > 6ρ₅`).** The same cell lemma one order down: five readings 1/6-clear in reading 1's 1/6-range of W₀ or W₁, with `δ = (1/6 − 1/7)/ρ₅` in `θ` units. Check that the 1/6-range plus the cell stays inside the 1/7-range. This is a new Lean file. It reduces that part to a five-reading statement, which the closure decides for bounded `ρ₅`.
2. **The non-fast remainder of `NStarAtMostOne` (`ρ₆ ≤ 6ρ₅`, `ρ₆ > 32`).** Same pattern: if no consecutive ratio is fast, then `ρ₆` is bounded by the product of the thresholds, and the closure decides the bounded box. If a lower ratio is fast, this is the two-block case of step 4.
3. **Case B (`ρ₇ ≤ 7ρ₆`).** The top block `{ρ₆, ρ₇}` has bounded ratio. If it is fast relative to `ρ₅`, the cell lemma's block form applies (step 4) with the lower five's clear instant. If it is not, `ρ₆ ≤ cρ₅`, and the pattern descends.
4. **The block cell lemma.** If a top block of `k` readings with internal ratios in a fixed box has every reading above `C·max(lower)`, then inside the cell around a `1/(8−k)`-clear instant of the lower readings, the block has a jointly 1/8-clear instant. The constant `C` comes from the block's longest wait for a joint clear instant over its ratio box, which the closure computes exactly. This is R8 with a block in place of one runner. Before building it, check it against the record's two-block template, E646–E669 (source first).
5. **Landing below 17 at each level.** Each reduction needs the lower set's clear instant in W₀ ∪ W₁ (the n* question), not only its existence. Record this per level.

## Not used

No density or Diophantine argument. Covering and counting appear only where tagged.
