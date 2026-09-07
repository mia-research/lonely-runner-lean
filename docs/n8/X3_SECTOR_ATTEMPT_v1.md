# Sector `x = 3` at `p = 163` — ATTEMPTED-NOT-DECIDED, with the cost measured

2026-09-07. Executes `PREREG_ESCAPE_X3_SECTOR_v1` (`docs/n8/PREREG_X3_SECTOR_v1.md`). Scripts
`experiments/n8/x3_sector_pilot_v{1,2}.py`, `x3_plant_control_v1.py` — **all three audit
clean, 0 float-capable sites**, integer/bitmask only, timing in integer nanoseconds.

**Outcome: `ATTEMPTED-NOT-DECIDED`** — the spec's pre-committed fallback when the projection
exceeds budget. The sector is **not** decided; the ledger stays at **2 of 135**.

## 1. The inversion, and the simplification that makes it well posed

Forward enumeration is `C(567,4) ≈ 4.2 × 10⁹`. The untried move
(`HANDOVER_2026_09_07b` §6.1) is to enumerate the coarse side, `C(81,3) = 85 320`.

**Why the inversion is exact, not an approximation.** By the proved cap table
(`CAP_TABLE_UNIFORM_v1.md`), a coarse speed covers a class **all-or-nothing**. So a coarse
triple partitions the 163 classes into covered and missed — *there are no partially covered
classes* — and the question becomes precisely: can four non-coarse speeds fully cover every
class of `M`, the missed set? Feature (`M`, coarse only) and tested property (non-coarse
coverability) are built from disjoint speed sets.

## 2. Pair-type structure used as a branching rule, per the spec

- **`[P1]` Deficiency prune.** Every non-coarse speed covers at most 2 of a class's 4
  targets, so with `4−d` speeds left every class of `M` must already have `≥ 4 − 2(4−d)`
  covered. At `d = 3` that reads "every class of `M` has `≥ 2`", evaluated in eleven bitwise
  operations as `at2 = ⋁_{s<t} (cov[s] & cov[t])`, prune if `M & ~at2`. It fires immediately
  before the widest branching level.
- **`[P2]` MRV branching** on the uncovered `(class, target)` with fewest covering speeds.

Both are complete: `[P1]` removes only states that cannot be completed within the remaining
budget; `[P2]` reorders branches without discarding any.

## 3. Control — and it passes  `[the load-bearing check]`

Spec control P2, a planted positive: take a seeded 4-set `V`, compute `D(V)`, feed
`M := D(V)` to the **unmodified** search. A completion exists by construction, so the search
must find one; a miss would mean the pruning is unsound and the run void.

    27 fired, 0 MISSED, 3 skipped (|D| < 20).   PASS.

Without this, "no completions found" would be indistinguishable from a broken search.

## 4. Measurement  `[EMPIRICAL — 20 seeded coarse triples, seed 20260907]`

| quantity | value |
|---|---|
| `\|M\|` missed by a coarse triple | min 62, median 66, max 78 (`U_min(3) = 58`) |
| search nodes per triple | 5 130 756 |
| wall time per triple | 21.85 s |
| **projected full run over 85 320 triples** | **517 CPU-hours** |
| coarse triples admitting a 4-speed completion | **0 of 20** |

Against the spec's 6 CPU-hour budget the abort rule fires; 517 h is ~86× over, and ~52 h
even across ten cores. Consistent with scale: Rosenfeld's *entire* `p = 163` verification is
32 h in C++ with four backtracking optimisations, so one sector at 517 h in pure Python is
the expected ~100× interpreter penalty, not evidence of a wrong algorithm.

**What the 0-of-20 is and is not.** With the plant control passing, it is genuine evidence
that the sector is empty — no sampled coarse triple admits a completion, and `|M| ≥ 62 > 58`
throughout. It is **not** a decision: 20 of 85 320 triples, seeded sample, and a sector is
decided only by an exhaustive search returning nothing.

## 5. What would decide it

- **A C implementation.** At the measured ~100× penalty this is ~5 CPU-hours, inside budget.
  This is the honest recommendation: the algorithm is sound and controlled, and the obstacle
  is purely the interpreter.
- Or a sharper prune. `[P1]` only bites at depth 3; a bound that bites at depth 2 would cut
  the tree by roughly the branching factor (~142).

## 6. Ledger

`n = 8` not proved. **Decided cells 2 of 135, unchanged** — `x = 3` at `p = 163` is
attempted, controlled, costed, and not decided. Nothing here touches the other 26 primes or
sectors `x = 2, 1`.
