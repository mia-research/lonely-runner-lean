# Arrangements that look different and are not (append-only log)

Started 2026-10-02 (owner: "keep a log of what looks like a different arrangement but is not, if we actually think about it").
Convention: readings `ρ_b` = speed minus the subject's, in units of `d_min` (so `ρ_1 = 1`); `R = 8·d_min·t`; `Z(b,j) = ((8j−1)/ρ_b, (8j+1)/ρ_b)`.
Each entry: what looks different, why it is the same (for the quantity named), the check, and whether it is an equivalence of the RESULT
(the cascade's path signature and landing) or only of something weaker. Entries are never edited; a correction is a new entry.

| # | Looks different | Same because | Scope | Check |
|---|---|---|---|---|
| 1 | `ρ` and `λρ` (any common factor) | the path in `R·λ` is the path in `R`; only ratios enter | RESULT (path); `R*` rescales | E263–E315: all runs in `d_min = 1` units |
| 2 | permutations of the labels | a reading's zones depend on its value only | RESULT | sorted order used throughout |
| 3 | two runners at the same speed | two equal readings give one set of zones | RESULT (one reading fewer) | `tail_update_v1`, ties at crossings |
| 4 | different values of an INERT reading (one clear at every visited state and at the landing: `‖R_i ρ/8‖ ≥ 1/8` for all `i`) | blockers and ends decide the path; a clear reading never blocks | RESULT | to be run: `inert_equivalence_v1` (E316) |
| 5 | `ρ` and `ρ + 8` (a whole extra lap) | position `R·ρ mod 8` is unchanged at every integer `R` | ONLY the status of the class events (integer `R`); NOT the path or the landing | E314: fastest runner `(7,9)` has four regimes, `(15,17)`, `(23,25)`, `(31,33)` have none |
| 6 | a runner anywhere in `(1, 7)` versus at its AP value | at `R = 1` it sits at position `ρ ∈ [1, 7]`: clear | `R = 1` lonely, so result "no move" | E313, E314 (strips); NOT the landing when `R = 1` is blocked (E313 `strip3`: the one-runner catalogue predicts it in 229 of 983) |
| 7 | different arrangements with the same single move, e.g. rank 5 lap 1 | one runner in the slot band, the rest clear at its exit | RESULT class | E315: 243 arrangements, four families |

## Checks of the entries above (appended)

- **#4 inert readings `[VERIFIED — exact]`** (`LonelyRunner/experiments/nN/redo/inert_equivalence_v1.py`, 2026-10-02): over 1,500 random arrangements (log-uniform, AP deformed,
  integers `≤ 40`), 7,719 readings are inert (clear at every visited state and at the landing; the smallest excluded), about 5.1 of the 6 non-smallest readings per
  arrangement; 61,752 replacements of an inert reading by a random value clear at the same states: the sequence of states `R_0 … R_n` was unchanged in all 61,752. So the
  result depends only on the readings that block somewhere along the path (typically one or two), the others only through being clear at those states.
