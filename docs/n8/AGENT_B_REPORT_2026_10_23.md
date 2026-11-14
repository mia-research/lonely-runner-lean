Rules: 5 (no runner at speed 0; readings are differences from a subject of speed > 0), 7 (covering steps tagged [PROVISIONAL: covering]), 15 (exact Fractions, no floats in statements), 16 (new files only), 18 (grades below).

# Agent B report, 2026-10-23: two movers, the 12 clean frozen sets, all movers beyond the least frozen reading

## Files created
Lean (all in `LonelyRunnerFresh/Fresh/`, all compiled with `./check.sh`, axioms `[propext, choice, Quot.sound]`, 0 sorry / native_decide / axiom / admit / unsafe, untagged 0):
- `S2CleanLemmas.lean`: `clear2_symm`, `wit_pt` (point witness), `r1_rect` (rule R1, rectangle form), `big_both` (both movers >= D, via `two_clear_in2`).
- `S2Clean_<set>.lean` for set in 123, 124, 134, 234, 1234, 2345, 23456, 23457, 23467, 23567, 24567, 34567 (12 files): `core_<set>`, `exists_common_clear_<set>`, `land2_all_<set>`.
- `S2Clean_All.lean`: `landing_twoMoverClean_<set>` (12 arrangement-level theorems in the Lands form).
Python (in `experiments/n8/`): `s2_clean_cover_v1.py` (exact box cover), `s2_gen_lean_clean_v1.py` (generator; re-checks every cell with an independent function before emitting), `s2_clean_sample_v1.py` and `.out` (exact random-sample sanity).

## Theorems [L]
For each set, with a = least frozen reading and [lw, rw] the first wide piece:
- `exists_common_clear_<set> (d1 d2 : R) (a < d1) (a < d2) : exists t, lw <= t <= rw, Clear2 d1 d2 t`. No grid, no upper threshold.
- `land2_all_<set>`: the conclusion of `land2C<set>` (IsFirst T of the frozen set with both movers, T the first listed point or first common clear instant in the wide piece) for all d1, d2 > a.
- `landing_twoMoverClean_<set> (c x1 x2) (k m1 m2) ... (hS : Sdisp2 k m1 m2 = F) (a < |x1 - (c+k)|) (a < |x2 - (c+k)|)`: exists T, 1/(8a) <= T, IsFirst, the cascade sequence reaches it, and every fixed point of the cascade from 1/(8a) equals T. Same conclusion as `TwoMoverLandingAll2` with both thresholds D0 replaced by a strict "> a".
Axiom output for all 12 x 3 theorems: `[propext, choice, Quot.sound]`.

## Method and per-set box counts
Box cover of the existence hypothesis only, on the triangle d1 <= d2 (swap by `clear2_symm`). Columns are d1 in [x, x+1] for x = a..D0-1 (no column needed refinement), within a column d2 is split into cells; d1 > D0 = ceil(1/L) is `big_both`. Certificates: R1a (d1 clear on [p,q], 4 d2 (q-p) >= 1), R1b (swapped), P (point witness). Numerals explicit in each leaf.

| set | a | D0 | columns | boxes | kinds |
|---|---|---|---|---|---|
| 123 | 1 | 6 | 5 | 7 | R1a 5, P 2 |
| 124 | 1 | 11 | 10 | 17 | R1a 10, P 6, R1b 1 |
| 134 | 1 | 11 | 10 | 17 | R1a 10, P 6, R1b 1 |
| 234 | 2 | 7 | 5 | 5 | R1a 5 |
| 1234 | 1 | 11 | 10 | 17 | R1a 10, P 6, R1b 1 |
| 2345 | 2 | 9 | 7 | 8 | R1a 7, P 1 |
| 23456 | 2 | 12 | 10 | 12 | R1a 10, P 2 |
| 23457 | 2 | 16 | 14 | 18 | R1a 14, P 4 |
| 23467 | 2 | 16 | 14 | 18 | R1a 14, P 4 |
| 23567 | 2 | 16 | 14 | 18 | R1a 14, P 4 |
| 24567 | 2 | 16 | 14 | 18 | R1a 14, P 4 |
| 34567 | 3 | 12 | 9 | 9 | R1a 9 |

(Columns number D0 - a; the final leaf d1 > D0 is `big_both` and is not counted among the boxes.)

## Regions not covered
None. Every one of the 12 sets was covered completely; no gap appeared, and no cell needed two-piece reasoning.
[OBS] s2_clean_sample_v1.out: 3000 random exact rational pairs per set with d1, d2 in (a, D0 + 3) had a common clear instant in the piece (0 failures); this is a sanity check, not part of the proof.

## Grades and what is not proved
- [L] with [PROVISIONAL: covering] (existence of the common clear instant is a finite box cover) and [PROVISIONAL: counting tool] (`r1_rect`, `big_both`: a clear window of one mover against the period of the other).
- Not proved: the cascade's path inside the wide piece; movers at or below a, or between a and other frozen readings (not required here); frozen sets other than these 12; the other 25 sets; the mixed regime where a mover disparity is below a.
- Nothing committed; no existing file edited; `docs/n8/RUNNING_LOG_order8_v1.md` untouched.
