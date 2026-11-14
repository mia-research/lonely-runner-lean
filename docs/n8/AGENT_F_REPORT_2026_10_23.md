Rules: 5 (no runner at speed 0; readings are differences from a subject of speed > 0), 7 (counting and covering steps tagged), 15 (exact Fractions, no floats), 16 (new Lean files only), 18 (grades below).

# Agent F report, 2026-10-23: two movers with at least one mover at or below the least frozen reading a, all 37 frozen sets

## Result
For ALL 37 frozen sets of `Sdisp2` and ALL pairs of positive mover disparities with `min(d1, d2) <= a`, a first lonely instant exists and the cascade from `1/(8 min(d1,d2))` lands on it (Lean `IsFirst`, fixed point, `Lands` form). Together with `S2Clean_All` / `S2Later_All` (both movers above `a`), `S2Below_Complete.lean` gives, for every frozen set and ANY two positive disparities (no other hypothesis), the cascade landing from `1/(8 min(a, d1, d2))`. Nothing partial: no frozen set and no region left out.

## Mechanism [OBS] and what the Lean statement is
- Exact study (`experiments/n8/s2below_study_v1.py`, `_v2.py`, `s2below_study_v1.out`, 147,888 random exact pairs; `s2below_grid_v1.py`, `.out`, 85,123 grid points, d1 in {k/16} plus {1/32,1/64,1/128}, d2 in {m/16}): the landing equals the first common clear instant of the pair in the first F-lonely piece (lap order, clipped to `[1/(8 d1), oo)`) holding one, with ZERO mismatches against the full cascade (`lf.cascade_land`). The mechanism asserted in the brief reproduces the cascade in every sample (this is the definition of the first lonely instant read piece by piece; the Lean form is `isFirst_char`, `first_in_piece`, `landing_in_piece`).
- Piece depth (number of F-pieces from the start to the landing piece), by regime: (ii) `d1 <= a < d2`: max 4 (grid: 4 at 13457; random: 3). (i) both `<= a` with `d1 >= 1/8`: max 4. (i) with `d1 < 1/8`: unbounded in the sense that it grows as the movers shrink: max 187 pieces / 31 laps (set 23567), 140 (1356), 108 (2345), 107 (14567) in the random sample; grid max 16 at `(1/128, 1/16)`. No uniform piece cap exists and none is used in the proof.
- The proof therefore proves EXISTENCE of one lonely instant (any lap) and takes IsFirst from the cascade (`exists_fixed_of_lonely`); it does not locate the landing piece. Which piece holds the landing is [OBS] only.

## Lean files created (all in `LonelyRunnerFresh/Fresh/`, each compiled singly with `./check.sh`; axioms propext, choice, Quot.sound only; 0 sorry/native_decide/axiom/admit/unsafe; untagged 0)
- `S2BelowCore.lean`: `fclear_add_nat`, `fclear_lap` (generic period-1 shift, every set); `ex_of_piece`; `isFirst_char`, `first_in_piece`, `landing_in_piece` (conditional landing at an arbitrary left end L: no frozen-clear instant below L has both movers clear, `[L,R]` frozen-clear holding a common clear instant => first lonely instant in `[L,R]`, first common clear instant at or after L); `exists_isFirst_of_lonely`, `landing_of_ex` (one lonely instant => Lands form from `1/(8 min d1 d2)`); `run_lemma`; `small_II`, `small_I_pos`, `small_I_neg`, `small_A`; `near_int`.
- `S2Below_<set>.lean`, 37 files (123 124 125 134 234 1234 1235 1236 1245 1246 1256 1345 1346 1356 1456 2345 12345 12346 12347 12356 12357 12367 12456 12457 12467 12567 13456 13457 13467 13567 14567 23456 23457 23467 23567 24567 34567): `small<set>`, `col<set>_<i>`, `exists_below_<set>`: for all `0 < d1 <= a`, `d1 <= d2`, `exists t > 0, FClear F t /\ Clear2 d1 d2 t`.
- `S2Below_All.lean`: 37 theorems `landing_twoMoverBelow_<set>` (hypotheses: `0 < d1`, `0 < d2`, `min d1 d2 <= a`, `Sdisp2 k m1 m2 = F`; conclusion Lands form with start `1/(8 min d1 d2)`).
- `S2Below_Complete.lean`: 37 theorems `landing_twoMoverComplete_<set>` (positivity only; start `1/(8 min(a, min d1 d2))`), dispatching to `S2Below_All`, `S2Clean_All` (12 clean sets), `S2Later_All` (25 others).
- Python in `experiments/n8/`: `s2below_study_v1.py` (+ `s2below_study_v1.out` from `_v2.py`), `s2below_grid_v1.py` (+ `.out`), `s2below_cover_v1.py`, `s2below_gen_v1.py` (generator; re-checks every box with an independent function before emitting). Modified none of the existing files; `RUNNING_LOG_order8_v1.md` untouched; nothing committed.

## Method (how the unbounded range d1 -> 0, d2 -> oo is closed)
Existence is only needed at SOME instant, so the witness may lie in any lap (`ex_of_piece`, frozen pieces repeat each lap).
- `d1 <= 1/8` (analytic, uniform over sets; `1/8` is a frozen-clear point `tau0` for every integer set within 1..7): put `t = n + tau0`, `n = ceil(1/(8 d1) - tau0)`, so `d1 t` is in the first clear window `[1/8, 1/4)` and `d2 t = j n + j tau0 + eps t` for `d2 = j + eps`.
  (a) `d2 >= D0 = ceil(1/(4 w0))`, `w0` the widest frozen piece: rule R1 (`small_A`) inside the first `d1` window [PROVISIONAL: counting tool].
  (b) `distInt d2 >= d1/2`: `run_lemma` at `tau0` (an arithmetic progression of step `d2` cannot stay within `1/8` of the integers for more than `1/(4 distInt d2)` terms); the laps used fit in the `d1` window because `d1 <= 1/8` [PROVISIONAL: counting tool].
  (c) `|d2 - j| < d1/2`, `1 <= j <= D0`: phase of `d2` moves from `j tau0` by at most `1/8`; patterns `(j, sign, tau0, N)` found by exact search per set (all existed; listed in each file docstring).
- `1/8 <= d1 <= a`: finite box covers with lap-shifted pieces, 3 to 6 columns and 8 to 47 boxes per set (certificates R1a and point witnesses; deepest lap used 2, set 12456), [PROVISIONAL: covering].
- The reduction of `d1 <= d2` to the unordered case uses `clear2_symm` and `min_eq_left/right`.
- One compile issue: `col13457_0` needed `maxHeartbeats 4000000` (400000 timed out); the generator now emits 4000000 for all columns; 13457 and 14567 were recompiled in final form, the other 35 compiled with 400000 (same proofs).

## Grades
[L] for every theorem named above, axioms propext, choice, Quot.sound. [PROVISIONAL: covering]: the box covers (columns `1/8 <= d1 <= a`). [PROVISIONAL: counting tool]: `run_lemma`, `small_A`, `small_II`, `r1_rect` by inheritance. [OBS]: all study and grid output.

## Not proved
- Which frozen piece holds the landing, as a closed formula (only [OBS]; depth grows without bound as both movers shrink).
- The cascade's intermediate setters and path.
- Membership of arrangements in the 37 sets (`Sdisp2_cases` is in `TwoMoverLandingAll.lean`; theorems are stated for any `(k, m1, m2)` with the given `Sdisp2`).
- No regime where the freeze mechanism fails to match the cascade was found (0 mismatches in 233,011 exact samples); this is [OBS].
