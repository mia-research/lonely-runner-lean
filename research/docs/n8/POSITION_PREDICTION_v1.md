# Predicting the displaced moments from positions — predictions written before testing

2026-09-14. n = 8, individual isolation, threshold 1/8. BSM is the ground truth throughout
(`experiments/n8/isolation_sets_v1.py` / the `ok_full_transit_sweep_v1` engine, unchanged).
Follows the pattern of `SCALE_RULE_v1`, `RANDOM_PREDICTION_v1` and `BLOCK_PUSHOUT_LAW_v1`:
predictions first, then the test, then the diagnosis.

**The displaced half.** A runner whose moment is later than its bound `1/(8·d_min)`. At the
bound, some runners are in the way (within `1/8`). The positions recorded in
`experiments/n8/out_full_transit_positions_v2.csv` and `out_replications_positions_v2.csv`
suggested the moment is set by one of them.

## Predictions, written before the test

- **Q1 (one runner sets it).** The moment is the first opening `(8k+1)/(8·|D|)` after the bound
  of the difference `D` to one of the runners in the way at the bound. Predicted time: the
  **largest** of those first openings (every runner in the way must have cleared).
- **Q2 (one step suffices).** At the Q1 time the runner is lonely, so the moment equals the Q1
  time exactly.
- **Q3 (the wrap partner).** When exactly one runner shares the slot (a reading divisible by 8)
  and no other runner is in the way at the bound, the moment is `1/(8·d_min) + 1/(8·D)`.

Q1 and Q2 together say: from the bound, one move — to the latest first-opening of the runners in
the way — gives the moment.

## Results  `[VERIFIED — exact, BSM]`

Script `experiments/n8/position_prediction_v1.py`, output `position_prediction_v1.out`.

| family | displaced | moment = one move (Q1/Q2) | Q3 cases | Q3 holds |
|---|---|---|---|---|
| one runner moved from the AP, step 0.05 | 360 | 174 | 54 | 40 |
| every runner moved, deviation ≤ 0.1 / 0.3 / 0.9 | 809 | 285 | 4 | 0 |
| push-out integer families, x = 8..60 | 402 | 147 | 402 | 147 |
| all 8-subsets of `[1,14]` | 8,064 | 4,284 | 8,064 | 4,284 |
| random integers to 500 | 1,657 | 849 | 88 | 36 |

**What is forced.** The moment is never earlier than the one-move time (0 cases in every family):
every runner in the way at the bound must reach its first opening before the subject can be lonely.
So whenever the one-move time is lonely it *is* the moment — Q2 adds nothing beyond "one move is
enough". In `[1,14]` every displaced runner has exactly one runner in the way (integral readings put
only multiples of 8 in the way at the bound), so Q3 there is Q1 restated.

**What is not forced, and what it shows.**
- **Q1/Q2 — one move from the bound gives the moment in 35–53% of displaced runners** (174/360,
  285/809, 147/402, 4,284/8,064, 849/1,657). **Refuted as a rule.** The rest need further moves.
- **Q3 — refuted as a rule.** Holds in 40/54, 0/4, 147/402, 4,284/8,064, 36/88.

**Not established.** What makes a second move necessary — whether it is always a runner that was
clear at the bound and ran out of room during the move (`BufferRoom_v1.lean`'s requirement against
room). That is the next test.
