# Master Problem 1 Safe-Fiber Budget Route SF3 (v1)
**Date:** 2026-03-07  
**Chosen route for MP1.7:** distributed event-spacing / safe-cell occupancy transfer.

## 0) Why SF3 is the right first theorem route
Two simpler routes are already too weak as standalone proof mechanisms:

1. **SF1 pure exit-count budget** is too weak.
   Event-path diagnostics show many tuples with `n_safe_cells < n` even though `B_safe >= n`.
   So one safe opening per run is not enough by itself.

2. **SF2 lower-band-only budget** is false as a universal route.
   The lower-band universality test records many runs with `safe_before < n`.

What remains consistent with the data is:

> safe mass is distributed across event-cell occupancies, not concentrated only in the lower band and not captured only by counting safe regions.

That points directly to an event-spacing theorem.

## 1) Diagnostic facts supporting SF3

### Event-path summary
From `lrc_gap4_s3_event_path_summary_v1.md`:
- `CB violations = 0` over `87,818` `L>n` tuples.
- `H1` (`n_safe_cells >= n`) fails often.
- `H2` and `H4` also fail often.
- Yet for `n >= 6`, the recorded minimum `B_safe` is already strictly above `n` in the tested packs.

Interpretation:
- the safe-fiber budget is real,
- but it is not captured by naive safe-cell counts or single-period bounds.

### Lower-band summary
From `lrc_g4b_lower_bound_universal_v1.md`:
- the claim `safe_before >= n` for every run is false.

Interpretation:
- the budget is not a pure prefix phenomenon.

## 2) Candidate theorem shape

### MP1.7-SF3 (candidate)
Let `C` be a `B_div` component and let the feasible-signature path decompose `C` into event cells `J_1,...,J_m` with occupancies `N_1,...,N_m`.

Define `S subseteq {1,...,m}` to be the set of indices of safe cells, i.e. cells on which `D(b) >= 1`.

Target theorem:

`sum_{j in S} N_j >= n`.

This immediately yields:

`B_safe(C) >= n`.

## 3) Why this is stronger than safe-cell counting
The route does **not** try to prove `|S| >= n`.
That would contradict current diagnostics.

Instead it tries to prove:
- there are enough safe cells,
- and/or the safe cells that do occur have enough occupancy,
so their total weight is at least `n`.

This matches the data pattern:
- few safe cells can still carry large safe mass,
- especially when event intervals are long.

## 4) Inputs already available

### Input A: event-path decomposition
From the feasible-signature path lemma, every component is a 1D walk through event cells with explicit occupancies.

### Input B: run-end coverage package
From Master Problem 1:
- every maximal run ends at a theorem-controlled safe opening,
- so every obstruction block is adjacent to at least one safe cell produced by a certified branch.

### Input C: boundary safe blocks
Boundary-ending runs and lower-band safe fibers give initial and/or terminal safe occupancy contributions.

## 5) Subclaims for SF3

| ID | Target | Role |
|---|---|---|
| SF3.1 | Every theorem-controlled safe opening lies inside a safe event cell of occupancy `>= 1` | converts local openings into weighted safe mass |
| SF3.2 | Successive obstruction runs force distinct safe-cell contributions or disjoint occupancy blocks | prevents overcount collapse |
| SF3.3 | Boundary safe occupancy contributes a fixed baseline at the start/end of each component | injects non-run-derived safe mass |
| SF3.4 | Total safe-cell occupancy across the component is at least `n` | final MP1.7 statement |

## 6) Expected proof architecture

1. Decompose `C` into alternating obstruction blocks and safe blocks along the event path.
2. Use MP1.6 to certify every obstruction block endpoint.
3. Lift each certified endpoint to a safe event cell with positive occupancy.
4. Add boundary safe occupancy.
5. Show overlaps between counted safe occupancies are controlled.
6. Conclude total safe occupancy `>= n`.

## 7) Main risk
The hard point is not existence of safe cells. It is preventing the same short safe cell from being counted repeatedly when many obstruction runs end nearby.

So the key technical subclaim is likely SF3.2, not SF3.1.

Working subclaim note:
- `lrc_master_problem1_sf3_overlap_control_note_v1.md`
- `lrc_master_problem1_sf3_unit_permanent_cover_note_v1.md`
- `lrc_master_problem1_sf3_nonunit_permanent_cover_note_v1.md`

This note adopts one useful input from the external O1 draft:
- repeated overlap collapse should be treated as a permanent-cover chain problem,
- but the stronger external closure claims are not imported without theorem-grade cleanup.

Later review of the combined O1/O2 closure draft adds one more scoped support fact:
- for a unit runner `e`, the number of interior `z=0` event positions in open `B_div` is exactly `e-1`;
- this is packaged in `lrc_g4b_unit_z0_event_count_lemma_v1.md`.

But the review memo
- `lrc_o1_o2_closure_review_memo_v1.md`
also shows why that count does **not** by itself prove
`B_safe >= n`:
- runner-wise event counts do not automatically convert into distinct safe-cell occupancy,
- coincident events can collapse onto the same fiber,
- so SF3 still needs explicit overlap/transfer control.

## 8) Program consequence
MP1.7 should now be attacked as an event-cell occupancy theorem, not as:
- a lower-band theorem,
- a run-count theorem,
- or an isolated exit theorem.

That is the first route worth turning into a full theorem note.
