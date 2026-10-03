# The cascade, mapped: what is established and what is open (v1)

2026-10-02. Written during the autonomous run of E317–E320 (owner away). Running record: `RUNNING_LOG_order8_v1.md` (E263–E320). Exceptions: `EXCEPTIONS_LOG_v1.md`.
Look-alike arrangements: `ARRANGEMENT_EQUIVALENCES_v1.md`. Plan: `EXHAUSTION_PLAN_v1.md`. Scripts and outputs: `LonelyRunner/experiments/nN/redo/`.

Owner's aims for this run: (a) a definitive finite list of arrangements; (b) a complete understanding of the cascade. **Neither is reached.** What is reached is listed below
with its grade. The owner's view, recorded here as given: a complete finite list may be achievable, because scale, the variations and the conjecture's own constraints reduce
the arrangements. Nothing below contradicts that; the evidence for and against is in §7.

Grades: **[LEAN]** proved in the Lean tree, axiom-clean (`[propext, Classical.choice, Quot.sound]`); **[EXHAUSTIVE]** a finite computation that covers every case of a stated class
(with its numerical caveats stated); **[CHECKED]** exact computation on a stated sample (a count, not a proof); **[DERIVED]** derived by hand and checked on samples; **[SEARCH]** heuristic
search (a lower bound on an extremum, never a proof); **[OPEN]**.

## 0. Conventions

Readings `ρ_1 = 1 < ρ_2 < … < ρ_7`: each other runner's speed minus the subject's, in units of the smallest (the subject has some speed `s > 0`; nobody is stationary; any `s` gives the same
separations). `R = 8·d_min·t`. A reading `ρ` blocks the OPEN zone `Z(ρ, j) = ((8j−1)/ρ, (8j+1)/ρ)` on lap `j ≥ 0`; it is clear in between (closed windows `[(8j+1)/ρ, (8j+7)/ρ]`).
The cascade starts at `R = 1` and, at a state `R`, moves to the largest EXIT `(8j+1)/ρ` among the zones containing `R`. The first lonely instant is the first point not in any zone: the right end of the
connected component of the union of the open zones that contains `R = 1` (or `R = 1` itself).

## 1. Proved in Lean (all axiom-clean; nested repo `LonelyRunner/`)

| module | statement |
|---|---|
| `SegmentWindowN` | six readings of common period `P`: order seven gives `t₇`; for every mover reading `x` with `x·P` not whole the arrangement is lonely at some `t ≤ t₇ + P(1/(4a)+1)`, `a = ‖xP‖`. The window of a one-mover segment is not uniform at the lattice points (`T ~ P/(4a)`), and every non-lattice point is lonely |
| `IntegerGridN` | `clear_rational_iff`, `clear_of_dvd_not_dvd`, `clear_two_adic`; `lonely8_of_no_multiple_of_eight`; `lonely8_two_adic_window` |
| `IntegerDisplacementN` | at the grid instant `a/8` a reading is in the way iff `8 ∣ x`; `move_at_grid`; the displacement of a slot-0 reading to its leaving edge in slot residue and shift (`lonely_of_displacement`, `slower_clear_iff`, `clear_at_exit_iff`); `nextOpening_rational`, `inWay_rational_iff`, `move_rational_le_iff` at every state `K/(8m)`; `lonely8_example` |
| `ClassDeviationN` | at a class instant a reading `d(8n+ε)` sits at `a·ε` eighths (the lap is invisible): `circDist_class_deviation`, `class_blocked`, `class_clear_of_band(_neg)`, `lapped_fastest` |
| `ZoneLinkN` | if the exit of `x`'s lap-`j` zone lies in `y`'s lap-`j'` zone: `y` slower ⇒ `j' ≤ j`; `y` faster ⇒ `j < j'`; equal readings cannot link |
| existing (earlier sessions) | `RealEightN` (real speeds reduce to whole numbers); `OrderEightCasesN` and `lonelyRunnerAt8_iff_residual`; `OneFreeN.lonely_of_one_free_eight`; `DeformationN`, `PathWindowN.lonelyRunnerAt8_of_window : WindowBound → LonelyRunnerAt8` (the single owed hypothesis is the window); `doors_agree`; `ProgressionPairN.pair_law`; `SeparationN`, `CascadeTransportN`, `HandoffDriftN` |

**What the Lean tree does not have:** the conjecture at eight runners; `WindowBound`; the effective-crossing rule; the hop/birth-death statement; the cell enumeration.

## 2. The structure of the path under deformation (computed on exact arithmetic)

- **Hop = birth or death of a lonely component [CHECKED, 1,716 crossings, 0 exceptions].** The spot (left end of the first lonely component) moves continuously while its component persists; a forward
  hop is exactly the death of the first component (length → 0 at a start–end tangency), a backward hop exactly the birth of an earlier one. The AP is the arrangement whose four lonely components are all
  tangencies (`R = 1, 3, 5, 7`).
- **Effective-crossing rule [CHECKED: 598 of 600 next-change predictions exact; the other 2 are crossings at `s = 1`, unobservable; locality 170 of 170].** The move sequence changes only at: A (a zone's start crosses a
  state `R_i` and the zone outlasts the setter), A′ (the setter's own start crosses `R_i`), B (a `j ≥ 1` zone's end crosses the landing while straddling it), C (a blocker's end meets the setter's end), D
  (the setter's exit meets its own state); start–start crossings never matter; the first differing move is out of state `i` (or `i−1` for C). Exception X6 (a touch, not a crossing) in `EXCEPTIONS_LOG_v1.md`.
- **Inert readings [CHECKED, 61,752 replacements, 0 changes]:** the result depends only on readings that block somewhere on the path (typically 1–2 of 6); the others only through being clear at the visited states.
- **Strips [CHECKED]:** `R = 1` is the landing iff no reading's `ρ mod 8` lies in `(−1, 1)`; for one to four deformed runners of the AP the first event survives exactly outside the strips `ρ ∈ (7, 9) + 8ℤ`; inside a strip
  the landing is set by the frozen runners' own positions (the entering-edge reader at position 7 gives `≥ 1 + 2/ρ_E`), not by the AP; the one-runner catalogue (E313) is complete for `ρ ∈ (0.35, 14)`.
- **Frozen runners [CHECKED, 90 runs and 2,449 steps ×2]:** the lonely set is the frozen runners' lonely set intersected with the movers' clear sets; the landing always lies in a component of the frozen set; the movers select.
- **Links [LEAN + CHECKED on 2,717 links].** The link rule is `ZoneLinkN`.
- **Results by the cascade's own path [CHECKED]:** 6,347 arrangements give 719 distinct paths; 43% have no move; B1 members give 22 results in 47 members; the AP-based families' counts of distinct results flatten,
  random/grid/integer families keep growing.
- **Grid scale invariance [DERIVED + CHECKED]:** the status of every integer-`R` event depends only on `ρ mod 8`; it does not carry over to the path (E314: a lapped fastest runner has four regimes at one lap and none at two).
- **Lap compression fails [CHECKED, E320]:** lowering a reading by a whole lap makes the landing later in A than in A′ in 4,922 of 31,585 pairs (largest excess 2.53): there is no monotone reduction of laps.

## 3. The one-lap window, exhaustively [EXHAUSTIVE, floating-point LP with exact checks]

`path_tree_par.py`, `sup_exact_v1.py`. Window `ρ_7 ≤ 9` (every reading within one lap of the smallest). Symbolic cascade over polyhedral cells (every condition is homogeneous linear in `ρ`); a branch is kept only if its cell
has an interior point; the tree branches on the setter and on possible straddlers.
- **The tree is finite: 27,517 nodes, 9,651 terminal cells, deepest path 29 (28 moves), 0 branches cut at depth 60.** Hence every arrangement of the window lands.
- **Exact supremum of the landing over the window: `R* ≤ 26433/2209 = 11.9660479855…`** (`2209 = 47²`, `26433 = 27·11·89`); the maximising cell's closure has the rigid vertex `ρ = (1, 16715503/7123545, 47/15, 726761/173745, 47/9, 15463/2673, 2209/297)`; the landing is `89/ρ_7`, lap 11, after a 27-move chain
  `7.1 6.1 5.1 4.1 7.2 3.1 6.2 5.2 2.1 4.2 6.3 7.4 5.3 3.2 6.4 4.3 5.4 7.6 2.2 1.1 5.6 4.5 2.3 5.7 6.8 4.6 7.11`. This is a limit; the owner's suspected maximum 12 is not exact in this window (`11.966…`).
- **Checks against the exact cascade:** 256 exact test arrangements (250 random + six of the hardest known) carried down the tree: 0 violations of the partition (at most one child; none ⇒ the exact cascade lands) and of soundness (each node's path is a prefix of the exact path).
- **Consequence by closedness:** the lonely condition is closed and the landing is bounded, so every arrangement of the closed window, including tied and integer ones, is lonely at some `R ≤ 11.97`, i.e. `t ≤ 11.97/(8 d_min)`.
- **Sensitivity to the cell-thickness threshold [CHECKED]:** the tree built with `TT = 1e-6`, `1e-9` and `1e-12` is identical: 27,517 nodes, 9,651 terminal, deepest 29, supremum `11.966048` in all three. No cell has thickness between `1e-12` and `1e-6`.
- **Caveats [OPEN]:** (i) the LP is floating point; a cell thinner than `1e-12` would be missed under all three thresholds; an exact rational Farkas certificate for every pruned branch would close it;
  (ii) the supremum is over closures.

## 4. Wider windows

TWO-LAP WINDOW (`ρ_7 ≤ 17`) [EXHAUSTIVE, same method and caveats as §3]: 343,070 nodes (12.5 × the one-lap window), 117,070 terminal, deepest path 29, 0 branches cut, 0 violations of the partition and soundness checks, 2,832 s on 9 workers.
**The supremum of the landing over this window is again `26433/2209 = 11.966048`**, attained by the same one-lap cell: the second lap adds cells and no later landing. THREE-LAP WINDOW (`ρ_7 ≤ 25`) [EXHAUSTIVE, same method and caveats]: 2,092,661 nodes, 747,487 terminal, deepest path 34, 0 branches cut, 0 violations of the partition and soundness checks, 13,975 s.
**The supremum of the landing is again `11.966048`**, same one-lap path and vertex: the second and third laps add cells and no later landing.
The late-state dictionary (largest `ρ_7` among NODES whose state can exceed `T`; interior nodes included, so it is not a landing statement): `T = 3: 25.0, 5: 25.0, 7: 24.65, 9: 24.40, 10: 8.70, 11: 8.37, 11.5: 7.86`. Reading: an intermediate state above 9 can occur at `ρ_7` up to 24.4, but a state above 10 (and so any landing above 10) occurs only with `ρ_7 ≤ 8.70`, inside the one-lap window. The same statement for terminal landings at `T = 7` is NOT established by this dictionary (terminals were stored only for the one-lap run).
CORRECTED (E330): exact members of the two-lap tree cells include 59 arrangements with a landing above 7 and `ρ_7 > 9` (largest `ρ_7` 16.19, e.g. `ρ_7 = 15.137`, `R* = 9.5793`, opener (7,18), 25 moves); the earlier statement that searches found none described the reach of the searches, not the cascade. Landings above 10 occur only with `ρ_7 ≤ 8.52` among those members. Earlier searches (hard-set search) did not reach these; hill-climbs from lap-added copies of the extremal arrangement reach only `R* ≈ 6.8–6.9` in windows 17 and 25.
Number of moves is not bounded by the one-lap window: tight fast clusters give paths of 41 moves with `R* = 2.27` (E320 search), landing small.

## 5. The slow runner below a cluster (Case C)

For a slow runner `d_min = 1` below six readings with smallest `c`, the slow runner is clear on `R ∈ [1, 7]`; so the arrangement lands in `[1, 7]` iff the six readings have a lonely `R ∈ [1, 7]` (Window Lemma W6).
[SEARCH] sup of (first lonely `R' ≥ c`)/`c` over six-reading sets: about `1 + 5/c` for `c = 9, 16, 30` (1.48, 1.31, 1.18); tight clusters `≤ 1.71`. The searches at small `c` (1.5–8) are lower bounds only and the known hard arrangement (R* ≈ 11.9, `c = 2.35`) shows they
undershoot there, so W6 for small `c` is false by that example; for large `c` it is untested beyond the search. **W6 is [OPEN].**

## 6. Why `R ≈ 12` [DERIVED + CHECKED]

In the hardest arrangements the first surviving class event is `a = 12` or `14` (even); the odd events die for every lap because the signs of the deviations of the pinned pair `(y ≡ a, y ≡ −a mod 8)` are lap-independent
(`δ_7, δ_3, δ_5 > 0` kill `a ≡ 1, 3, 5`; `a ≡ 7` dies by magnitude); `a = 12 ≡ 4 (mod 8)` puts the odd readings at the middle of the clear arc (tolerance `|12δ| ≤ 3`) and the even ones in the slot, so it needs `12δ_{2,4,6} ∈ [1, 7] (mod 8)`. The landing is the displaced event just before 12.

## 7. Toward (a) and (b): evidence and limits

For a finite list. **For:** (1) the one-lap window is finite (9,651 cells), (2) the landing there is bounded by a rational `< 12`; the path-signature classes of the AP-based families flatten; late landings (`R* > 5`) only found with small spread; (3) the closure argument turns a bounded landing into
a statement for every arrangement of the window, including the degenerate ones; (4) in Lean, `lonelyRunnerAt8_of_window : WindowBound → LonelyRunnerAt8`, and a universal landing bound would give the window.
**Against / open:** (1) the windows above one lap (two-lap run in progress; wider ones not attempted); (2) the cluster case (W6) is a statement about six readings at arbitrary scale; (3) the LP is floating point (caveat §3); (4) the number of moves is unbounded across windows (41 found); (5) the lap-compression
monotonicity is false, so wider windows do not reduce to the one-lap window by peeling laps; (6) no argument is yet known for why a universal bound `R* ≤ 12` should hold; the one- and two-lap trees give the same supremum (11.966), so there it does not grow with the window.
For (b): the cascade's moves from a state are its definition; what is mapped is how the path changes under deformation (§2) and its complete behaviour in the one-lap window (§3). There is no closed-form rule for the landing from the readings.
