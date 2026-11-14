# The Native Lean Development for Eight Lonely Runners: Cascade, Cells and Displacement

*Version 23_7, 2026-10-09 (supersedes `MANUSCRIPT_v23.md` to `MANUSCRIPT_v23_6.md`, which are kept unchanged; twenty-nine rules-audit or name-convention findings across six checks are fixed here, and §10 records what is not carried from v21 and v22). **DRAFT. Not the record.** `MANUSCRIPT_v21.md` remains the manuscript of record until the author promotes anything. This file does not edit, supersede or alter v21 or v22. It writes up the development in `LonelyRunnerFresh/` (37 modules, `Fresh/*.lean`, checked by `./check.sh`) and the exact data in `experiments/n8/` that accompany it, as recorded in `RUNNING_LOG_order8_v1.md` entries E428 to E443. Requested by the owner, 2026-10-09: "Ok lets write this up in manuscript and then we can look at a paper".*

**Status: n = 8 is NOT proved.** The conjecture at eight runners, `LonelyRunnerEight`, is stated in `Framework.lean` and is tagged `-- STANDING: OWED`; nothing in this folder proves it. Every statement of "the displacement is forced" that has been formalised is an `iff` with the conjecture, so it is a restatement and not a step toward it (`PathForm.displacementPath_iff`, `Cascade.cascadeForm_iff`, `Localisation.candidateScaleForm_iff`, `Doors.global_door_iff`). The existence content is isolated and stated as owed: the transversal condition (§8), `CompatAll`, `PathLonelyBound` and `ConjectureGivesBound`. What the development does prove is the machinery around that content: where the first move and the landing sit, how an isolation is displaced under a deformation of the arrangement, and the exact arithmetic of the instants involved.

**Latest whole-folder run (E443, 2026-10-09):** `./check.sh` exit 0; 37 modules; 19,767 lines; 24 warnings (unused variables and linter), no error; scan of code (comments stripped) for `sorry`, `native_decide`, `axiom`, `admit`, `unsafe`: 0 in every file; untagged `Prop` definitions: 0; 976 `#print axioms` lines, 967 read `[propext, choice, Quot.sound]`, 9 read a subset of it; no `sorryAx`. Lean was not run for this manuscript; the counts in §9 were recomputed by `grep`.

**Rules:** v4, 1, 5, 6, 7, 13, 15, 16, 18, 21.

---

## 0. Conventions

**Ground rules of the owner's framework** (`RULES_n8_v4.md`; owner messages by id in `OWNER_INSTRUCTIONS_EXTRACT_v1.md`).

1. Existence of the isolation is established at the AP and the grid. Any deviation from them displaces the isolation, and the cascade shows where and why it goes there. What is to be shown is that the displacement is forced (rule 1).
2. No runner is ever stationary or at speed 0. Every speed is positive and no two speeds are equal. Readings are differences from a subject of positive speed; every statement is about differences. Examples use positive speeds (rule 5).
3. Exact only. Lean's `ℝ`, exact fractions in the data; no floats, no decimals offered as fact (rule 15). A float-steered search is marked as steering and carries no weight.
4. The method is the boundary set method or the cascade (`IsMove`, `CascadeFixes`). The cascade is the object; a statement proved about a proxy of it is not a statement about it (owner guidance, Appendix A).
5. Density, coverage, cap, move budget and termination are not the shape of any argument offered here (rule 7). A counting step used as a tool carries `[PROVISIONAL: counting tool]` and a covering or complement step carries `[PROVISIONAL: covering]`, each at the step with the supported claim named, as the module files do (79 occurrences in `Fresh/*.lean`). Provisional means the owner may withdraw the relaxation of 2026-10-05 and the steps resting on it.
6. Nothing is imported from the older repository `LonelyRunner/`. Its Lean files were read for the argument only; every theorem here is re-derived, and the module headers record the corresponding older declaration (Appendix B). Names of older-repository declarations are written in plain text, not in code font, so that every code-font Lean name in this file is a name in `Fresh/*.lean`.

**Grades.**

| Tag | Meaning |
|---|---|
| [L] | A Lean theorem, named and present in `Fresh/*.lean`, with a `#print axioms` line in the module. The axiom set is `[propext, Classical.choice, Quot.sound]` unless stated. |
| [OBS] | Exact data with its population stated. Never an argument. |
| [reasoned] | An argument not formalised. |
| [OWED] | Not done. A `def … : Prop` carrying `-- STANDING: OWED` is a statement that is asserted nowhere, not a proof. |
| [PROVISIONAL: counting tool], [PROVISIONAL: covering] | As in rule 7, at the step, claim named. |

"Restatement" means an `iff` with the conjecture: it moves no grade and proves no existence.

---

## 1. Objects (`Framework.lean`)

All objects are defined from first principles, in a folder that cannot import the older repository (E428).

* `distInt x` is the distance from `x` to the nearest integer.
* `IsArrangement v`: `v : Fin 8 → ℝ`, every `v i > 0`, `v` injective. `IsOrderedArrangement v`: strictly increasing and positive.
* `disparitySet v k`: the absolute differences `|v i − v k|`, `i ≠ k`. `IsDmin v k m`, `IsSubjectDmax v k m`: least and greatest disparity of subject `k`.
* `IsolatedAt v k t`: every other runner has `distInt ((v i − v k)·t) ≥ 1/8`. `Isolation v k`: an isolated instant `t > 0` exists. `GloballyIsolatedAt v t`: every subject isolated at `t`.
* `CompleteResidues idx`, `IsAP v`, `IsGrid v` (speeds `v₀ + idx j · d`, `idx` a complete residue system mod 8), `IsGridWithDeviation v`.
* Cascade objects, on a finite set of positive disparities `ds`: `InWay d t` (`distInt (d·t) < 1/8`), `nextOpening d t` (the instant at which `d` stands at exactly 1/8 past a lap line), `IsMove ds t t'` (go to the largest next opening among the runners in the way; stay if none is), `CascadeFixes ds t₀` (the cascade from `t₀` reaches a fixed point), `CandidateScaleClear ds`.

**The claims, all tagged OWED in `Framework.lean`.**

| Claim | Statement | Status |
|---|---|---|
| `LonelyRunnerEight` | every arrangement, every subject, has an isolation | [OWED]; the target |
| `GridGlobalIsolation` | a grid is globally isolated at every `a/(8d)`, `a` a unit mod 8 | tag in `Framework.lean` stays OWED; proved as `Grid.gridGlobalIsolation` [L] |
| `DisplacementPath` (a) | along a continuous path of arrangements from a grid, every point has an isolation | [OWED]; `PathForm.displacementPath_iff` [L] |
| `CascadeForm` (b) | from `1/(8 d_min)` the cascade reaches a fixed point | [OWED]; `Cascade.cascadeForm_iff` [L] |
| `CandidateScaleForm` (c) | some opening of some flank is clear for every disparity | [OWED]; `Localisation.candidateScaleForm_iff` [L] |

**One theorem in `Framework.lean`:** `lonelyRunnerEight_imp_displacementPath : LonelyRunnerEight → DisplacementPath` (specialise the conjecture along the path) [L].

**A defect in the framework file, found and kept** (E429). `IsGridWithDeviation` is vacuous: every arrangement satisfies it (take `d = 1`, `idx j = j`, `e j = v j − v 0 − j`; the example is in `Where.lean`). "Grid plus deviation" carries information only through the choice of grid (gap `d_min` through the subject) and the coordinates (slot, ε). `Framework.lean` was left unchanged because other modules compile against it; a replacement is not needed, since the conversion is a coordinate change (E431). Also, `GridGlobalIsolation` as stated is a sufficient-instants statement; it is not the φ(8) law's "exactly" (`Grid.grid_extra_instant`).

---

## 2. The grid layer

### 2.1 Grid and octagon (`Grid`, `Octagon`)

All [L], symbolic in all arrangements.

* `Grid.octagon`: eight points pairwise at circle distance at least 1/8 form a regular octagon; every difference is a whole number of eighths (v9 Theorem 2, difference form). One counting step, tagged `[PROVISIONAL: counting tool]` (an injective `Fin 8 → Fin 8` is onto). Inherited by `deviation_integral`, `deviation_iff`, `ap_globalIsolation_iff`, `Octagon.globallyIsolatedAt_iff_octagon`.
* `Grid.deviation_position`, `deviation_survives`, `deviation_necessary`: v9 Theorem 5, without the counting step.
* `Grid.deviation_iff` (v9 Theorem 6 in full): with `e 0 = 0`, global isolation at `a/(8d)` holds iff every `e j · a/d` is an integer `w j` and `j ↦ idx j · a + w j` is a complete residue system mod 8.
* `Grid.gridGlobalIsolation : GridGlobalIsolation`; `Grid.ap_globalIsolation`; `Grid.ap_not_even`.
* **The φ(8) law, in full:** `Grid.ap_globalIsolation_iff`: the AP is globally isolated at `t` iff `t = a/(8d)` with `a` a unit mod 8, for every real `t`, so "no other instant" is included. In one period of the AP `1..8` the four instants are 1/8, 3/8, 5/8, 7/8 (`Cycle.ap18_four_before_return`).
* `Octagon.isolatedAt_iff_gaps` (v9 Theorem 1 in unsorted infimum form); `not_exactly_seven` (by symmetry of circle distance alone, no counting); `globallyIsolatedAt_iff_octagon` (v9 Theorem 2); `globallyIsolated_pairDist_eighths`; `integer_flank_isolated_iff`.

**Exceptions understood** (E429), each with the hypothesis that fails:

| Exception | Lean | Why |
|---|---|---|
| speeds `1 + j + 1/2` are globally isolated at 1/8 yet `e 0 = 1/2` | `Grid.unanchored_not_integral` | the hypothesis `e 0 = 0` fails; a common deviation is a common rotation |
| the grid `idx j = 9j` is globally isolated at `1/(72d)`, not of the form `a/(8d)` | `Grid.grid_extra_instant` | it is the AP with common difference `9d`; "exactly `a/(8d)`" needs `d` to be the primitive step |

### 2.2 D_max (`DMax`)

Shifting runner `j` by `8·c_j·d` keeps the indices a complete residue system (`dmax_complete`), so the shifted grid is globally isolated at every `a/(8d)` (`dmax_globalIsolation`). At those instants every reading changes by a whole number of laps (`dmax_reading_unchanged`), so isolation of any subject is the same before and after (`dmax_isolatedAt_iff`) [L]. A D_max shift displaces nothing.

### 2.3 Cycle and grand return (`Cycle`)

All [L]. `GrandReturnAt v t`: every `v i · t` is a whole number.

* Integer speeds with gcd `G`: grand return iff `t = z/G` (`grandReturn_iff`); the least positive one is `1/G` (`grandReturn_isLeast`). Position patterns have period `τ` iff `τ` is a grand return (`positions_period_iff`). Isolation of every subject repeats under a grand return (`isolatedAt_add_grandReturn`). A subject's reading pattern has least period `1/Gk`, `Gk` the gcd of its disparities (`readingPattern_least_period`); `isolatedAt_add_gcdDiff` gives isolation period `1/Gk`. Minimality of the isolation predicate's period is [OWED].
* Real speeds: a grand return exists iff all speeds are pairwise rational multiples (`exists_grandReturn_iff`); speeds `1, √2, 3, …, 8` have none (`sqrt2_no_grandReturn`). Periodicity of the isolation predicate for incommensurable speeds is not stated.
* **Cycle of the slowest speed versus grand return** (`grandReturn_eq_rotations`, `grandReturn_slowest_iff`): the grand return is always a whole number `m/G` of slowest rotations and equals one slowest rotation iff the slowest speed divides every speed. **Counterexamples, with the reason:** the AP `3..10` (`ap3_counter`): 3 does not divide 4, so the slowest rotation 1/3 is not a grand return and the grand return is `t = 1`; the AP `3, 5, …, 17` (`ap_odd_counter`): 3 does not divide 5 and the isolation period is 1/2. For the AP `1..8` both are `t = 1` (`ap18_cycles_equal`). Whether the owner means absolute speeds or disparities is open; both versions are in the file.
* **D_min displacement, exact:** changing one speed by `δ` displaces the reading of the changed runner by `δt`, its partner by `−δt`, every other reading by 0 (`reading_update`). Runner `m` moved by `c` grid steps displaces each reading at `t = a/(8d)` by exactly `([i=m] − [k=m])·c·a/8` laps (`single_change_reading`). Subject `k` keeps the old instant iff no other index is congruent to `idx k` mod 8 (`isolatedAt_grid_iff`). A single-runner move keeps the residues complete iff 8 divides `c`, that is only a D_max shift (`shiftIdx_complete_iff`); otherwise the new residue collides with exactly one other runner and exactly `m` and that runner lose the old instant (`single_change_losers`, `[PROVISIONAL: counting tool]`: an injective `Fin 8 → ZMod 8` is onto). Nothing claims that the displaced isolation lands anywhere; that is the conjecture.

### 2.4 Grid to grid (`GridToGrid`)

[L], displacement only. `matched_reading_shift`: the new reading at the new instant equals the old reading at the old instant plus `(Δ'a' − Δa)/8` laps, for any steps and bases. `new_isolatedAt_iff`, `isolatedAt_transfer`; `instants_meet_iff` and `ratio_odd_of_meet`: the old instant is a new-grid instant iff `d'/d` is a ratio of odd integers. **Counterexample** (`counterexample_double`): `v j = 1 + j` is globally isolated at 1/8; `v' j = 1 + 2j` has no isolated subject at 1/8 and is globally isolated at 1/16, because 1/8 = 2/16 and 2 is not a unit mod 8. Path form: `path_reading_affine`, `reading_reaches_eighth`. [OWED]: `d'/d` with 2-adic valuation above 1; relation of a mid-path arrangement to a grid. Where a displaced isolation lands is the conjecture and is not claimed.

### 2.5 Localisation (`Localisation`)

[L]. `lonely_ge_bound` (v9 Theorem 7); `localisation` (v9 Theorem 9: the opening is constructed, not searched); `candidateScaleForm_iff` (restatement); `certificate_iff` (v9 Theorem 10, integer disparities; not bridged to an arrangement's `disparitySet` in this module, and bridged for integer flanks by `Octagon.integer_flank_isolated_iff`); `certificate_periodic` (`#print axioms` reads `[propext]`).

---

## 3. Cells, carving and the gate

### 3.1 Cells (`LonelyCells`)

For every finite set of positive disparities, all [L].

* `isClosed_lonelySet`: the isolation set is closed.
* `cell_of_lonely`: every isolation instant lies in a cell `[u, w]`, a maximal closed interval of isolation instants; `u` is the largest last opening before `t`, `w` the smallest next entry after `t`.
* `cell_left_end_is_opening`: `u = (k + 1/8)/x`, runner `x` at exactly 1/8, `x` in the way just left of `u`. `cell_right_end_is_entry`: `w = (k' + 7/8)/y`, runner `y` at exactly 7/8.
* `cells_upTo_finite`: finitely many cells meet `(0, b]` (one counting step, `[PROVISIONAL: counting tool]`).
* **Where the isolation goes, in the cascade's own objects:** `landing_is_first_cell_left_end` (the cascade's landing is the left end of the first cell), `cascade_lands_at_first_cell`, `states_below_landing` (every state is at most the landing, every earlier state is not lonely; no bound on moves).
* `cell_width`: `w − u = (k' + 7/8)/y − (k + 1/8)/x`. `degenerate_opener_ne_closer`, `degenerate_cell_isolated`: a one-point cell is a touch between two different runners (record L7). `ap_first_cell_is_touch`: for the AP disparities `{1, …, 7}` the first cell is the single point 1/8, opened by runner 1, closed by runner 7. `opener_eq_closer_window`: if one runner is both opener and closer, the cell is its whole window, of width `3/(4x)`.

No cell is claimed to exist for every disparity set; that is the conjecture.

### 3.2 Carving (`Carving`)

The calculus of the lonely set under adding a runner [L]: `lonelySet_insert` (the lonely set of `insert d ds` is the lonely set of `ds` intersected with `clearSet d`); `killed_iff`, `cell_killed_iff` (a cell dies exactly when it lies inside one open zone of the added runner; `[PROVISIONAL: covering]`, containment in a zone, supports the carving calculus and no existence claim); `cell_survives_of_wide` (a wide cell survives, `[PROVISIONAL: covering]`, supports "a cell survives an added runner"); `cell_gap` (consecutive cells are at least `1/(4 d_max)` apart, for every `ds`; `[PROVISIONAL: covering]`, a zone against gap width, supports only the gap bound and no existence claim); `cells_ordered` (an ordering fact on the cells of a family, not a covering claim); `zone_meets_at_most_one_cell` (`[PROVISIONAL: covering]`, one zone against the cells of a family, supports `cell_gap` and the carving calculus, no existence claim); `ap_first_cell_leftmost`, `ap_touch_by_carving` (the AP's first cell `[1/8, 7/(8k)]` shrinks to the single touch at `k = 7`).

**The L2 counterexample, and why** (`L2_fails_without_order`). The record's lemma "the added runner never kills the first cell" holds only when the added runner is at least as fast as all others. Counterexample: `ds = {8}`, added `d = 1`. A slower runner's zone is wider than the first cell. The theory that was wrong is the unconditioned L2; the hypothesis that fails is the order.

### 3.3 The gate (`Gate`, with `Types` for the paused part)

For a disparity set with least element `m` and `R = 8·m·t`, all [L]:

* `dmin_clear_first_window`: `m` is never in the way for `R ∈ [1, 7]`. `dmin_inWay_gate`: `m` is in the way on `(7, 9)` and its next opening there is exactly `R = 9` (`[PROVISIONAL: covering]`, one runner's zone against the window `(7, 9)`; supports `no_lonely_in_gate`, no existence claim).
* `no_lonely_in_gate`, `landing_not_in_gate` (`[PROVISIONAL: covering]`, same supported claim): no isolation and no landing lies in `(7, 9)`. `landing_gt_seven_iff`: a landing above 7 occurs exactly when `[1, 7]` holds no isolation. `move_from_first_window`: one move from `R ≤ 7` lands below 9. `first_state_above_seven`: the first state above 7, if any, lies in `(7, 9)`. `gate_move_ge_nine`: every move from inside the gate lands at `R ≥ 9`.
* `opener_closer_is_fastest` (L4: opener = closer implies fastest runner), proved as stated.
* `staircase_setter`, `staircase_card`, `staircase_rank` (L5): bound the instant at step `n`, not the number of moves. `[PROVISIONAL: counting tool]`.
* `lonely_interval_ceases_only_at_touch` (L7): a lonely interval of a continuously deformed arrangement ends only through a touch (two different runners, one at an opening, one at an entry). With `cell_persists`, `cell_limit_lonely`, `strictly_clear_iff`.
* `gate_lands_at_nine_iff` (L1(d)): the move from the first state above 7 lands exactly at 9 iff no runner in the way there has next opening past 9. This is not proved to hold; it is the content of `StrongGate` (§6.2).

### 3.4 Doors (`Doors`)

[L]. `instant_is_opening`: every instant of any move sequence from `1/(8 d_min)`, including the start, is an opening `(j + 1/8)/d` of some disparity `d`. `landing_is_opening`, `landing_runner`, `landing_isLeast`: the landing is the least positive isolation and some disparity `d` has `d·t* = j + 1/8` exactly (either `d_min` with no forward move, or the last setter with `x·t* = lap + 1/8`). `zone_run`: a forward move starts in the setter's zone and ends at its right end; the next setter is a different runner whose zone contains the new instant. A tie of setters breaks nothing: both stand at exactly 1/8 at the landing, on different laps.

`doors_agree`: the five doors (A) an isolation exists, (B) the cascade fixes, (C) its instants are bounded, (D) some flank has a lonely opening, (E) every runner is in the way at finitely many cascade states, are equivalent. `global_door_iff`: each door is `↔ LonelyRunnerEight`, so **each is a restatement**. C to B and E to B rest on a step tagged `[PROVISIONAL: counting tool]` (supports "the cascade cannot move forever below a bound" and "a finite union of finite index sets is not all of ℕ"); no counting-free argument was found.

### 3.5 Where the first move and the landing sit (`Where`, `WhereProofs`)

`Where.lean` states ten claims as Props (tagged OWED there); `WhereProofs.lean` proves each as a theorem of exactly its stated Prop [L]: `clearIffPosition`, `positionAtStart`, `startBlockers` (start blockers are exactly slot 0 or slot 7 with ε > 0, proved for all arrangements; E427's 0 exceptions in 345,304 sets was a check), `startOpening`, `startDisplacement` (`(1−ε)/ρ` for slot 0, `(2−ε)/ρ` for slot 7), `firstMoveIsLargestStartOpening`, `enteringEdgeEveryMove` (in the stronger form `enteringEdge_anyMove`), `enteringEdgeSlotSeven`, `landingIsFirstIsolation`, `cascadeFindsIsolation`. The slot-7 hypothesis of the record's item E299 is idle: `enteringEdge_firstMove` removes it, and what remains is true of every move. `cascadeFindsIsolation` inherits one counting tag from `Cascade.exists_fixed_of_lonely`.

### 3.6 Dilation and chain laws (`Dilation`, `ChainLaws`, `Protection`)

* `Dilation` [L]: the setter reads exactly 8N + 1 eighths at the new instant (`setter_reading_eighths`); every reading shifts by `gap·d/x` with `0 < gap < 2` (`gap_pos`, `gap_lt_two`, `reading_shift`); `t'/t < 9/7` when the setter's lap is at least 1 (`dilation_lt_nine_sevenths`); the lap is at least 1 whenever `t ≥ 1/(8m)` (`one_le_lap_of_bound`); consecutive setters differ (`consecutive_setters_ne`); the link rule L6 (`link_slower_lap_le`, `link_faster_lap_ge`, `link_rule_seq`): a slower later setter's lap is at most the earlier setter's, a faster one's is at least one more. No move-count bound is stated.
* `ChainLaws` [L], every finite set of positive disparities, every cascade sequence: the single inequality `later_lap_of_ge` (if `x` sets the move on lap `j`, every `y ≥ x` in the way at a later instant is on lap `≥ j + 1`). From it: `setter_recur_lap` (a recurring setter recurs on a strictly higher lap; E323 and E315), `lap_seq_mono`, `setter_not_twice_in_row`, `per_lap_decrease` and `word_strictAntiOn_lap` (E332: setters on one lap are strictly decreasing in speed; tested on 372,642 sets before it was a theorem). The maximality clause of the move is not needed. **Exception understood:** the setter of a step need not be unique (two runners can share the largest next opening, for example `x = 1` on lap 0 and `y = 9` on lap 1 at `t ∈ (7/72, 1/8)`), so the "word" depends on the choice at a tie; the rank form is proved for every choice and tied setters are always on different laps (`setters_same_step_distinct_lap`). `link_faster_persistent` is the persistent faster clause; the slower clause has no persistent form.
* `Protection` [L]: for a reading that starts at the lower edge `P + 1/8` of its window, `telescope_lower_edge` gives position `P + 1/8 + Σ gap_k·b/(8x_k)` after `n` forward moves; `protection` (if `Σ b/x_k ≤ 3` it stays strictly inside the window, never in the way); `recapture_sum_gt`; `no_recapture_of_faster`; `no_recapture_one_move`; `protection_offset`. **The limit, exact:** `offset_recapture_example` (disparities `{1, 17/20}`: the reading 17/20 is clear at `t = 1` and recaptured at 9/8 with ratio sum 17/20 ≤ 3, so protection needs the lower edge). `owner_iff_fails`: the pasted line "b/(b/c+b/d+b/e) ≥ 1/3 ⇔ b/c+b/d+b/e ≤ 3" is false in both directions (`b = 2, c = d = e = 1`; `b = 1/4, c = d = e = 1/2`). As a bound over a whole chain it would be a move budget (rule 7), so it is a local tool. Exact check [OBS]: all 7-subsets of `[1, 20]` with gcd 1, 63,753 (setter, later state) pairs, 0 violations, 2,795 recaptures, smallest sum at a recapture 216/65 (`experiments/n8/protection_bound_check_v1.py`).

### 3.7 Cascade and path form (`Cascade`, `PathForm`)

* `Cascade`: the cascade's basic facts as lemmas (`nextOpening_eq`, `lt_nextOpening`, `not_inWay_at_nextOpening`, `isMove_unique`, `exists_isMove`, `isMove_mem_openings`). `fixed_is_first_isolation`; `cascadeFixes_iff_isolation`; `cascadeForm_iff : CascadeForm ↔ LonelyRunnerEight`. One counting step in `exists_fixed_of_lonely`, `[PROVISIONAL: counting tool]` (an injection of ℕ into a finite set of openings), supports "the sequence cannot move forever below a lonely instant".
* `PathForm`: `displacementPath_iff : DisplacementPath ↔ LonelyRunnerEight` (sorting, the straight-line path from the AP `(1, …, 8)`, relabelling; no counting) [L].

---

## 4. Displacement laws

### 4.1 The pair law at the AP (`PairLaw`)

Readings `d : ℕ → ℝ`, hypothesis `|d j − j·c| ≤ ρ·c`, class `a` odd with mirror `b = 8 − a`. The radius is a hypothesis of a local displacement statement, never a bound on the cascade. All [L].

* `opening_at_u`, `entry_at_w`: `u_a = a²/(8 d_a)` is an opening of `d_a` (lap `k`, `8k + 1 = a²`) and `w_a = a(8 − a)/(8 d_b)` is an entry of `d_b` (lap `k'`, `8k' + 7 = a·b`).
* `interval_lonely`: for `ρ ≤ 1/22`, `[u_a, w_a]` lies inside the lonely set. The argument is symbolic in the reading `j` (residue `R` of `j·a` mod 8: `res_ne_zero`, `res_one`, `res_seven`, from `a² ≡ 1` mod 8). The radius enters only through three core inequalities (`core_lower` at 1/14, `core_upper_small` at 1/22 for `a ≤ 5`, `core_upper_seven` for `a = 7`, tight at `j = 2`).
* `u_le_w_iff`: `u_a ≤ w_a ⇔ a·d_b ≤ b·d_a`. `pair_law`: at 1/22, one of the two mirror classes is a cell. `pair_both_iff`: both are nonempty iff `a·d_b = b·d_a` (their common boundary, `pair_touch`); `pair_exclusive`. `interval_isCell`, `interval_ends`, `interval_width` tie it to §3.1.
* `instant_lonely_record`, `pair_law_record`: the record's own statements at the record's radius `c/20` (the left end is lonely when `a·d_b ≤ b·d_a`; one of each mirror pair keeps an instant lonely).

**Correction of the v9 interval claim.** The statement "instant `a` survives as the interval `[a²/(8 d_a), a(8−a)/(8 d_{8−a})]`" (docstring of the older ProgressionPairN, E69; v9 Part I-1 row 1) is false at the record's radius `c/20` for class 7. The older Lean proves only that every runner is clear at the left end `u_a` [reading, not re-proved]. `record_interval_fails`, `record_interval_fails_c20`, `cx_class_seven` [L]: for `c = 1`, `d_1 = 1 − ρ`, `d_2 = 2 + ρ`, `d_j = j` otherwise, `ρ ∈ (1/22, 1/8)` and at `ρ = 1/20`, the record's right end `7/(8 d_1)` is not lonely, because runner 2 sits at 14/8 at the start of the interval and enters its zone before runner 1; this happens exactly when `7(2 + ρ) > 15(1 − ρ)`, that is `ρ > 1/22`. **Exact** [OBS, `pair_law_class7_check_v1.py`]: at `ρ = 1/20` the record's right end 35/38 is not lonely, runner 2's entry 75/82 is lonely and lies below it; at `ρ = 1/22` the two coincide at 11/12. So 1/22 is the sharp radius of the interval statement: `interval_lonely` holds up to 1/22 and the class-7 family fails above it [L]. The isolation is displaced, not destroyed: `displaced_cell` gives the cell `[7/8, 15/(8(2 + ρ))]` for `ρ ∈ [1/22, 1/14]` (runner 7 opens, runner 2 closes). **The theory that was wrong:** "the closer is the mirror runner `8 − a`"; the closer is whichever runner enters first. Next-tightest per-(class, reading) radii 3/46 (class 5, reading 6), 1/15 (class 7, reading 3), 7/90 (class 7, reading 6, lower side) are [OBS], exact fractions outside Lean. `pair_law` itself is not affected. v10 of the compilation rewords the row (E436).

### 4.2 The AP neighbourhood (`APNeighbourhood`)

[L]. The older 56-lemma proof for AP speeds `c + j + e_j`, `|e_j| ≤ 1/32` of the gap, is re-proved symbolically in the offset `j = i − k`: `interior_clear` (one argument for all interior readings), `end_clear`, `end_clear_seven` (by the mirror `e ↦ −e(7 − n)`). `ap_isolated_of_le`: the same isolation for radius `ε ≤ 1/16`, twice the older hypothesis; `ap_nbhd_isolated` recovers 1/32. The displacement is bounded (`apT_displacement`: `|apT e k − 1/8| ≤ 2ε/7`, or `|… − 7/8| ≤ 2ε/7` for an end runner of class 7). **Sharpness and the exception:** `cx_not_isolated`: at `ε = 1/15` (`e0 = 1/15`, `e1 = −1/15`, `e7 = 1/15`, others 0) the named instant 15/104 of runner 1 is not isolated; `d_min = 13/15`, runner 7's reading `92/15` exceeds `7·d_min = 91/15`, and at 15/104 that reading is 23/26, only 3/26 from a lap. The pair forcing `ε ≤ 1/16` is `(1, 7)` (or `(6, 0)` mirrored): `6 + 2ε ≤ 7(1 − 2ε)` iff `ε ≤ 1/16`. The isolation is not lost: `cx_isolated_displaced` proves runner 1 isolated at 135/488 [L, a concrete check]; that this is where the cascade from 15/104 settles after three moves (states 15/104, 135/736, 135/608, 135/488) is [OBS, exact Fractions, one arrangement, `ap_nbhd_counterexample_cascade_v1.py`], not formalised.

### 4.3 The pair law for grids (`GridPairLaw`)

Subject the slowest runner, all others ahead; disparities `d_j > 0` with integer offsets `o_j` whose residues mod 8 are a complete nonzero system; class `a` odd, opener `A` with `o_A ≡ a`, closer `B` with `o_B ≡ −a`; `u_a = o_A·a/(8 d_A)`, `w_a = o_B·a/(8 d_B)`. All [L].

* `setting_of_complete`, `setting_mirror`, `interior_res`; `opening_at_u`, `entry_at_w` (`8 n_A + 1 = o_A·a`, `8 n_B + 7 = o_B·a`); `u_le_w_iff` (`u_a ≤ w_a ⇔ o_A d_B ≤ o_B d_A`); `pair_cover` (one of the two ratio conditions holds; both iff the touch). The pair law is algebra; the content is the interval.
* `grid_interval_lonely` under `ClassHyp`, a displacement hypothesis on **rescaled** positions (every other runner within `η ≤ 1/8` of its grid position `o_j·a/8` at both class instants); `grid_interval_isCell`, `grid_interval_width`, `grid_pair_law`, `grid_instant_lonely`, `drift_le`, `eta_sharp` (1/8 cannot be raised).
* **Exceptions understood.** The naive radius `|d_j − o_j·d| ≤ ρ·d` is the wrong theory for grids with large offsets: the drift of a runner over the interval is `d_j·(w − u)`, proportional to its offset. `ap_case`, `ap_exception_eta`: for `o = (1, …, 7)` the AP exception of §4.1 is exactly the failure of `ClassHyp` for runner 2 at the same `ρ = 1/22`. With one large offset `o = (1, 2, 3, 4, 5, 8m + 6, 7)`: `F1_interval_fails` (the interval contains an instant at which runner 6 is on a lap line, for `ρ ≥ 3/(28m + 24)`, a threshold decaying like 1/m), `F1_instant_lonely` (the class instant itself stays lonely for every `m`), `F1_displaced_cell` (the closer changes from runner 1 to runner 6), `F2_both_instants_fail` (for `7/(56m + 90) < ρ < 21/(56m + 88)` neither class instant of the pair `(1, 7)` is lonely although `|d_j − o_j| ≤ ρ`), `F2_example_cell` (`m = 1`, `ρ = 1/20`: the cell `[485/558, 35/38]`, opened by runner 6 at lap 12, closed by runner 1), `F2_example_cascade` (the cascade from `u_7 = 245/282` makes one move to 485/558 and fixes; displacement 5/13113). The record's own GridPairLawN hypothesis (deviation at most `1/C` after rescaling) is not contradicted; the wrong theory is reading it as a bound in units of the grid step. Owed: subjects with runners on both sides; a link from `ClassHyp` to an explicit offset-dependent bound on deviations.

### 4.4 Zero margin and touches (`ZeroMargin`, `TouchTheory`)

The AP's isolations are zero-margin touches (§4.6), so the first-order theory of a touch is the displacement law there.

**`ZeroMargin`** [L]; counting steps tagged `[PROVISIONAL: counting tool]` in `ratio_necessary`, `ratio_sufficient`, `ap_classes`. The separation step in `gordan` uses Mathlib's Hahn–Banach as a separation tool, not a covering step.

* Exact survival, not only first order: the moved reading is `d·t0 + e(A + e·B)` with `A = δ·t0 + d·τ`, `B = δ·τ` (`reading_expand`), so at `A = 0` the sign of `B` decides. `exact_touch_survival`: for `e > 0` and `e(|A_i| + |B_i|)` below each runner's margin, the moved instant is lonely iff every opener has `0 ≤ A_i + e·B_i` and every entry has `A_i + e·B_i ≤ 0`; `touch_survives_of_strict`, `touch_fails_of_violation`.
* `helly_one_dim`: a `τ` exists iff for every opener `i` and entry `j`, `δ_j/d_j ≤ δ_i/d_i`. `free_touch_survives`: a touch with no opener or no entry survives every direction (`free_example`: disparities `(1, 2, 4)` at `t = 1/8`). `scaling_B_obstruction`: for `δ = c·d` no affine `τ` survives when both an opener and an entry are present; the non-affine move `t0/(1 + e·c)` survives exactly (`scaling_nonaffine_survives`).
* **The AP:** at `a/8` (`a` odd, at most 7) runner `j` is an opener iff `j = a` and an entry iff `j + a = 8`; every other runner has slack at least 2/8 (`ap_classes`, `div8_slack`). The survival form is `σ_a = δ_a/a − δ_b/b`, `b = 8 − a`; `sigma_antisymm : σ_b = −σ_a`; hence for every `δ` one instant of each mirror pair survives to first order (`ap_mirror_survival`). `survival_form_is_linearisation`: `b·d_a − a·d_b = e·a·b·σ_a` exactly. `pair_law_is_survival_form`: the pair law's condition `u_a ≤ w_a` is exactly `0 ≤ σ_a`. So the pair law is this first-order condition with no higher order, and its radius 1/22 is the range where the margins of the non-critical runners hold.
* Conjugates: `conjugate_pair_exists`, `ratio_condition`: an (opener `d_i·t`, entry `d_j·t`) instant exists iff an (entry, opener) instant exists (`t' = 7t`), and with `d_i : d_j = p : q`, `p` odd, the exact condition is `p + q ≡ 0` mod 8 (`ratio_condition_needs_coprime`: `p = 2`, `q = 6` has 8 dividing `p + q` and no instant). `commensurable_mirror`: if every `d_i·T` is an integer, then `t' = mT − t0` swaps every role and preserves every circle distance.
* `gordan`, `every_direction_survivor_iff`: for finitely many forms, either some direction violates all or they are positively dependent. For the AP, `σ_1 + σ_7 = 0` and `σ_3 + σ_5 = 0` (`ap_touch_positive_dependence`, `ap_every_direction_survivor`). Positive dependence for general arrangements is [OWED], not asserted.

**`TouchTheory`** [L] (E440; corrects E439).

* `wholeset_conjugate`: for every finite family of positive disparities and every lonely instant `t0` there is `N ≡ 7` (mod 8) such that `N·t0` is lonely, every opener of `t0` is an entry there and every entry an opener. No common period and no hypothesis beyond positivity. The critical readings flip under any `N ≡ 7` (mod 8) (`scale_flip`); readings with positive slack keep their margin when `N = 8m − 1` is chosen by simultaneous recurrence (`simult_approx`, `[PROVISIONAL: counting tool]`: recurrence of finitely many reals mod 1 by compactness of the torus, supports `wholeset_conjugate`; the tag was added by the main session). The critical readings are automatically commensurable with one another.
* `cones_cover_iff`, `violating_direction_exists_iff`: a touch and its conjugate cover every first-order direction iff there is no opener, or no entry, or exactly one of each (`[PROVISIONAL: covering]`, direction-space covered by the two cones; supports only the first-order survival statement, no existence claim) (`singleton_touch_survives`, `touch_conjugate_cover`, `not_cover_iff`). A killing direction exists iff there is an opener and an entry and not both are single; the killing orders are two openers around one entry, or two entries around one opener. Exact example `(1, 2, 3, 4, 5, 6, 11)` at 3/8: openers the disparities 3 and 11, entry 5; for `δ = (1, 4, 9, 16, 25, 36, 77)` neither touch survives for any `τ` and small `e` (`E439_example`, `violation_kills`).
* Second order at the AP pair `(a, 8 − a)`: `affine_survival_classification` (an affine move survives iff `σ_a > 0`, or `σ_a = 0` and `δ_a = 0`), `sigma_zero_nonaffine` (at `σ_a = 0` the move `a/8 → (a/8)/(1 + e·r)`, `r = δ_a/a`, survives exactly), `window_trichotomy` (`u_a < w_a` iff `σ > 0`; equal iff `σ = 0`; `w_a < u_a` iff `σ < 0`), `ap_pair_survives_every_direction`: for every `δ`, one of each mirror pair has a lonely moved instant for all small `e`; the survivor along an affine move is the one with `σ > 0`; at `σ = 0` both survive, along the non-affine move. `scaling_case` is the test case `δ = c·j`.
* `blocked_pair_conjugate_example` (re-run exactly by the main session): `d = (1, 7, 16/7, 2, 3, 4, 5)`, `t0 = 1/8` is lonely (opener 1, entry 7); 7/8 is not lonely (16/7 stands at exactly 2); the whole-set conjugate 15/8 is lonely with roles swapped.
* Not done: positive dependence for general arrangements; uniqueness of the lonely instant near `a/8` at `σ = 0` [reasoned only]; no bound on `N`.

**Reading of the zero-margin route** [PARTIAL]. The displacement of a touch is governed by one linear form per touch, `σ = δ_i/d_i − δ_j/d_j`. A touch with a single opener and a single entry, together with its whole-set conjugate, covers every first-order direction (`touch_conjugate_cover` [L]; "covers every direction" is a covering statement, `[PROVISIONAL: covering]`, supports only "no first-order escape direction for these families", not the conjecture). This accounts for the AP, its two relatives (§7) and the pair law. It stops where touches stop: for generic arrangements the isolation sits in positive-width cells, where there is no touch to deform (§4.6); a touch with two or more critical runners on one side can be killed to first order together with its conjugate, and the isolation then sits elsewhere. It does not state why an isolation exists.

### 4.5 Block landing (`BlockLanding`, `BlockLanding2`)

For `S = C ∪ F` with `tC` the core's landing, `wC` its first cell's right end, `u` the first point at or after `tC` clear for `F`. All [L], conditional on a lonely point existing; no existence is claimed.

* `BlockLanding`: `lonelySet_union`; `landing_union_ge_u` (every positive lonely point of `S` is at least `u`), `landing_union_eq_u` (`u ≤ wC` gives landing `u`), `landing_union_gt_wC` (`wC < u` gives landing beyond `wC`), `landing_eq_u_iff`, `typeX_iff` (`wC < u` iff no point of `[tC, wC]` is lonely for `F`; `[PROVISIONAL: covering]`, a complement statement, supports the landing decomposition and no existence claim), `landing_decomposition`, `type_trichotomy`. The ordering of `F` above `C` is idle.
* Displacement formula: `inWay_bound_iff` (`x` is in the way at the start iff `|sres m x| < m`); `nextOpening_bound` (then `8m·nextOpening = 1 + (m − s)/x`); `core_displacement` (for a core with `R_C = 1` and cell width at least `1/(4x)`, the landing of `C ∪ {x}` is that value); `singleton_core_displacement` (for `C = {m}`, `x ≥ m` no exceptions); `u_multiple` (`x = 8mk` gives `1 + m/x`); `singleton_one_multiple` (`C = {1}`, `x = 8k` gives `1 + 1/x`).
* **Exceptions understood:** a degenerate core cell (width 0) means some core runner reads exactly 7/8 at `tC`, at `R = 1` exactly `7m, 15m, 23m, …` (`cell_degenerate_iff`, `degenerate_at_bound`); any block runner in the way then pushes the landing past the cell whatever its size (`typeX_degenerate_iff`). A cell of positive width absorbs the push iff it is at least the push; `typeX_imp_narrow`, `not_typeX_of_wide` (`4·width·x ≥ 1` is sufficient, not necessary; `[PROVISIONAL: covering]`, a window width against a push size, supports `typeX_iff` and no existence claim). Instances, re-run exactly by the main session: `{1, 7, 8}` lands at `R = 9/7` (`t = 9/56`, not `9/64`); `{2, 12, 15}` lands at `R = 3/2` (`t = 3/32`; the formula's 6/5 is `u`, not the landing) (`touch_block_example`, `narrow_cell_example`). A claim made during the work, "past-the-cell forces zero width", is false: `{2, 12, 15}` has positive width.
* `BlockLanding2` (each statement below that is a covering or complement statement carries `[PROVISIONAL: covering]` here, with the supported claim named): `clearFirst_zone_form` (`[PROVISIONAL: covering]`, supports `typeX_iff_cover`; `u` is given exactly by "every point of `[a, u)` lies in a zone of `F`"); `typeX_iff_cover` (`[PROVISIONAL: covering]`, supports `typeX_iff`; the landing falls past the core's first cell exactly when the zones of `F` cover that cell); `cover_singleton_iff` (`[PROVISIONAL: covering]`, supports `typeX_iff_cover`; one runner's zones cover a cell iff one single zone does); `two_zone_needed_iff` (`[PROVISIONAL: covering]`, supports `typeX_iff_cover`); `landing_iff_first_open_cell` (`[PROVISIONAL: covering]`, supports the next-cell landing recursion; the landing of `C ∪ F` is in the first cell of `C` that the zones of `F` do not cover and equals the first `F`-clear point of that cell); `landing_past_least` and `landing_recursion` (both `[PROVISIONAL: covering]`, same supported claim); `touch_next_cell`, `narrow_next_cell`.
* **Limit found** [OBS]: in the test sets AG used (selected by AG's script, core of one to three runners, block of one to four, values to 59; a non-exhaustive test set, not a population, and no claim is made beyond it), 8 of 1,167 type-X first cells needed three or more zones to cover; example core `{13}`, block `{6, 45, 32, 2}`, first cell `[1/104, 7/104]`, landing 25/256. No exact condition is proved for covers by three or more zones. The instance theorems do not identify the later cell's left end in Lean; that is from the Fractions check only.
* **The data against the imported parameters** [OBS] (`block_rule_cascade_v1.py`, exact; 5 hand values and 10,109 sets against a least-lonely-opening search, 0 mismatches). For core `{1}` and block `x = 8k` the landing is `R = 1 + 1/x` at every `x` tested to 1024; for two readings the cascade moves exactly when the ratio mod 8 leaves `[1, 7]` (14,328 pairs, 0 mismatches). The `T` at which the past-the-cell type disappears grows with the core (suprema 6, 34, 62 for three-element cores with values to 12, 24, 40). Reading: neither the block size `f` nor a threshold `T` is a parameter of the cascade at the first landing; the content found is the core's cell, the block's residue mod `8·d_min`, and a displacement of order `1/x`. (The two older-repository propositions that carry `f` and `T` are recorded in §6 as imported.)

### 4.6 Path laws and their classification (`PathLaws`, `PathClassify`)

Paths of arrangements `v : ℝ → Fin 8 → ℝ`, subject `k` fixed, `isoSet v k` the parameters with an isolation. All [L] unless marked.

* **`PathLaws`.** Openness with an explicit modulus: a lonely `(s0, t0)` with margin `e` keeps `t0` lonely for nearby `s` and `t` (`isolatedAt_transfer_s`, `isolatedAt_transfer_t`, `openness_s`, `openness_t`). Closedness: a limit of lonely instants with finite limit `t0` is lonely and `t0 > 0` (`lonely_limit`, `lonely_limit_pos`, `not_isolatedAt_zero`). **Loss dichotomy, no bound assumed** (`isoSet_dichotomy`): if `s_n → s0` with a lonely `t_n` at each, then either `t_n → ∞` or `s0` has an isolation. If `s0` is not an interior point of the isolating parameters, every lonely instant at `s0` has a runner at exactly 1/8 and every cell at `s0` is a single point (`loss_needs_boundary`, `loss_no_interval`); a lonely interval of positive width at `s0` gives a neighbourhood (`isoSet_open_of_cell`). **Escape to infinity occurs when the limit is not an arrangement:** speeds `(1, 1+s, 3, …, 8)`, subject the runner of speed 1, lonely at `t = N + 1 + 1/8` for `s = 1/(2(N+1))`, none at `s = 0` where two speeds coincide (`escapeEx_escape`, `lonely_time_escapes`). Owed, named, never assumed: `PathLonelyBound` (a uniform bound on lonely witnesses; cap-shaped, rule 7) and `SuccessorIsolation` (every isolating parameter has a neighbourhood of isolating parameters). `isoSet_eq_of_owed` records that the two together give an isolation along the whole path (real-line induction); it is **not offered as the argument**.
* **`PathClassify`.** The conjecture gives `isoSet = Icc 0 1` (`lre_isoSet_eq`) and hence `SuccessorIsolation`, right-isolation and closedness (`lre_imp_successorIsolation`, `lre_imp_right`, `lre_imp_closed`). `SuccessorIsolation` alone gives only a start interval (`successorIsolation_only_openness`). Exact topology: `isoSet = Icc 0 1` iff 0 is in it, it is left-closed, and right-isolation holds (`isoSet_eq_iff_leftClosed`, each hypothesis necessary); closedness is exactly "no escape point" (`isClosed_iff_no_escape`); at an escape point every witness sequence tends to infinity (`escape_witnesses_diverge`). Along admissible grid-start paths the conjecture is iff (left-closed and right-isolation) (`lre_iff_leftClosed_right`), and the bound plus successor on every such path gives the conjecture (`owed_pair_imp_lre`). **These are restatements.** `pathLonelyBound_iff_localBound` (by compactness, `[PROVISIONAL: covering]`, supports `isoSet` closedness); `not_localBound_imp_touch` (no local bound at `s0` means every lonely instant at `s0` is a touch); `not_localBound_imp_seq`. Whether the conjecture implies `PathLonelyBound` is `ConjectureGivesBound`, **[OWED]**, neither proved nor refuted.
* **A theory that is wrong, proved so.** "A strictly clear instant exists at every parameter" is false (`strictForm_refuted`): at the AP `(1, …, 8)`, for every real `t` some runner `i ≠ 0` has circle distance of `i·t` at most 1/8, by Dirichlet with seven runners (`ap_not_strict`, `[PROVISIONAL: counting tool]`, the pigeonhole inside Mathlib's Dirichlet lemma). So the AP's isolations are all touches (`ap_const_path_isoSet`). A margin-positive form of openness is the wrong object. The isolations the framework starts from sit at zero margin.

---

## 5. Boundary arithmetic and decompositions

### 5.1 Boundaries (`Boundaries`)

[L], integer disparities where stated. `opener_unit`, `entry_unit`, `touch_units`: for a boundary `t = p/q` in lowest terms, an opener `x` with `x·t = k + 1/8` has cofactor `c = 8x/q` with `c·p = 8k + 1`, `p` and `c` odd, `8 | q`, `c ≡ p` (mod 8); an entry has `c·p = 8k' + 7` and `c ≡ −p`; where one runner opens and another enters at the same instant their cofactors satisfy `c + c' ≡ 0` (mod 8). The AP's four touches carry the four units 1, 3, 5, 7 at 1/8, 3/8, 5/8, 7/8. This needs a rational boundary; for real disparities the form is that `m = 8xt` is an integer `≡ ±1` mod 8 at the boundary of `x` (§5.4). `width_congruence`: the cell between opener `(x, lap k)` and entry `(y, lap k')` has width `m/(8xy)`, `m = (8k'+7)x − (8k+1)y`, `8 | (m + x + y)`; so a touch (`m = 0`) needs `x + y ≡ 0` (mod 8) and the narrowest positive width `1/(8xy)` needs `x + y ≡ 7`. `half_lonely_iff_odd` and `finset_half_lonely_iff` (1/2 is lonely iff all disparities are odd) and `lonely_mirror` (the lonely set is symmetric under `t → 1 − t`) need integer disparities, that is a period. `four_cells`: for integer disparities with no multiple of 8 and some element at least 4, the instants `a/8` (`a` odd) are all clear and each interval `(j/8, (j+2)/8)`, `j` odd, contains a blocked instant, so there are at least four cells (`[PROVISIONAL: covering]` at this step: a blocked instant in every interval of length 1/4 against the spacing of the four unit instants, supports "at least four cells" and no existence claim; the general-n form `units_separated`, §5.6, carries `[PROVISIONAL: counting tool]` at its pigeonhole). `unit_lonely`, `blocked_between`, `half_nbhd_lonely`, `mirror_opening` are the supporting lemmas.

[OBS] (integer populations: all gcd-1 7-subsets of `{1..N}`, `N` = 14, 18, 22: 3,431 / 31,788 / 170,213 sets). Smallest positive-width cell seen 1/1056 at `(1, 2, 3, 5, 6, 11, 12)`, attained at the largest-product pair `(12, 11)` with `x + y ≡ 7`. Sets with a multiple of 8 can have fewer than four cells; the ten two-cell sets at `N ≤ 22` all contain a multiple of 8, for example `(1, 2, 3, 4, 5, 7, 8)` with cells `[9/56, 7/40]` and its mirror; no account is known of which such sets have only two cells. Cells per period: parity is the only invariant (odd exactly for all-odd sets); for all-odd sets the cell containing 1/2 is `[1/2 − 3/(8 d_max), 1/2 + 3/(8 d_max)]` [reasoned, verified on every all-odd set in the populations; `(1, 3, 5, 7, 9, 11, 13)` has width 3/52]. Smallest gap between consecutive cells 1/(4N) exactly for `N` = 8 to 20 and 14, 18, 22, reasoned lower bound `[PROVISIONAL: covering]`, supports only this observation (a gap contains a whole zone, width at least `1/(4 d_max)`).

### 5.2 Two scales (`TwoScale`)

For integer disparities with no multiple of 8 the instants `a/8` (`a` odd) are all lonely (`Boundaries.four_cells`, `unit_lonely`). The obstruction is a disparity `8c`, a D_max-shifted runner. Split `D = D' ∪ 8C`, `t = (a + η)/8`.

* [L] `lonely_iff_shift`: `D' ∪ 8C` is lonely at `(a + η)/8` iff every `d ∈ D'` has `d·(a + η)` mod 8 in `[1, 7]` and every `c ∈ C` has circle distance of `c·η` at least 1/8. `residue_window`, `r1_clear`, `r1_blocked_small`, `r7_blocked_small`, `r7_clear_from_two`, `residue_slack`: a residue-7 runner is blocked for `d·η ∈ (0, 2)` and clear from 2; a residue-1 runner is clear on `[0, 6]` and blocked just below 0 (critical on one side); residues 2 to 6 have slack. `tower_two`: the same decomposition at the second level of the 8-adic tower.
* **The reduction makes nothing easier** [L]: `Compat D' C` (an integer `a` and a real `η` with `a + η > 0`, every `d ∈ D'` in its residue window, `C` lonely at `η`) holds iff `D' ∪ 8C` has a lonely instant (`compat_iff_exists_lonely`). `CompatAll` (the integer eight-runner statement: for `D'` of non-multiples of 8 and `C` of positive integers with `|D'| + |C| = 7`, `Compat D' C`) is `-- STANDING: OWED`, `[PROVISIONAL: covering]`, supports the conjecture itself; named, not asserted.
* [L, PARTIAL] An existence result in one regime, conditional on a hypothesis: `explicit_instant` (and `explicit_instant_plus`, `explicit_instant_minus`): if `D'` misses an odd residue class `m` mod 8 and `η` is lonely for `C` with `d·η ≤ 1` for every `d ∈ D'`, then both `(m − η)/8` and `(8 − m + η)/8` are lonely. The condition `d·η ≤ 1` has the bound shape of rule 7 and is `[PROVISIONAL: covering]`; it supports only the existence of a lonely instant in this regime and is not offered as the argument for the conjecture.
* [OBS, exact, gcd-1 7-subsets of `{1..N}` containing a multiple of 8: 1,715 / 20,349 / 92,730 sets at `N` = 14 / 18 / 22]. The explicit instant applies to 2,568 of 92,730 sets at `N = 22`; the other 90,162 are displaced. The landing equals the first lonely point `η_C` of `C` alone in 2,997 sets, all with `min(D')·η_C ≥ 1`; in all 89,733 sets with `min(D')·η_C < 1` it is later, the displacement being the exit of a `D'` runner from its blocked interval (a residue-7 runner exits at `d·η = 2`); re-run by the main session for `(1,2,3,4,5,7,8)` (`s = 8t = 9/7`, `η_C = 1/8`), `(2,3,4,5,6,7,8)` (`s = 1/2`) and `(1,3,4,5,6,7,16)` (`s = 25/7`, `η_C = 1/16`). For `|C| = 1` the window method matches the direct landing in 60,684 `(c, D')` pairs, 0 mismatches. The cascade from `η_C` reaches the landing in up to 18 moves.
* [OBS] Fail set: for every set `D'` of six non-multiples of 8 in `{1..N}`, `N` = 14, 18, 22, and every `c ∈ {1..48}`, `D' ∪ {8c}` has a lonely instant: 82,368 + 384,384 + 1,860,480 pairs, 0 without one. Nothing is claimed for `c` above 48.
* [OBS] The central-cell mechanism (a unit `a` whose central cell meets the `C`-lonely set) is real but not the principal one: no unit works for 43,243 of 92,730 sets at `N = 22`; the landing lies in a central cell for 9,519 sets. The 8-adic tower does not determine the landing (depth-2 population of 25,067 sets: odd first-level digit in 9,370; first-level part equals the landing of `C` in 6,533, displaced in 18,534).
* Real disparities [reasoned in E441; made [L] in §5.4].

### 5.3 Landing exceptions (`LandingExceptions`)

Populations as §5.1 and §5.2, full. [L] where marked.

* **Corrections to the boundary data** (E441): the counts "1 / 3 / 5 / 7" are `p` mod 8, not `p` (`p` is often large); `cofactor_class` (`g·p = 8k + 1` gives `8 | (g − p)`, `g = gcd(8k+1, x)`); the counts 181,859 / 8,894 / 1,209 / 21 are counts over openers (per set with ties removed: 160,233 / 8,750 / 1,209 / 21 at `N = 22`); the sharper bound is `8k + 1 ≤ 4x`, that is `t* ≤ 1/2` (`landing_le_half`, `opener_lap_bound`). The earlier "`k < x`" was wrong.
* [L] What blocks an earlier opening: `inWay_opening_iff` (runner `z` is in the way at the opening time `n/(8x)` iff `|z·n − 8jx| < x` for some integer `j`), `step_blocks`, `chain_blocks`, `chain_blocks_opening` (`[PROVISIONAL: covering]`, the move intervals against the interval from the start to the landing; supports the statement that no earlier opening is lonely, which is the definition of the landing, and no existence claim): every instant between the start and the landing is blocked by the setter of the move whose interval contains it. [OBS] 27,484 + 282,339 + 1,553,083 earlier openings each blocked by the named runner, 0 violations; the blocker is slower than the opener in 1,459,192 and faster in 93,891 cases (`N = 22`). The landing opener is the final setter, or `d_min` at lap 0 if there is no move (170,213 of 170,213).
* [L] `clear_lap0_iff`, `landing_lap0_iff`, `landing_gt_of_forbidden`, `lap0_opener_is_min`: `1/(8·d_min)` is the landing iff `|d − 8j·d_min| ≥ d_min` for all `d` and integers `j`; a disparity in a forbidden zone of `d_min` makes every clear instant strictly later. [OBS, set equality in all populations] the sets with landing lap above 0 are exactly the sets with a disparity in a forbidden zone of `d_min` (792 of 3,431; 13,642 of 31,788; 61,958 of 170,213).
* [L] Sweep-down (`neighbour_in_way`, `landing_no_predecessor`): if `y` opens at lap `j` at time `t` and `0 < e·t < 1/4` then `y − e` is in the way; with `e = d_min`, a landing with `R* < 2` never has `x − d_min` in `D` (58,777 landings, 0 violations).
* [L] Ties (`openers_at_instant`): at `t = p/(8c)` (`p` odd, `gcd(p, c) = 1`) a runner `d` stands at exactly 1/8 past a lap iff `d = m·c` with `m ≡ p` (mod 8) [OBS 205,432 sets, 0 mismatches].
* The rare classes (`p` mod 8 = 7, 5, 3): finite lists (the bound `8k+1 ≤ 4x` leaves 2, 4, 14 admissible `(x, k)` pairs for `g` = 7, 5, 3 at `N = 22`, of which 2, 3, 7 are realised). **Rarity is a population effect:** `p` mod 8 = 7 sets number 21 / 25 / 356 at `N` = 22 / 26 / 30, `p` mod 8 = 5 sets 1,209 / 2,132 / 8,015. The 21 sets at `N = 22` are two instants, `t* = 7/24` and `t* = 7/16` (one set `(1,3,4,5,6,8,14)`, re-run: landing 7/16).
* **A claim refuted, with the reason:** "the first setter is the smallest forbidden disparity" holds in 61,958 of 61,958 sets at `N = 22` and fails in general: `D = (2, 3, 4, 5, 6, 17, 31)` has 31 as the first setter (opening `R = 34/31` above 18/17) and lands at 17/248 (re-run).
* **Residue rule refuted as stated** (the theory that the residue of `d` mod 8 determines the landing class). Same residue pattern `(1, 2, 3, 4, 5, 6, 0)`: `(1, 2, 3, 4, 5, 6, 8)` lands at 9/64 with first setter 8 on lap 1; `(1, 2, 3, 4, 5, 6, 16)` lands at 17/128 with first setter 16 on lap 2 (re-run). The first setter's lap is the quotient `d/8`, which a residue cannot see. For `d_min = 1` the lap-0 landing holds iff no `d ≡ 0` mod 8 (54,264 of 54,264 at `N = 22`); for `d_min > 1` the right quantity is the residue of the ratio, `d` mod `8·d_min` in `[d_min, 7·d_min]`.

### 5.4 The real case (`RealCase`)

No integrality or commensurability hypothesis anywhere. All [L]. In the gate coordinate `R = 8·d_min·t` with `ρ = d/d_min`, write `ρR0 = 8z + δ` with `δ` the signed residue (Lean's rounding puts the range at `[−4, 4)`).

* `clear_shift_iff`: runner `ρ` is clear at `R0 + ε` iff `(δ + ρε)` mod 8 lies in `[1, 7]`. `blocked_iff`, `clear_iff`, `slack_iff`: blocked at `ε = 0` iff `|δ| < 1`, clear iff `|δ| ≥ 1`, clear with slack iff `|δ| > 1`. `lonelyAt_gate_iff`, `inWay_gate_iff` for a finite set. `nextOpening_gate`: for `d` in the way, `8m·nextOpening = R0 + (1 − δ)/ρ`. `isMove_gate`, `isMove_of_gate`: the move from `R0` goes to `R0 + max` over blocked `e` of `(1 − δ_e)/ρ_e`, and is the identity when nothing is blocked.
* **`dev_scale`: `δ` is unchanged under `d → c·d`, `m → c·m`. This is the exact sense in which the cascade does not see rational versus integer.** The cascade's definitions (`InWay`, `nextOpening`, `IsMove`) are written for positive reals and never ask whether two speeds are commensurable; the split enters the work only through exact-data tools (Fractions enumerate rational sets) and periodicity (`Cycle`, `Boundaries`, `commensurable_mirror`). Rational populations are test cases for the oracle, not a reduction, and no existence statement may rest on a grand return or a half period.
* `eps_strictAnti`: for fixed `δ < 1` the offset `(1 − δ)/ρ` strictly decreases in `ρ`, so the residue alone does not determine the move (the symbolic reason, true for all reals, behind `(1,…,6,8)` versus `(1,…,6,16)`). `TwoScale` is the case `δ = 0`: for integer `d` and odd integer `R0 = a`, `d` is blocked iff 8 divides `d` (`blocked_integer_iff`), and a `δ = 0` runner reads `distInt(ρε/8)`, for `ρ = 8c` the sub-instance `distInt(c·ε)` (`delta_zero_shift`). **So the two-scale reading adds no mechanism beyond the cascade's move.**
* **The non-generic locus.** `touch_ratio`, `touch_of_ratio`: an opener of `x` and an entry of `y` at a common instant `t > 0` exist iff `x(8k'+7) = y(8k+1)` for naturals `k, k'` (`RatioForm`); `tie_ratio` for two openers. `Generic ds` means no pair of `ds` has `RatioForm` (`irrational_not_ratioForm`, `generic_of_irrational`). `generic_cell_pos_width`: every cell of a generic set has positive width. `isoSet_open_at_generic`: if the disparity set at `s0` is generic and an isolation holds at `s0`, the isolation set contains a neighbourhood of `s0` in `[0, 1]`. A claim in the brief, "every lonely instant is a point of positive margin", is false even for generic sets: `cell_end_zero_margin` shows the left end of every cell has a runner at exactly 1/8; the true statement is that every generic cell has positive width and contains positive-margin points (`generic_margin_point`). Along an affine path: `moebius_value_subsingleton`, `pair_equation_subsingleton`, `pair_ratio_dichotomy`, `nongeneric_params_countable` (with every pair non-proportional, the non-generic parameters are countable; `[PROVISIONAL: counting tool]`, countability of a set of parameters, supports the use of `isoSet_open_at_generic` along a path and no existence claim). This is not closedness: openness holds at a point where isolation already holds, and the escape branch of `isoSet_dichotomy` is untouched [reasoned].

### 5.5 Cells as transversals (`CarvingLineage`)

[L]. `cell_in_window`, `isCell_iff_transversal`: a cell of `ds` is the intersection of exactly one window of each runner, `[max of the openings, min of the entries]`, nonempty iff every opening is at most every entry (`ends_le_iff_pairwise`); `ancestor_isCell` for sub-families; `cell_insert_unilateral` (an inserted runner no faster than every earlier one clips a parent cell at one end only); `Icc_transversal_subset_lonely`; `not_lonely_iff_in_some_zone` (`[PROVISIONAL: covering]`, a zone-membership statement, a definitional unfolding, supports the transversal form below).

`exists_lonely_iff_transversal` and `zones_cover_iff_all_transversals_blocked`, both `[PROVISIONAL: covering]` (support "the isolation exists iff the zones of the runners do not cover `(0, ∞)`"): these are equivalences, asserting neither side, and each is the conjecture. **Stated exactly in §8.**

[OBS] No stage-wise end-position invariant survived the full populations (`carving_lineage_v1.py`, both insertion orders). "The landing ancestor at stage `s` is the first cell not killed by any single remaining runner" is refuted: `(1,2,3,4,6,7,8)`, slowest first, the cell `[1/8, 7/48]` is clipped to the touch `[1/8, 1/8]` by 7 and the point is then killed by 8; no single runner kills the original cell. "Every window of `d_min` contains an isolation" is refuted: smallest example `(3,4,5,7,8,9,13)`, window `[3/8, 5/8]`, no lonely point in the window (checked on a 4,001-point grid, which is a check and not a proof; the exact reason is the joint killing of the window by all six other runners, found by AJ's lineage computation `experiments/n8/carving_lineage_v1.py`, exact transversal test of the window).

### 5.6 The comparison across n (`AcrossN`)

Recorded as data only. The owner's question (2026-10-09), "Wait, why are we trying to prove generality. Have we proved n=8 first?", is answered in the status block: no. Nothing is built on this section and no further work at other n is started unless the owner directs it. [L], integer disparities, gap `1/n`: `lonely_iff_not_dvd` (`a/n` is clear for `d` iff `n` does not divide `d·a`), `unit_lonely_general`, `multiple_blocks`; `units_separated` with `lapline_between`, `lapline_between_ap` (for `n − 1` distinct positive integers with no multiple of `n` there are at least φ(n) cells; the general form of `four_cells`; one counting step, `[PROVISIONAL: counting tool]`); `touch_sum_dvd`, `touch_cofactors`, `width_congruence_general`; `gate_blocks`, `no_lonely_in_gate` (no lonely instant with `R ∈ (n−1, n+1)`; `[PROVISIONAL: covering]`, one runner's zone against a window, supports the general-n gate statement and no existence claim); `conj_integer`, `conj_integer_opener`. **What is specific to `n` dividing 24** (here `n` = 6 and 8): the opener cofactor satisfies `c·p ≡ 1` (mod n), so `c ≡ p` only when `p² ≡ 1` (mod n) (`cofactor_eq_iff_selfinverse`, `sq_one_of_dvd_24`; `not_selfinverse_examples`: fails at n = 5, 7, 9, 10). The reading "cofactor ≡ p, entry cofactor ≡ −p" in §5.1 is therefore the self-inverse case. [OBS] populations: n = 5 N = 40 (85,771 sets); n = 6 N = 30 (139,246); n = 7 N = 24 (133,644); n = 8 N = 22 (170,213); n = 9 N = 18 (43,749); n = 10 N = 16 (11,440). The integer cascade equals the first lonely point of an independent exact cell computation in every set at every n, 0 mismatches. Touch-only sets: n = 5 `(1,2,3,4)`, `(1,3,4,7)`; n = 6 `(1,2,3,4,5)`, `(1,3,4,5,9)`; n = 7, 9, 10 the AP only within the stated limits; in every one the cells are exactly the φ(n) unit instants; no derivation of why relatives exist at n = 5, 6, 8 and not in the searched ranges at 7, 9, 10. Crossers found only by wider searches at n = 6 (8 sets, smallest `d_min` 9, maximum `R*` 301/36, search to 80) and n = 7 (9 sets, smallest `d_min` 7, maximum 150/17, search to 58); none at n = 5 (to 250), n = 9 (to 40), n = 10 (to 36), conditional on method and range. The first move equals `R0 + max (1 − δ_e)/ρ_e` at every n (0 mismatches). No fact found uses n = 8 beyond the self-inverse case; none bears on existence for any n.

---

## 6. Restatements, refuted theories and corrections

### 6.1 Table

One line per item. "Reason" names the hypothesis or object that was wrong.

| Entry | Found | Reason the theory was wrong / the correction |
|---|---|---|
| E429 | `IsGridWithDeviation` is vacuous (every arrangement satisfies it) | the grid and its coordinates carry the content, not the existence of some `(d, idx, e)`; replaced by the coordinate conversion in `Where` |
| E429 | (a), (b), (c) forms of "the displacement is forced" are each `iff` the conjecture | none states where the isolation goes beyond the first move |
| E429 | `GridGlobalIsolation` as stated is a sufficient-instants statement, not the φ(8) law | `grid_extra_instant`: a non-primitive step has more instants |
| E428 | stage-1b register: DoorFirstLap, DoorLargestFlank marked refuted in their source with counterexamples | cap shape (cascade iterates at most `1/d_min`; lonely opening at the largest flank); counterexamples are in the older record and are not re-derived here |
| E428, E436 | register rows Cover8, WideStep8, WindowBound, RCapped | caps; the owner's words never ask for a threshold, cap or cover parameter; classed imported (cap) |
| E436 | ArrBlockRule8 and ArrBoundedCovered8 (older repository, plain text) | imported, tested: no threshold fixes the landing; `f` and `T` are not parameters of the cascade at the first landing (§4.5, §7). Owner, 2026-10-08: "I would say the evidence decided." |
| E430 | the pasted line "b/(b/c+b/d+b/e) ≥ 1/3 ⇔ b/c+b/d+b/e ≤ 3" | false both ways (`owner_iff_fails`); the left side does not involve `b` |
| E429, E430 | protection over a chain | holds only for a reading that starts at the lower edge (`offset_recapture_example`); as a bound over a chain it has the move-budget shape |
| E431 | AP neighbourhood radius 1/32 | not sharp; 1/16 holds (`ap_isolated_of_le`); the pair `(1, 7)` forces it (`cx_not_isolated`) |
| E432 | the v9 interval claim at `c/20` for class 7 | the closer is whichever runner enters first, not the mirror runner; sharp radius 1/22 (§4.1) |
| E433 | pair law for grids with the radius `|d_j − o_j·d| ≤ ρ·d` | drift is proportional to the offset; the hypothesis must be on rescaled positions (§4.3) |
| E434 | L2 "the added runner never kills the first cell" | true only when the added runner is at least all others (`L2_fails_without_order`) |
| E434 | E342 "integer readings, none above 7" and E357 (`s ≤ 3`) | do not extend; integer crossers exist from `d_min = 6` |
| E434 | E340's hand proof of the nine-landing | does not cover a blocker entering after the last state at or below 7 |
| E434 | the cascade types are a finite set | full types, rank words and the coarse class each equivalent to a move cap or an `R*` cap (rule 7 shape) or to a population (§7) |
| E435 | "the cycle is the slowest speed's full rotation" is the period of the pattern | only when the slowest speed divides every speed; AP `3..10` (`ap3_counter`) |
| E435, E436 | `StrongGate` via `FiveReach`; the reach thread | the covering method stops at three readings; `Reach 6 6` is false; paused (§6.2) |
| E437 | the "handover" picture (an isolation passes to a newly born cell) | in all but 57 of 35,740 deaths another cell was already present; `SuccessorIsolation` is not a local transport law (§7) |
| E437 | the mirror class `8 − a` as a universal law | the pair law at the AP only; away from the AP the survivor is another class in most data (A1: 872 of 1,115) |
| E438 | a strictly clear instant at every parameter | false at the AP (`strictForm_refuted`); the AP's isolations are touches |
| E436 | "past-the-cell forces zero width" (block landing) | false (`{2,12,15}`) |
| E439, E440 | a whole-set conjugate of a touch needs commensurable disparities | a sufficient hypothesis of `commensurable_mirror` taken for a necessary one; `wholeset_conjugate` needs only positivity |
| E440 | the integer mirror symmetry read as an integer-set feature | the role swap exists for every positive family (`wholeset_conjugate`); the half-period statements (`half_lonely_iff_odd`, `finset_half_lonely_iff`, `int_lonely_half`) need integer disparities, a period; the conjugate does not |
| E440 | "the half-period `t = 1/2`" as a general mechanism | integer specific (§5.1) |
| E440 | "the landing ancestor is the first cell not killed by any single remaining runner"; "every window of `d_min` contains an isolation" | refuted by `(1,2,3,4,6,7,8)` and `(3,4,5,7,8,9,13)`; survival is a property of the whole transversal (§5.5) |
| E440 | AJ's "the landing lies in the first window of `d_min`" (all 170,213 sets, `N ≤ 22`) | false in general: the integer crosser `(6,16,21,26,29,36,45)` lands at `R = 294/29`, outside the first window; a population-size pattern |
| E441 | "1 / 3 / 5 / 7" landing numerators; "`k < x`" | were `p` mod 8 and `8k + 1 ≤ 4x` |
| E441 | "the first setter is the smallest forbidden disparity" | `D = (2,3,4,5,6,17,31)`: first setter 31 |
| E441 | the residue rule | `(1,…,6,8)` and `(1,…,6,16)` have the same residues and different landings; the lap is the quotient `d/8` |
| E440, E441 | "each eighth-class at most once among the runners on an eighth at the landing" | refuted in 34,327 of 170,213 at `N = 22`; two non-subject runners may stand at the same point |
| E441 | the two-scale reduction as progress | `compat_iff_exists_lonely`: an `iff` with existence; nothing is made easier |
| E442 | "every lonely instant is a point of positive margin" (brief) | `cell_end_zero_margin`; generic cells have positive width and contain positive-margin points |
| E442 | integer-specific mechanisms | do not transfer to reals: "R = a works iff 8 does not divide d", "D' misses an odd residue class", the gcd-1 normalisation behind `8k + 1 ≤ 4x` |
| E443 | the comparison across n as the next step | the owner: n = 8 first; the results are data only |
| E440 | run-time and count corrections (E439): AI's run time given as about 13 minutes | the final notice reads about 25 minutes; the data are unaffected; AH's report said "no warnings" and `ZeroMargin.lean` has three unused-variable warnings |
| E433, E438, E443 | agent run times | first notices are partial; final notices are used. E433: `GridPairLaw.lean` was first cut off by a usage limit and was complete when read |

### 6.2 The paused gate thread (`Types`, `SmallDmin`, `StrongGateStudy`, `FiveReach`)

The thread inherited from the record's gate lemmas bounds where a landing sits (R at most 9, R below 12), a cap shape the owner's words do not ask for. Stocktake of E437, for the owner to confirm or strike: the thread is paused; its results stand as recorded.

* `StrongGate` (setter into the gate on lap 1 with ratio below 17/15, next opening past `R = 9`) is `-- STANDING: OWED` in `Types`. [L] `strong_gate_of_gap` (if every `d ≠ m` has `15d ≥ 17m`, the move out of the gate lands at exactly `R = 9`; the older FirstGateN needed `d ≥ 2m`); `late_blocker_forces_slow_lap_one`; `no_crossing_of_small_dmin` (`d_min ∈ {1, 2}` integer: no crossing); `firstMove_lap` and `firstMove_lap_injective` (`{1,…,6,8j}` has first letter (rank 7, lap `j`), so the lap label carries scale and the set of full types is infinite).
* `StrongGateStudy` [L]: `idle_before_entry`; `violation_carves` (`[PROVISIONAL: covering]`, supports `FiveCarve`); `late_blocker_fast`; `fiveCarve_of_fiveReach`, `strongGate_of_fiveCarve` (`[PROVISIONAL: counting tool]` in `card_disparitySet_le`); `lonely_at_inv_of_no_multiple`, `crosser_needs_multiple`, `crosser_dmin_seven` to `crosser_dmin_three`. `FiveReach` (any set of at most five disparities, all at least `m`, has a lonely instant in `R ∈ [1, 6]`) and `FiveCarve` are `-- STANDING: OWED`, `[PROVISIONAL: covering]`, supports `StrongGate`.
* `FiveReach` module [L]: `Reach k B`; `fiveReach_iff : FiveReach ↔ Reach 5 6` (`Iff.rfl`); `reach_one` (9/7), `reach_two` (81/49), `reach_three` (729/343, a union bound), each `[PROVISIONAL: covering]` (zone ratios against window length; support `StrongGate` through `Reach`) with matching lower-bound witnesses; `not_reach_six_six` (the six-reading analogue is false: witness with first lonely `R = 4900000/562313` after 20 moves, re-run); `union_bound_range` ((9/7)³ < 15/7 < (9/7)⁴), `capacity_jump` (both `[PROVISIONAL: covering]`, same supported claim) (why the covering method stops). `ReachFourSharp` (289/105) and `ReachFiveSharp` (2125/483) are OWED. **Why the covering method stopped:** it bounds how much of a window one reading can shadow; past three readings a fourth reading returns on lap 2 (`lap_one_return_gap`) and the capacity bound fails past 15/7. A proof of the five-reading case must use that there are five.
* `SmallDmin` [L]: `crosser_iff_pattern`, `crosser_iff_linear_pattern` (crossers are exactly the union of the open polyhedral cells given by setter-lap patterns, no division), `crosser_iff_all_laps_fail`, `patternLinear_iff_intPattern`, `crosser_scale`, necessary conditions `crosser_first_zone`, `crosser_last_zone`, `crosser_index_ge_eight`, `crosser_first_two_setters`, `crosser_two_large`; certificates `ex_crosser` (`{6,16,21,26,29,36,45}`, landing `R = 294/29`), `lonely_m3`, `lonely_m4`, `lonely_m5` (`R` = 17/3, 68/11, 125/19). `NoSmallIntegerCrosser` (integer, 7 disparities, `d_min ∈ {3, 4, 5}`) and `ReadingsAboveFifteenSevenths` are `-- STANDING: OWED`. The absence at `d_min` = 3, 4, 5 is a lattice-free property of each of 337 cells found, each with a named reason, and not a uniform obstruction [OBS]; the cell list is not proved complete.

---

## 7. Exact data

Every datum is [OBS]: exact integers or Fractions, the population stated, never an argument. "Shows" and "does not show" are given; a pattern that depends on the population size is marked **[ARTEFACT: population size]** (E442). Scripts are under `experiments/n8/`.

**7.1 Types, crossers (E434).** All 7-subsets of `{1..N}`, gcd 1, `N` up to 56 (230,701,234 sets). Independent Fractions cascade agrees with the integer enumerator on type, `R*` and zero-width flag for all 170,213 sets with `N ≤ 22` (0 differences). Full types: 74 at `N = 12`, 604,660 at `N = 56`. Rank words: 48 at `N = 12`, 63,243 at `N = 56`, maximum 24 moves for `N` = 32 to 56. Coarse class (opener rank, closer rank, landing above 7), no ties: 37 for `N` = 19 to 44, then 39 at 48 and 41 at 56 **[ARTEFACT: population size]**. Integer gate crossers: none for `N ≤ 44`, 5 for `N ≤ 56`, 47 for `a7 ≤ 70`, each with exactly one letter `(1,1)`; none with `a1 ≤ 5`, exhaustively to `a7 ≤ 100` (3,836,946,849 sets for `a1` = 2 to 5). Maximum landing seen 657/64 at `(9,23,30,37,41,51,64)`, below 12. Shows: the full type, the rank word and the coarse class as counted are not a finite set. Does not show: why `a1` = 3, 4, 5 have no crosser.

**7.2 `StrongGate` (E435).** The 47 crossers all satisfy `17m ≤ 15d` for every `d ≠ m`, so `strong_gate_of_gap` excludes a violator in each. Setter into the gate (rank, lap) counts: (3,3) 22, (5,4) 9, (2,2) 6, (6,5) 5, (4,4) 3, (7,7) 2; never lap 1; smallest ratio of a setter to `d_min` 7/3. Integer 7-sets with `a1` = 3, 4, 5, `a7 ≤ 100`: first lonely `R*` at most 51/9, 68/11, 125/19. Best chain of five readings reaches 2125/483 (an LP maximum not attained; the cascade object is the set of five readings: the witness sets of `not_reach_four` and `not_reach_five` have exact landings 8500/3089 and 6250/1421, re-run by the main session with the exact cascade); exact enumeration of all 6-sets gives maximum 275/64 for `A` = 1 to 14, `a ≤ 100`. One exactly verified real-valued crosser: `1, 66983/31250, 2927303/10^6, 3843261/10^6, 975767/200000, 2740801/500000, 7000043/10^6`, `R* = 65/7`. Hill-climb thresholds and sampling figures are steering and carry no weight.

**7.3 Z1 cells (E436).** 337 cells with exact rational vertices; none has a lattice point at `d_min` = 1 to 5; smallest `d_min` with a lattice point per cell: 6 (8 cells), 7 (41), 8 (40), 9 (21); exact infimum of the second reading over the cells 15/7; the cell list was extended twice using crossers found by a random-sampling search outside the list (9, then 2); that sampling departs from rule 14 (nothing is random) and the list is not claimed complete.

**7.4 Block rule (E436).** §4.5. Does not show: that `f` or `T` plays any role; the data checked only the first landing.

**7.5 Touch transport (E437, `touch_transport_v2.py`).** Straight paths of speeds that keep the speed order, event parameters solved exactly. Paths generated by AD's script from stated families (A1 64, A2 60, A3 60, grid-to-random B 60, P 40, Q 40, CX 1 paths; 2,600 subject-paths over 325 paths); this is a non-exhaustive path set, not a population, and the random-start families depart from rule 14, all eight ranks, window `T = 1`. Every death and birth of a cell at an interior parameter is a touch, in all 35,740 deaths and 33,702 births; no merge and no split (0 each). In 35,683 of 35,740 deaths a cell persists on both sides, in no death did the survivor depend on a cell born at the same parameter (0). The 57 deaths with no cell left in `(0, 1]`: the next cell lies beyond the window and was present all along (for example `t = 9/8` at `s0 = 20/21`). All 68 phases without a cell in the window are window artefacts. No path has an empty lonely set (finite population, not a proof). Population B's `T = 3` figures are inherited and unverified and carry no weight. Shows: the successor is not a transport law. Does not show: why 27 paired opener-and-closer swaps occur at AP-symmetric parameters such as 7/12 and 5/7.

**7.6 Touch-only sets and cones (E438, E439).** Integer 7-subsets: sizes 1 to 6 with entries at most 16, none; size 7 with entries at most 28 (all 1,184,040 7-subsets of {1..28}), exactly three: `(1,2,3,4,5,6,7)`, `(1,2,3,4,5,7,12)`, `(1,4,5,6,7,11,13)`, each lonely at 1/8, 3/8, 5/8, 7/8 per period. All 18,643,560 integer 7-subsets of `[1, 40]`: 11 survive, all scalings of those three; rational sets `a/Q`, `Q` = 2, 3, 4, 5 (all 7-subsets of {a/Q in [1,12]}: 245,157 + 5,379,616 + 45,379,620 + 231,917,400 = 282,921,793 sets): rational multiples of the same three. Cone cover (all 5,040 orders tested): the touches at 1/8 and 7/8 each have one opener and one entry, and cover every direction (`[PROVISIONAL: covering]`). Generic sets: all 7-subsets of `[1,14]` and `[1,18]` (3,432 and 31,824): 4 have no positive-width cell. Exception `(1,2,3,4,5,6,11)`: under `δ = (1,4,9,16,25,36,77)` at `e = 1/1000` both touches vanish and the isolation moves into positive-width cells already there, least lonely time 125/1001. Model check at `e = 1/10^6` (an exact rational): 112/112, 124/124, 128/128. Does not show: that any incommensurable touch-only set has no escape (rank 2 and higher families not searched).

**7.7 Boundaries, two scales, landing exceptions (E440, E441).** §5.1 to §5.3. Population-size artefacts: the 1/3/5/7 numerator counts; "ten two-cell sets all contain a multiple of 8"; rarity of `p` mod 8 = 7, 5, 3; "rank 1 at lap above 0 never occurs" (maximum seen 33/7 against the 9 needed).

**7.8 The real case (E442, `real_case_v1.py`).** Embedded C int64 kernel, no floats, validated against the Fraction cascade with 0 mismatches on 3,431 + 1,107,106 + 657,800 sets, every 211th set of a `Q = 7` population, and the AN anchors at `N = 22`. Full enumerations of 7-subsets of `{a/Q}` in `[1, 12]`: `Q = 3` 5,378,824 sets; `Q = 5` 231,916,608; `Q = 7` 2,641,901,328 (no pattern table). A `Q = 3` slice (`d_min ∈ {1, 4/3}`, elements to 16; the exact count is in `real_case_v1.out`) is a stated slice, not a population. Ties or touches (commensurability artefacts): 37614/170213 (integer, `N = 22`), 399927/5378824 (`Q = 3`), 7533888/231916608 (`Q = 5`), 66544926/2641901328 (`Q = 7`). Landing in the first window `[1, 7]`: all sets at `N = 22` and `Q = 3`; at `Q = 5` all but 14 (`R*` above 7, maximum 511/50); at `Q = 7` all but 183 (maximum 65/6); no landing in `(7, 9)`; the sets with `R* > 7` need `d_max/d_min` at least 50/7 (`Q = 5`) or 78/11 (`Q = 7`); re-run: `(7,17,22,29,36,40,51)/5` has `R* = 9`, `d_max/d_min = 51/7`. Landing at `R* = 1`: 108255/170213 (`N = 22`), 3776650/5378824 (`Q = 3`), 166764591/231916608 (`Q = 5`), 1941245798/2641901328 (`Q = 7`). Explicit instants: 126850/170213, 4653825/5378824, 205076113/231916608, 2304023325/2641901328.
**[ARTEFACT: population size]** (not integrality): "`R*` at most 33/7"; "all landings in `[1, 7]`" (true for `N ≤ 22` only); "rank 1 at lap above 0 never occurs" (the same statement as `R* < 9`); "first setter = smallest forbidden disparity" and "no residue-rule conflict" (these need a ratio range of about 15 or more; AN's first exception: 0 in every full population, 395,752 of 10,551,255 forbidden-start sets in the `Q = 3` slice, minimum `d_max/d_min` 46/3; AN's residue exception: 0 in the full populations, 35,694 patterns in the slice; re-run: `{1, 4/3, 5/3, 2, 7/3, 8/3, 22/3}` versus `{…, 46/3}` have the same residues, `R*` = 27/22 versus 51/46, landing laps 1 versus 2). The crossers of E434 are the real structure those populations were too small to show.

**7.9 Across n (E443).** §5.6.

**7.10 What the exact data collectively do not show.** None of the patterns above is a statement about all arrangements; each is a count over a stated population. They steer which statement to attempt; none is cited as a reason for a claim in §§2 to 5.

---

## 8. What is owed, and where the existence content sits

**The transversal condition, exactly stated.** For a finite set `ds` of positive disparities, with `winLo e N = (N + 1/8)/e` (the opening of lap `N`) and `winHi e N = (N + 7/8)/e` (its entry), `CarvingLineage.exists_lonely_iff_transversal` states [L, `[PROVISIONAL: covering]`]:

```
(∃ t, 0 < t ∧ t ∈ lonelySet ds)  ↔
  ∃ N : ℝ → ℤ,  0 < sup' over e ∈ ds of winLo e (N e)
              ∧  ∀ e ∈ ds, ∀ e' ∈ ds, winLo e (N e) ≤ winHi e' (N e')
```

That is: a choice of one lap per runner whose largest opening is positive and is at most the smallest entry. The conjecture is that for every arrangement and subject such a choice exists for `disparitySet v k`. No stage-wise invariant of building the arrangement guarantees it (§5.5); the existence content is in the whole set. No mechanism guaranteeing a transversal was found (owner, 2026-10-09: "Not found: a mechanism that guarantees such a transversal exists ... Ok lets look for that"; E441 searched and reports none).

**The two scales** (§5.2). Existence is equivalent to `Compat`: a coarse unit `a` and a fine position `η` in a smaller instance (`compat_iff_exists_lonely`). The coarse scale gives explicit lonely instants only when `D'` misses an odd residue class and the fine scale is small (`explicit_instant`; 2,568 of 92,730 sets at `N = 22`); otherwise the landing is the cascade from `η_C` displaced by exits of `D'` runners from blocked residue intervals. In the real case the same statement is the cascade's move (`isMove_gate`), so passing to reals or to residues reduces nothing. Observation [reasoned, `[PROVISIONAL: covering]`, supports no claim, not offered as an argument]: the blocked fraction per runner is a quarter of the time line in every coordinate, so seven runners block seven quarters in total at every scale tried (`[PROVISIONAL: covering]`, supply against demand of blocked fractions; supports only the reading, in §5.5 and §8, that no stage-wise guarantee appears, and is not offered as an argument).

**Why every route reduced to it.**

| Route | Native result | Reduction |
|---|---|---|
| Three forms of "forced displacement" (E429) | `displacementPath_iff`, `cascadeForm_iff`, `candidateScaleForm_iff` | each `iff` the conjecture |
| Doors (E431) | `doors_agree`, `global_door_iff` | each door `iff` the conjecture |
| Path laws (E437, E438) | loss dichotomy, `lre_iff_leftClosed_right`, `owed_pair_imp_lre` | the owed pair is `PathLonelyBound` and `SuccessorIsolation`; together they give the conjecture along grid-start paths |
| Zero-margin (E439, E440) | `σ`-law, `wholeset_conjugate`, `touch_conjugate_cover` | governs the AP, its relatives and the pair law; stops at generic sets (positive-width cells, no touch to deform) and at touches with two critical runners on one side |
| Covering (E440) | `exists_lonely_iff_transversal`, `zones_cover_iff_all_transversals_blocked` | the conjecture, stated exactly |
| Two scales (E441) | `compat_iff_exists_lonely` | `iff` existence |
| Real case (E442) | `isMove_gate`, `dev_scale` | the cascade's move; no new mechanism |
| Gate and reach (E434 to E436) | gate lemmas, `Reach k B` | bound where the landing sits; the covering method stops at three readings; paused |

**Owed, by name.**

* Existence: the transversal condition for every arrangement and subject; `CompatAll` (OWED in `TwoScale`); `PathLonelyBound`, `SuccessorIsolation` (OWED in `PathLaws`); `ConjectureGivesBound` (OWED in `PathClassify`). Why a chain ends is the conjecture and is untouched.
* Touch theory: positive dependence for general arrangements; the second-order case in general ([L, PARTIAL]: the AP pair is covered by `affine_survival_classification` and `ap_pair_survives_every_direction`; other arrangements are not); a whole-set no-partner example with both an opener and an entry (none found, none proved impossible); the escape alternative at an arrangement; whether a touch-only arrangement can host an escape (rank 2 and higher not searched).
* Landing: the exact condition for covers by three or more zones; the multi-runner narrow-cell criterion; the landing as the cascade from `η_C` in Lean; a proof that rank 1 forces lap 0 (`R* < 9`); `CompatAll` and the fail set for `c` above 48; the cell-count structure (`2·pairs + [all odd]`) in Lean; an account of the two-cell sets.
* Gate thread (paused): `StrongGate` (L1(d)), `FiveReach`, `FiveCarve`, `ReachFourSharp`, `ReachFiveSharp`, `NoSmallIntegerCrosser`, `ReadingsAboveFifteenSevenths`.
* Grid layer: minimality of the isolation period; `d'/d` with 2-adic valuation above 1; subjects with runners on both sides in `GridPairLaw`; a bridge from `certificate_iff` to a general arrangement's disparity set; `Framework.lean`'s `GridGlobalIsolation` and the `Where.lean` Props still carry OWED tags although proved in `Grid` and `WhereProofs`.
* Register (E428): stage-1b rows other than ArrBlockRule8 and ArrBoundedCovered8 await the owner's confirmation or strike.
* Wording: v9 Part I-1 row 1 (reworded in v10).

---

## 9. Inventory

Counts recomputed by `grep` on 2026-10-09; Lean was not run. "Theorem and lemma declarations" counts lines beginning `theorem` or `lemma` as whole words (`grep '^theorem\|^lemma'` returns 1,010 because a docstring line in `APNeighbourhood.lean` begins with the word "lemmas"; the table total is 1,009).

| Module | Purpose | Log entry | Lines | Theorem and lemma declarations | `#print axioms` lines |
|---|---|---|---|---|---|
| Framework | Definitions, the owed claims, three candidate forms of 'forced displacement' | E428 | 165 | 1 | 1 |
| Grid | Grid layer: octagon, deviation, AP law, extra instant | E429 | 457 | 21 | 21 |
| Octagon | Isolation by gaps, octagon, global isolation | E430 | 255 | 14 | 14 |
| DMax | D_max shift displaces nothing | E434 | 63 | 4 | 4 |
| Cycle | Grand return, cycle of slowest speed, D_min displacement | E435 | 849 | 48 | 48 |
| GridToGrid | D_min between grids of different step | E436 | 477 | 28 | 27 |
| Localisation | Lower bound, localisation, candidate-scale form, certificate | E429 | 343 | 27 | 27 |
| LonelyCells | Cells of the lonely set, landing = first cell left end | E431 | 675 | 35 | 35 |
| Carving | Carving calculus of the lonely set, L2 counterexample | E434 | 732 | 41 | 41 |
| Gate | Gate lemmas for R = 8 d_min t | E434 | 698 | 29 | 29 |
| Doors | Five doors equivalent to the conjecture; landing is an opening | E431 | 406 | 20 | 20 |
| Where | Ten claims about where the first move and landing sit, stated as Props (OWED tags; proved in WhereProofs) | E429 | 266 | 0 | 0 |
| WhereProofs | Proofs of the ten `Where` claims | E429 | 443 | 28 | 28 |
| Dilation | Setter reading shift, dilation below 9/7, link rule | E429 | 324 | 25 | 25 |
| ChainLaws | Lap laws of cascade chains | E430 | 246 | 12 | 12 |
| Cascade | Cascade facts; cascade form iff conjecture | E429 | 476 | 35 | 35 |
| PathForm | Path form iff conjecture | E429 | 195 | 11 | 11 |
| Protection | Lower-edge protection over several moves | E430 | 375 | 21 | 21 |
| PairLaw | Pair law at the AP, sharp radius 1/22, record interval claim fails | E432 | 749 | 41 | 41 |
| GridPairLaw | Pair law for grids, rescaled hypothesis, exceptions | E433 | 921 | 56 | 43 |
| APNeighbourhood | AP neighbourhood isolation, radius 1/16, counterexample | E431 | 449 | 22 | 22 |
| ZeroMargin | Exact touch survival, interval system, AP survival form, conjugates, Gordan | E439 | 1048 | 58 | 58 |
| TouchTheory | Whole-set conjugate, cone cover, second-order pair law | E440 | 815 | 26 | 26 |
| BlockLanding | Core plus block decomposition and 1/x displacement | E436 | 739 | 44 | 44 |
| BlockLanding2 | Cover form of the block landing, next-cell recursion | E438 | 479 | 23 | 23 |
| PathLaws | Openness, closedness, loss dichotomy, escape example | E437 | 606 | 32 | 30 |
| PathClassify | Owed path statements classified against the conjecture | E438 | 478 | 24 | 24 |
| Boundaries | Units, widths and cell counts at boundaries | E440 | 332 | 16 | 15 |
| TwoScale | Two-scale decomposition, `Compat`, `CompatAll` (OWED) | E441 | 532 | 33 | 26 |
| LandingExceptions | Blocking of earlier openings, lap-0 landing, ties, cofactors | E441 | 495 | 28 | 28 |
| RealCase | Move in gate coordinate for real sets, generic sets | E442 | 664 | 41 | 39 |
| CarvingLineage | Cells as transversals; existence iff transversal | E440 | 330 | 9 | 9 |
| AcrossN | General-n versions of the unit, touch and gate facts | E443 | 515 | 26 | 25 |
| Types | Gate entry and crossing lemmas, `StrongGate` (OWED), types do not settle | E434 | 499 | 15 | 15 |
| SmallDmin | Crossers as a union of cells; `NoSmallIntegerCrosser` (OWED) | E436 | 777 | 28 | 28 |
| StrongGateStudy | What a counterexample to `StrongGate` needs | E435 | 393 | 15 | 15 |
| FiveReach | `Reach k B`; suprema for one to three readings; `Reach 6 6` false | E436 | 1501 | 72 | 66 |
| Total (37 modules) | | | 19,767 | 1,009 | 976 |

**Axioms (latest whole-folder run, E443).** 976 `#print axioms` lines; 967 read `[propext, choice, Quot.sound]` (`choice` is `Classical.choice`); 9 read a subset of it (for example `Grid.completeResidues_id` reads `[propext, Quot.sound]` and `Localisation.certificate_periodic` reads `[propext]`); no `sorryAx`; 37 modules; 19,767 lines; 24 warnings (unused variables and linter), no error. Scan of code for `sorry`, `native_decide`, `axiom`, `admit`, `unsafe`: 0 in every file. Untagged `Prop` definitions: 0; the folder carries 30 `STANDING: OWED` and 48 `STANDING: DEFINITION` tags. 79 `[PROVISIONAL: …]` occurrences in `Fresh/*.lean`.

---

## 10. Not carried from v21 and v22

This manuscript does not carry the content of `MANUSCRIPT_v21.md` (the record) or `MANUSCRIPT_v22.md` and does not supersede them. A compile-diff of v22 against v23_2 (2026-10-09) lists what is absent. Pointers: v22 §18D to §18G. The absences that could mislead a reader of this file alone:

* **Lean hold.** Owner, 2026-10-01 (E222): "Yes we are not looking at lean until the map is complete". Lifted for new files by the owner on 2026-10-05 ("see if you can extend the work to a lean proof"; `RULES_n8_v4.md` rule 16), and the separate folder outside the Lean repo was the owner's decision (E428). This manuscript's Lean work rests on that lift; the hold's end condition was never defined.
* **The first isolation is not an obligation.** Owner (v22 §18F, E200): "I don't like first isolation. Because that is not required by the conjecture"; E215: no "first window". The landing results here (§3, §4.5, §5) say where the cascade lands; they are a mapping, not the target. The conjecture asks for an isolation.
* **Existence is graded two ways in the record.** v21 §6.7 grades Existence `[PROVED — via the Localisation equivalence]` through `doors_agree`; v22 §18G (review finding M1) records that this rests on an equivalence; this manuscript grades the same statement OWED because each door is an `iff` with the conjecture (§3.4). The author has not settled the conflict; this file alters neither v21 nor v22.
* **Bound retractions.** v22 §18E carries the retractions about bounds on the landing (E47: fine shapes reach `R*` above 11, exact value in v22 §18E; E151, E330: "no landing above 7 with `ρ_7 > 9`" is forced by the range, not a law). The `R*` figures here (§7) are populations and artefacts of range; a statement such as "`R*` below 9" in §8 is owed, not known.
* **Rule 7.** v22 §18F (E230) rules that existence by any means is admissible and that Props 6.10 and 6.11 were withdrawn for their covering form. This file follows `RULES_n8_v4.md` rule 7 as relaxed on 2026-10-05 (counting and covering steps tagged `[PROVISIONAL: …]`); the two framings are not reconciled here.
* **The finite cover.** v22 §18F (E270, E332) fixes what the finite set of arrangements may be; §6.1 here records "the cascade types are a finite set" as refuted for the counts tried (each version is a cap or a population). The ruling that fixes the finite set is not carried.
* **The analytic route.** v21 and v22 record that at the AP the clear set on `(0, 2]` is 8 isolated points, measure zero (`experiments/n8/clear_set_measure_v1.out`); §4.4 here covers the same locus through the survival form and `ap_not_strict`, without restating the measure fact.
* **EightResidual and orders 3 to 7.** v21 §17 reduces order eight to one statement about EightResidual sets and records orders 3 to 7 as native; this file states the conjecture directly as `LonelyRunnerEight` and does not use orders 3 to 7.
* **Review findings M3, M4, M6, M7** of v22 §18G (Theorem 11.3's proof step at `R = 3/2` and `R = 9/7`; the omitted band hypothesis for unit_never_blocks; the gate banner at orders 3 to 7; "by any means" against "must bound the witness") are not carried, and no refuted proposition of v22 is used as a premise here.

---

## Appendix A. The owner's rulings and guidance

Quoted verbatim from the log (entry cited) or from `RULES_n8_v4.md`.

* 2026-10-05 (`RULES_n8_v4.md`, rules 7 and 16): "relax rule 7 for the moment and see if you can extend the work to a lean proof"; "see if you can extend the work to a lean proof".
* 2026-10-07, guidance in force for every brief of E429 onward (E429 records it as applied; text from the briefs): "enumeration is ok, but a symbolic proof is better. Sometimes we need to enumerate and then look for the proof that is lying within but we are really looking for an analytical proof. Exceptions, counter examples etc are important to be understood why, not just that they occur. Also the cascade is [your] best friend it is 100% accurate. Also be careful trying to prove the proxy of a thing instead of the thing. If you find your proxy has holes, its because the theory was probably wrong because the object like cascade has never had an exception."
* 2026-10-07 (E430, mid-turn, recorded in paraphrase): the system is deterministic, not probabilistic; the math tells us what a statement of "where" is.
* 2026-10-08 (E436): "Yes you have my permission" (the v10 rewording); on ArrBlockRule8: "How would I know? We need to test it and see if it works?"; on ArrBoundedCovered8: "I don't know we need to find out"; after the tests: "I would say the evidence decided. Im not an oracle, the cascade is. We are trying to figure out why it always gives us the isolation event. It does it without fail. The failure is ours of understanding why it must do it."
* 2026-10-08 (E437): "lets continue on with the real target, native proof of n=8"; "Please also keep an eye on what can been proven symbolically".
* 2026-10-09 (E439): "Go with the zero-margin route to start and if that doesnt work go the other".
* 2026-10-09 (E440): "if that doesnt work go the other" (E439); "The cascade doesn't see a difference. Why do we?"; "If you are going to look for things, look for totients, look for exact factions, look for boundaries".
* 2026-10-09 (E441): "Not found: a mechanism that guarantees such a transversal exists ... Ok lets look for that" (the ellipsis is the log's).
* 2026-10-09 (E442): "Start with one and go on to the next if you need to".
* 2026-10-09 (E443): "Wait, why are we trying to prove generality. Have we proved n=8 first?" and "Ok lets write this up in manuscript and then we can look at a paper".
* Framework statement of the owner (from the task brief for the Lean agents, not a log entry; E428 cites it as M005 and M036): any deviation from the AP or grid "just displaces the isolation because we can show where and why it goes there"; the cascade converts an arrangement into grid plus deviation.
* Ground rules that govern every statement here (`RULES_n8_v4.md`): rule 1 (displacement forced), rule 5 (no runner stationary), rule 6 (banned imports), rule 7 (shapes banned; relaxed with tags), rule 15 (no floating point), rule 18 (do not claim what is not done), rule 21 (no new scaffolding documents; never overwrite a versioned file).

## Appendix B. Provenance

Each module header records the older declaration its argument corresponds to; arguments were read and understood, and no proof was copied that was not understood. Older-repository names are plain text. Modules whose header names no older declaration are marked.

| Module | Corresponds to (older repository, per the header) |
|---|---|
| Framework | the owner's document (pasted 2026-10-07) and `FRAMEWORK_COMPILATION_v9.md` sections 0 to 3; the module header records no older Lean declaration |
| Grid | v9 Theorems 2, 4, 5, 6 |
| Octagon | v9 Theorems 1, 2, 10 |
| Localisation | v9 Theorems 7, 9, 10; the Doors and Arrangement/Flanks files of `LRC/Cascade` |
| Cycle | the owner's cycle and grand-return sentences; GrandReturnN read for provenance (E435) |
| GridToGrid | `Fresh.Cycle.grid_reading_shift` and the older arguments read for the idea |
| LonelyCells | the localisation argument (`Fresh.Localisation.exists_opening_of_lonely`; older Flanks exists_flank_of_lonely); right end written for this file |
| Carving | the record's boundary set method (v9 §1) and gate-lemma form (v9 §7); the module header records no corresponding older declaration, and the main session did not search the older repository for one |
| Gate, Types, SmallDmin, StrongGateStudy | record gate lemmas L1 to L7 (`GATE_LEMMAS_v1`), FirstGateN |
| Doors | DoorsN, `LRC/Spec/Doors`, MomentIterationN (iterate_mem_openings, lonely_of_fixed), v9 Theorems 11, 13 |
| Where, WhereProofs | `LRC/Cascade/Reading`, SeparationN |
| Dilation, ChainLaws | `LRC/Cascade/Iteration`, ZoneLinkN, LapDeadlineN |
| Cascade | header records provenance per theorem; no single older module |
| PathForm | ArrangementShapeN |
| Protection | `LRC/Cascade/FourDifferences`, `LRC/Cascade/SmallOrders`; one-move case PinchTransportN (displacement_lt_three_quarters, old_setter_band, handoff_pair_clear) read, not rechecked (E429) |
| PairLaw | ProgressionPairN (E69) |
| GridPairLaw | GridPairLawN, GridClassN (gridTp), GridPairN (grid_pair) |
| APNeighbourhood | APNeighbourhoodN (56 generated pair lemmas) |
| ZeroMargin, TouchTheory | ProgressionPairN (survival form); the module headers record no older declaration for the touch theory, and the main session did not search the older repository for one |
| BlockLanding, BlockLanding2, TwoScale | DoorFlank, `LRC/Cascade/Iteration` |
| PathLaws | `LRC/Cascade/Arrangement`, `LRC/Spec` |
| Boundaries, LandingExceptions | GrandReturnN (`lonely_mirror`), v9 Theorem 10 |
| RealCase | `LRC/Cascade/*` displacement at the bound, read for the idea only |
| FiveReach, DMax, PathClassify, CarvingLineage, AcrossN | no older Lean declaration named in the header |

*End of draft. Nothing here moves a grade in v21. No existing document was edited.*
