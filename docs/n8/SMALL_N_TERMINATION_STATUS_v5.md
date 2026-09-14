# Termination of the moment iteration at small orders — status

Version 5, 2026-09-15. The imports found by the owner-requested drift audit (`OBJECTION_LEDGER_v1.md` Part 7) are
excised and replaced (revision-list item 51): the zone-width count is gone from the Lean file and from this document,
replaced by the slowest-setter recursion; the cap is stated as `R < 4`. Covers the work recorded as items 37–51 of `V7_REVISION_LIST_v1.md` (commits `b29c413` …
`7cf51b4`, plus the v14 excision). Everything below is stated in the framework's objects: the moment iteration (move to the latest next
opening of the runners in the way), its lap zones, setters, laps and readings. Grades follow `CLAIM_GRADES_v1.md`.

## 1. The question

Version B at a given order: *for every arrangement, the iteration from the bound `1/(n·d_min)` reaches a fixed point*.
The fixed point is then the first isolation time (`first_isolation_of_fixed`, proved for every `n`). So Version B is a
statement about termination only.

Notation: threshold `1/n`; `k` = number of differences of the subject (the owner's order `n` has `k = n − 1`); `a` = the
nearest difference; `F(Q) = (Q + 1/n)/(Q − 1/n)` = the growth bound of a move set at lap `Q`.

## 2. What is proved in Lean

All in `experiments/n8/MomentIterationN_v14.lean` (each `vN` contains all earlier sections), outside both Lean trees,
imports only `ConstructionN`. Compiles with no errors or warnings, no `sorry`; every axiom line
`[propext, Classical.choice, Quot.sound]` (63 lines).

### 2.1 Termination results (the table)

| differences `k` | orders proved | theorem | moves at most |
|---|---|---|---|
| 2 | every `n ≥ 3` | `FewDifferences.two_diffs_stop_within_one_move` | 1 |
| 3 | every `n ≥ 4` | `FewDifferences.three_diffs_stop_within_three_moves` | 3 |
| 4 | every `n ≥ 6` | `FourDifferencesSix.four_diffs_stop_ge_six` | 7 |
| any `k` | every `n ≥ max(9, 2^(k−1))` | `SlowestRecursion.stops_slowest_recursion` | `2^(k−1) − 1` |

**Version B form** (section `VersionB`): each row also gives the answer — an explicit iterate that is lonely with no
earlier positive lonely time (`VersionB.two_diffs`, `three_diffs`, `four_diffs`, `slowest_recursion`, `order_three`,
`order_four`).

Special cases at the owner's orders: `n = 3` (`TerminationThree.three_stops_within_one_move`) and `n = 4`
(`TerminationFour.four_stops_within_three_moves`, with the time bound `a·T < 3/4`).

**Open:** `k = 4, n = 5` (the owner's order 5); `k = 5` at `n = 6 … 15`; every owner order `n ≥ 5`.

### 2.2 General-`n` tools

| tool | statement (every `n` unless marked) | section |
|---|---|---|
| general iteration | soundness, first-ness, completeness given termination, `lonely_iff_run_ends`, flank, scale bridge, drift lines, slot-sharers at threshold `1/n` | `MomentIterationN` |
| capped chain stops | iterates `≤ U` for all `N` ⇒ some iterate fixed | `ChainBounds.exists_fixed_of_capped` |
| move growth | a move set at lap `Q` multiplies the time by `< F(Q)` | `ChainBounds.move_growth` |
| return growth | a runner that left at lap `P` is back in the way only after growth `> (P + 1 − 1/n)/(P + 1/n)` | `ChainBounds.return_growth` |
| return lemma | return straight after a move at lap `Q`: `Q(n − 2) < 2P + 1` | `TerminationFour.return_lemma` |
| W1 (`n ≥ 4`) | no return straight after a move by a runner at least as fast | `WordRules.no_return_after_faster` |
| W2 (`n ≥ 4`) | no four consecutive moves `y z y z` | `WordRules.no_four_alternation` |
| setter pigeonhole | a setter repeats within `n − 1` moves while the nearest runner is clear | `NearestState.repeat_within` |
| nearest reading | `a·t_N ≤ (1/n)·∏ F(lap)`; nearest runner in the way ⇒ product `> n − 1` | `NearestState` |
| nearest clear early | clear at iterate `j` whenever `((n + 1)/(n − 1))^j ≤ n − 1` | `FewDifferences.nearest_clear_first_moves` |
| slowest-setter recursion | a run of moves by `r` runners has `≤ 2^r − 1` moves when `2^r ≤ n` | `SlowestRecursion.run_length_le` |
| few faster moves | no return across `≤ g` moves at laps `≥ P + 1` when `n ≥ 2g + 2` | `FasterMoves.no_return_after_few_faster` |
| three-move bound (`n ≥ 6`) | `F(A)F(P + 1)F(A + 1) ≤ (P + 1 − 1/n)/(P + 1/n)` for `2A ≥ (P + 1)(n − 2)` | `FourSixAlgebra.three_move_bound` |
| sorted laps | `m` distinct laps `≥ 1` ⇒ product of lap factors `≤ ∏_{r=1}^{m} F(r)` | `FourSixAlgebra.sorted_lap_prod` |

## 3. What the computations show (not proofs)

Scripts in `experiments/small_n/`. Chain computations use exact rationals and agree with BSM wherever checked; the
relaxed-chain LPs use floating-point `scipy linprog` (HiGHS) with strict margins `EPS = 1e-7`, so their suprema are
rationals recognised from float optima over bounded searches.

- **Chain length by order** (`chain_depth_by_n_v1.py`, `chain_length_k_by_n_v1.py`): owner orders — longest found 1 (n=3),
  3 (n=4), 137 (n=5), and long at n = 6, 7, 8. Long chains are resonances (near-rational speed ratios) and barely move the
  time (`n5_cycles_v1.py`: 300 moves, nearest reading 1.38).
- **Where the nearest runner leaves its first clear window** (`nearest_window_anneal_v1.py`, `_v2.py`): never at n = 3,
  4, 5 in any search; **leaves at n = 6** (verified case, speeds `1, 59733/25000, 299191/100000, 392283/100000,
  516561/100000`; BSM agrees), and at n = 7, 8, 9 — always below the second window's edge `2n − 1` in these searches.
- **Relaxed chain as a linear program** (`n5_relaxed_lp_v1.py`, `relaxed_lp_general_v1.py`): with a word and its laps
  fixed, all handoffs are linear in the lap periods. Supremum of the nearest reading: n = 4 → 3 (matches the proof);
  **n = 5 → 31/9** (laps ≤ 12, length ≤ 11; at `dcbdcd`, laps (2,1,1,5,2,6), ratios 9/4, 27/8, 9); n = 6 → 95/11 (laps ≤ 6,
  length ≤ 14). With closed inequalities the n = 5 value jumps to 4.125 at an all-boundary chain that BSM counts clear —
  the boundary treatment is load-bearing.
- **Five differences at n = 7 … 10** (`k5_structure_v1.py`): the slowest runner never set more than one move, the
  nearest runner never set a move, longest chains 8, 6, 6, 6 — the same structure that closes four differences at
  `n ≥ 6`; not formalised (the gaps of the slowest runner are then chains over three runners, up to 7 moves long, and
  each gap shape needs its own growth inequality).
- **Product accounting alone does not cap n = 5** (`n5_resonance_products_v1.py`): the setter-lap product exceeds 4 in 733
  chains (max 5.04) while every true nearest reading stays below 4.

## 4. What is missing at the owner's orders

**n = 5 (`k = 4`).** The target is the cap: every iterate stays below `4/(5a)` — in the cascade's own quantity,
**`R = d_min/D_final < 4`** (items 35–36; largest found `31/9`). Then
`exists_fixed_of_capped` gives termination. The `n ≥ 6` proof does not transfer: at `n = 5` the slowest runner *can*
return (the 137-move resonances), so "slowest sets at most once" fails, and the sorted-lap product is too weak (§3). What
is needed is an accounting that sees how deep each setter was into its zone (the true growth of a move), not only its
lap — or a scale-separation lemma for the resonant case combined with a finite LP check of the small-lap case (item 44).

**n = 6, 7, 8.** In addition to the above, the nearest runner itself enters the chain (§3), so any cap must sit in a later
window, and the word rules must include the nearest runner as a setter.

**What the small orders taught.** The mechanisms that close `k ≤ 4` off the diagonal are (i) the return lemma and its
multi-move form, (ii) the word rules W1/W2, (iii) "the slowest setter sets at most once", and (iv) per-runner lap
counting. On the diagonal at `n = 5`, (iii) fails in the data (item 40: the slowest runner's settings recur, separated by
`cd`, `dc`, `dcd`) and (iv) is too weak in the data (§3: product above 4 in 733 chains). What stops the chain there has
to be found in the handoffs themselves — which runner sets, at which lap, and the reading it hands on.
