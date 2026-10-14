# Handover to myself — order-8 cascade mapping, autonomous run (2026-10-02, written before context compaction)

Read first: this file, then `docs/n8/CASCADE_ACCOUNT_v1.md` (what is proven vs open), then the tail of `docs/n8/RUNNING_LOG_order8_v1.md` (E317–E322), `docs/n8/EXCEPTIONS_LOG_v1.md`,
`docs/n8/ARRANGEMENT_EQUIVALENCES_v1.md`, `docs/n8/EXHAUSTION_PLAN_v1.md`. Memory rules that bit this session: never write "subject at 0", present speeds as `s + …` (owner); ask "is it needed by the argument?"
of everything added; check `docs/n8` and `experiments/nN` for an existing object BEFORE building one (the old partial residual definition cost a wrong claim, E303/E304).

## The owner's standing instruction (still in force)
Owner is away for hours. Run autonomously until tokens run out or (a) a definitive finite list of arrangements and (b) a complete understanding of the cascade. Keep careful logs; write a thorough
summary of proven vs open (done: `CASCADE_ACCOUNT_v1.md`, update it). Be honest that a finite list may be achievable (scale, variations and the conjecture's own constraints reduce the arrangements) and also that neither (a) nor (b) is reached.
Latest message: "keep going until the tree finishes, tokens have been reset". Never treat a SYSTEM NOTIFICATION as user input.

## The object (conventions)
Readings `ρ_1 = 1 < … < ρ_7` (speed minus the subject's, units of `d_min`), `R = 8·d_min·t`. Zones `Z(ρ, j) = ((8j−1)/ρ, (8j+1)/ρ)` (open). Cascade from `R = 1`: jump to the largest exit among the zones containing `R`;
the landing is the first point in no zone (right end of the union component containing 1). Path signature = list of (setter rank, lap).

## What is established (grades in CASCADE_ACCOUNT_v1.md §1–§6)
- Lean (axiom-clean, nested repo `LonelyRunner/`): `SegmentWindowN`, `IntegerGridN`, `IntegerDisplacementN`, `ClassDeviationN`, `ZoneLinkN` (all committed). Deformation route: the only owed hypothesis is the window (`PathWindowN.lonelyRunnerAt8_of_window : WindowBound → …`); a universal landing bound would supply it.
- Computed structure: hop = birth/death of a lonely component (1,716/1,716); effective-crossing rule (598/600 + 2 unobservable; locality 170/170); inert readings (61,752/61,752); strips; frozen runners fixed; results by path; lap compression FAILS (4,922/31,585).
- **Exhaustive trees** (`experiments/nN/redo/path_tree_par.py`, `path_tree_par2.py`; symbolic cascade over polyhedral cells, parallel, with a partition/soundness check on 256 exact arrangements):
  one-lap window `ρ_7 ≤ 9`: 27,517 nodes, 9,651 terminal, deepest 29, **sup landing `26433/2209 = 11.966048`** (exact vertex via `sup_exact_v1.py`: `ρ = (1, 16715503/7123545, 47/15, 726761/173745, 47/9, 15463/2673, 2209/297)`; tangent to d_min's second window edges 9 and 15, `47 = 8·6−1`);
  identical under `TT = 1e-6, 1e-9, 1e-12`. Two-lap window `ρ_7 ≤ 17`: 343,070 nodes, 117,070 terminal, deepest 29, **same supremum**, 0 violations, 2,832 s.
- Owner's suspicion `R = 12` is the middle of d_min's second clear window `[9, 15]`; the true maximum in these windows is `11.966…` (E318, E321).
- Searches (not proofs): no landing above 7 with `ρ_7 > 9`; hill-climbs from lap-added extremal seeds reach only 6.8–6.9 in windows 17, 25; paths of 41 moves exist for tight fast clusters (landing 2.27); cluster window `q ≈ 1 + 5/c` for `c ≥ 9`.

## RUNNING NOW (check first)
`path_tree_par2.py 3 3 10` — three-lap window `ρ_7 ≤ 25`, 12,640 top-level subtrees (depth 3), 10 workers, started ~20:25 local. Output `LonelyRunner/experiments/nN/redo/path_tree_par2_J3.out` (one line per finished subtree; the final line starts `DONE`,
preceded by a line `LATE LANDINGS: largest rho_7 (closure) among nodes whose state can exceed T`). At the time of writing: about 8,760 of 12,640 subtrees, ~965,000 nodes, partial sup 9.652 (heavy subtrees still running), 0 violations. Estimated total several million nodes, hours.
Check with: `wc -l`, `tail -1`, `grep -c "violations [1-9]"` on that file; `grep -E "^LATE|^DONE"`. Re-arm a Monitor (until-loop on `^DONE`, sleep 300) — monitors expire after 30 min without events.
When it finishes: (1) read `sup R` (expect `11.966048` again) and the LATE LANDINGS dictionary (if the largest `ρ_7` for `T = 7` is `≤ 9`, late landings are confined to the one-lap window); (2) log E323; (3) update `CASCADE_ACCOUNT_v1.md` §4 (three-lap) and §7; (4) commit outer (`docs/`) and nested (`LonelyRunner/`) repos SEPARATELY, always with absolute paths (`cd "/Users/trentpalelei/Desktop/Math Ex"` for docs; `cd .../LonelyRunner` for experiments and Lean).

## Things to do next (ordered)
1. Finish the three-lap tree (above). Optionally record per-terminal-cell path signatures to count the result classes in each window (the parallel script does not store them).
2. Exact certificates: for every pruned branch a rational Farkas certificate (dual multipliers from the LP, exact nullspace of the active rows with sympy) would turn the windows' computation into a proof. Estimated ~1.6M certificates per one-lap run; heavy; not started.
3. Universal landing bound over all spreads (the missing hypothesis of `lonelyRunnerAt8_of_window`): windows beyond three laps need an argument for fast readings (a fast reading is a perturbation of size ~`2/ρ` except where the slower readings' lonely components are single points: the near-AP case) and for the slow-runner-below-a-cluster case (Window Lemma W6: six readings have a lonely `R ∈ [1, 7]`; tested only; false for small `c` by the known `R* ≈ 11.9` arrangement).
4. Lean statements still owed: the five effective-crossing types; hop = birth/death; the cell lemma.
5. Memory: a `project_` memory for the cascade map is NOT yet written (CLAUDE.md §2 requires the `memory-drafter` agent for any `feedback_*`/`project_*` memory). The feedback memories written this session: `feedback_n8_no_runner_is_stationary_2026_10_02.md` (+ speeds addendum), `feedback_n8_ask_if_needed_2026_10_02.md` (+ addendum: grep before building).

## Pitfalls hit this session (do not repeat)
- Float cascade: a position that rounds to `0.9999999…` at its own exit makes a runner "still block" and loops (the "401 moves" artefact): always use an edge tolerance and CONFIRM extremes in exact Fractions.
- `exec(open(f).read().split('if __name__')[0])` breaks when the file itself contains that string; split on `'\nif __name__ =='`. A script that imports `anatomy_members_v1` changes the cwd (`os.chdir('..')`). A list named `pos` shadowed the function `pos`.
- Git: `git add` of a path inside the nested repo from the outer repo fails the whole add; run docs and Lean commits from their own repos with absolute `cd`.
- The cell/tree code reads `symbolic_cells_v1.py` by slicing; `TT` (the cell-thickness threshold) must be defined in the importing file (`path_tree_par*.py` define it from the environment).
- My earlier claims withdrawn: coalescence (E295); hops land on frozen edges (E311); the one-runner catalogue predicts the landing (E316); E303's "residual" tag (partial field set); "D = 1 grid is the cascade's start" (only when the reading 1 is present).
