# The order-six cascade: established, open, and against BHK — v5

2026-10-15. Supersedes v4 (kept). Source: `LOG_n6_native_v1.md` E1–E34 and the files named there.

**Purpose (owner).** Understand how the cascade proves n = 6, or how and why the BHK proof can be
reformulated. The cascade is the oracle: it stops exactly at the first lonely instant
(`lonely_iff_run_ends`, `first_isolation_of_fixed`) and never fails; flanks, residues, laps and phases are
explanations of what it does. Order eight is a separate project; it appears here only as a comparison or
as an instrument control. Existence needs an isolation, not the first one (owner, E30).

**Grades.** [L] Lean, axiom-clean (`propext`, `Classical.choice`, `Quot.sound`; kernel `decide` files: no
axioms). [X] exact over the stated range (0 mismatches). [C] count, not a rule. [O] open. [A] argued, not
formalised.

## 0. Status against the purpose

- **Reformulated: complete.** The framework track's order six (`LRC.OrderSixN.existenceAtN_six`) is BHK
  carried into framework objects, Lean-checked and axiom-clean. Nothing below changes this.
- **Native: no proof.** The native work gives exact descriptions of what the cascade does, and of how an
  isolation is handed on under deformation. It does not give a forcing argument.
  - §8: the cascade's route is BHK's route (same case split). Native and reformulated coincide.
  - §5, §7: the cascade shares BHK's reductions but ends at earlier instants that BHK's length lemmas
    (Proposition 11, Lemma 4, Case 5.1) do not account for. A native proof needs its own reason why a lonely
    opening exists there. **Open.**
  - §6: not compared case by case. **Open.**
- **Specific gap:** a residue-level reason for the existence of the cascade's lonely openings in §5 and §7,
  in place of BHK's length lemmas.

## 1. Context that is settled

- Two independent tracks: classical (`SmallN/IntLRC_3..7`, integer speeds, gcd 1) and framework
  (`Spec/`, real speeds). Bridge: `classical_certificates`, `framework_intLRC` [L]
  (`unified-lonely-runner-paper/lean/Bridge.lean`). The framework track's order six is BHK carried into
  framework objects; it is a complete, axiom-checked proof.
- Residual class `SixResidual`: implementation matches Lean on every field [L checks]; 2,771 / 17,135 /
  119,572 primitive residual sets in [1,30] / [1,40] / [1,60]; rule-based reduction (`OrderSixN.lean`) is
  not on the order-six proof path.

## 2. What the cascade does (all cases)

| Explanation | Grade |
|---|---|
| First move at 1/(6 v1): blocking ratio test, setter = latest next opening (`first_move`) | [L], [X] |
| Every later move: blocking is the residue band at the current flank opening; next setter = latest nearest-lap opening (a residue walk) (`later_move_blocking`) | [L], [X] 25,638 moves |
| Opening-1 rule: x in the way at 7/(6z) iff \|7x − 6Nz\| < z (`opening_one_inWay_iff`) | [L] |
| Staircase: same opening index ⇒ strictly smaller flank (`staircase`) | [L], [X] |
| Early end criterion v1(6k+1) < 2x at the final state (`early_iff`) | [L] |
| Returns: inside the proved growth window (`ChainBounds`); return lap = nearest integer to (P+1/6)g; lap skip iff g > (6P+11)/(6P+1) (`lap_skip_iff`); position in window set by setter depths | [L], [X] 1,188 |
| Cell reduction at a divisible flank e = 6E; residue pinning to {1,2,3,5}, {1,3,4,5} (`cell_criterion`, `all_shifts_blocked_iff`) | [L] |
| Coarse blocking needs every unit residue: possible iff φ(n) ≤ n − 2 (n = 6: two patterns; n = 7: none; n = 8: one) | [X] |
| Largest flank caps the cascade's stop, except 13 sets (all max ≤ 30), capped there by the second-largest | [X] to 150 |
| Scaled blocking families kP + {e}: failure depends on phase k mod n and e; complete list (12 and 3 pairs) for every k (finite check + window lemma) | [X] + existing lemma |

## 3. Case by case against BHK

| BHK case | Cascade | Verdict |
|---|---|---|
| §8 (v3 ≤ 3 v1) | Walk of {v1, v4, v5} in 3,710 / 3,716 [C]; slow three clear at v5's opening 1 [L]; steps on iff 7 v4 > 5 v5 [L]; runner j blocks at v4's opening 1 iff 5 v4 < 7 v_j [L]; exceptions chained to v3 > 125 v1/49 [X] | **Reproduced**: BHK's split 5 v4 < 7 v3 and `s81_step1` (5 v1 < v5, 5 v5 < 7 v4) are the cascade's conditions |
| §7, §2 (generic) | Runner 3 the commonest setter; ends in a meeting-time lap of runner 3 more than chance when ending there (56.5% vs 35.8%) [C]; 63% end at other flanks [C] | **Same region, own route** |
| §5 (D \| v1) | Ends at runner 4/5 most often, runner 2 in 22–31%, runner 3 almost never [C]; Prop 11 windows: 16.1% vs 11.2% (k = 1), 3.7% vs 12.1% (k = 2) [C]; k ≥ 3 ends in the first meeting window (forced by early end); in-window lonely openings at 4/5 = three residue conditions with runners 2, 3 merged (`merged_pair_iff`) [L]; outside the window, band intersection [X]; ~77% of 4/5 endings in 123-gaps shorter than Lemma 4's length [C] | **Shared reduction** (v1 + v2 = v3 collapses runners 1–3), **different instants**: BHK's length lemmas do not account for most cascade instants |
| §6 (D \| v3) | Runner 2 clear at runner 3's opening k < c iff 2c − 1 ≤ 6k (`s6_runner2_at_runner3`) [L]; route sorted by c = v3/D [C] | **Not compared** case by case |

## 4. The isolation under deformation (E21–E34)

Frame (owner): existence holds at the grid (AP) and at residue-grid sets; deformation moves the location.
Path samples: E21 and E22 used 286 ordinary residual sets plus the 11 chains; from E23 on, every 8th residual set
in [1,40] (2,142 sets) plus the 11 chains. Axis paths move v5, v4, v3, v2 in turn (E21–E33), straight lines move
all speeds together (E34). Statements about paths hold on
these paths only. "Alive" means alive as a closed box (possibly a single point), not positive length (E33).

| Finding | Grade |
|---|---|
| Lap box: lonely iff every ordered pair has (6k_i+1) d_j ≤ (6k_j+5) d_i; instant = latest entry (`lap_box_lonely`) | [L] |
| The grid c(1,…,5) sits on the face d_5 = 5 d_1: one side keeps the 1/6 event (spread box), the other the 5/6 event (`grid_tight_pairs`); every perturbation opens exactly one | [L], [X] 4,000 |
| Tight integer 5-sets in [1,200]: only (1,2,3,4,5) and (1,3,4,5,9), both simple (one entry, one exit per lonely point); matching against the literature on tight instances not checked (citation-verifier owed if used) | [X] 2,450,913,356 sets |
| Mirror at an integer degenerate point: the opening conditions at p and 1 − p are reverse inequalities (`mirror_opening`) | [L] |
| Every 2-torus through a tight vector of either class ((1,2,3,4,5) or (1,3,4,5,9) up to permutation and sign; the classes are those of the E24 search, entries ≤ 200) other than its own circle meets the open cube: residues mod 11 (`torus_witness_grid`, `torus_witness_other`; kernel checks `check_grid`, `check_other`); lattice step and Kronecker density | [L] core; [A] the rest |
| The deformation frame does not reduce the problem: configurations without rational relations are lonely (Kronecker), so the lonely set is dense and its closedness is existence itself | [A] |
| Forced by construction, not found: closures of the earliest instant are by the moving runner (frozen runners keep their status), the first setter after a closure is the mover (E21); a box dies when its earliest exit meets its latest entry, and only the mover changes (E28) | forced |
| Tracking the earliest instant reduces displacement to the cascade again: it shows how, not why (E21); E30: following the earliest instant rebuilt the cascade's steps | reading |
| Lonely intervals in [0, 2/v1]: every axis path keeps at least 2 after the first step (E22); a cap-type observation, the same kind as DoorFirstLap, not a forcing mechanism | [C] |
| Earliest-isolation handovers (E28): control, the cascade's earliest instant just past each death equals the takeover's instant in 7,326 of 7,326; no death without a takeover; over 7,294 ordinary deaths the takeover is at the mover's next entry (4,747) or later (2,547), at the blocking runner's entry in 2,049 of these; the 7,326 of the control include the chains | [X] control; [C] |
| Readings at the takeover instant (E29): the runner nearest an edge is the one at an edge at the death, now a little inside (old flank F just entered, kind 1; mover just re-entered, kind 2); when F is faster than the mover and something blocks the mover's next entry, the isolation often returns to F's own entry, a whole number of F-laps later | [C], observation only |
| Following the isolation: at every death of the followed box another box is alive across the death; thin moments 0 (24,310 deaths on axis paths, 6,071 on straight lines; on these paths no handover depends on the 1:5 coincidence) [C], path-independent. Takeovers born at the death: 860 on axis paths, all at speed ratio 5 between the mover and a partner; 22 on straight lines, ratio 5 in 15, the r = 11 double coincidence once (family 7b − 5b' = 3; constructed control at r = 11), six at other ratios (23/19, 41/7, 17/13, …), so not always the 1:5 or 1:11 mirror pair | [C], path-dependent; controls [X] |
| Neighbouring boxes (one runner one lap apart) are the two pieces of the others' common stretch J cut by that runner's blocked window (`neighbours_open_iff`, `stretch_long`, `takeover_open`, `piece_lonely`) | [L] |
| The cutter is usually the fastest runner; J usually holds exactly two of its bands | [C], path-independent |
| Takeover condition at a death: J's binding runner outlasts the cutter's blocked window (5/6 − ρ_q > d_q/(3 d_r) and its mirror); axis paths: strict in 8,391, equality in 409 (the takeover's piece is a single point at the death and opens just past it), fails 0; straight lines: strict in all 2,466. Carried by "a third of a lap left" in 62% on straight lines, 28% on axis paths. Path-dependent: how often the cutter's speed carries it, the 7/9 residue on axis paths (grid speeds of the unmoved runners), and the dominance of births at ratio 5 | [C]; frequencies and dominant residues path-dependent |
| Instant d_min·T: integer sets in [1,120] leave the slowest runner's first lap in 68 sets (spread floor(d_max/d_min) in {5, 6}), never its second; their earliest boxes (1,3,4,5,7) or (1,2,3,4,6), all inside (1,3,4,5,7); real configurations (adversarial climb) never leave the slowest runner's second lap, with late configurations also in (1,3,4,5,6); supremum just across the face d_max = 5 d_min about 1.4394 (candidate 95/66) | [X], [C], candidate |

What §4 does not give: a reason why the binding runner always outlasts the cutter's window. That is the
handover question, and by the density remark it is equivalent to existence. §4 is description, not forcing.

## 5. Refuted or set aside in this line

- A finite signature decides the largest-flank outcome — refuted.
- Named multipliers ±c·x⁻¹ with c ≤ 5 — at chance against a same-size random list; c grows to 10 by e ≤ 120.
- A single long window, phase-free (folded) coverage, measure/density statements — set aside as imported
  framing (owner, E2); the exact identity "openings meet the lonely set of the other four" stands.
- "93% next-lap returns" as a law — it is the lap-skip criterion below threshold.
- `DoorFirstLap` (d_min·T ≤ 1) — **refuted at n = 6** (E19): (103, 246, 300, 395, 518), T = 1/72,
  d_min·T = 103/72 (not residual; fails only `no_free_flank`); 13 moves; cascade and exhaustive enumeration of
  openings agree; directed search, instrument checked by an n = 8 positive control.
- First-lap cap for residual sets — **refuted** (E20): 11 residual sets in [97,150] with τ > 1, all with τ > 1 (none in (5/6, 1]), three verified by `dfl_verify_v1.py`; max 903/660 at
  (21,53,64,84,110); resonant chains, ratio ≈ 1.31; chain conditions necessary (observed), not sufficient
  (81,402 chain sets, 11 leave the first lap).
- The open-and-closed template (E23–E26: persistence at degenerate configurations, no escape to infinity) —
  **withdrawn as a route** (E27): imported shape, vacuous by the density remark. Its results stay as facts (§4).
- A uniform second-lap bound τ ≤ 11/6 checked over ratio space — **not pursued**: a cap, and the check has the
  shape of the covering route (E26, E27).

## 6. Open

1. **§5 and §7: why a lonely opening exists where the cascade finds one** (which openings are lonely is exact;
   existence is not explained). This is the gap between native and reformulated.
2. §6 case by case; §8's inner sub-cases (8.2.1, 8.2.2, v4 < 2 v3) against cascade readings.
3. *(Resolved, kept for the record.)* Whether every residual set stops inside runner 1's first clear lap: no
   (E20, §5); every residual set in [1,40] does (max v1 T = 35/48) [C].
3a. v4's headline question, why the cascade's lonely instant exists early, has no general answer: not the first
   lap (§5), and the deformation picture restates existence (§4). Open 1 is its form in the BHK cases; Open 4 its
   form under deformation.
4. The handover question (§4): why J's binding runner outlasts the cutter's blocked window. Equivalent to
   existence; open.
5. Degenerate configurations: tight sets beyond 200; real rank ≥ 2 lattices whose all-nonzero vectors all
   have entries above 200 (E24–E25).
6. The BHK §6 omission of (1/N_G, ±3/N_G): independent confirmation owed.

## 7. Answer to the purpose, as it stands

The framework proves order six by carrying BHK into its objects. The cascade's own route reproduces BHK
exactly in §8; in §5 and §7 it shares BHK's reductions and regions but reaches earlier lonely instants that
BHK's length lemmas do not account for. A proof following the cascade's own route would need, in place of
those lemmas, an exact explanation of why a lonely opening exists. It cannot be the first lap of the slowest
runner in general (`DoorFirstLap` refuted at n = 6), and the deformation picture (§4) restates existence rather than forcing it.
The next step is §5: the cascade's ending instants there, read in the cut-stretch language of §4.
