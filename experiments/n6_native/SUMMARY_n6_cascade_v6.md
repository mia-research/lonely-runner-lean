# The order-six cascade: established, open, and against BHK — v6

2026-10-15. Supersedes v5 (kept). Source: `LOG_n6_native_v1.md` E1–E41 and the files named there.

*Process item (E35), owner's call:* v5 was edited in place while under the compile-diff gate, before promotion;
the versioning memory reads "ANY edit = new version" with no draft exception.

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
    opening exists there. **Open.** E37's reading: "§5 at this level is the cascade itself (described exactly)
    without a forcing argument; BHK's Lemma 4 forces only the long-window regime." *Reading, not an owner
    ruling (conversation after E37, not logged):* since existence needs an isolation, not the first (E30), a
    proof of §5 need not account for the cascade's earlier instants.
  - §5 natively (§4A): BHK's two-step structure (a window lemma for runners 4, 5; windows supplied by runners
    1–3) rewritten in framework objects. The window lemma is proved in Lean and is sharper than BHK's Lemma 4.
    Window existence is read off each set, not derived; the q = 4 case is not treated natively. **Partial.**
  - §7: not yet treated natively. **Open.**
  - §6: not compared case by case. **Open.**
- **Specific gap:** a residue-level reason for the existence of the cascade's lonely openings in §5 and §7,
  in place of BHK's length lemmas. For the §4A route in §5 (BHK's architecture in framework objects), what is
  missing is a derivation of the window geometries from runners 1–3 (v1 + v2 = v3) and the q = 4 case; §7 is
  untreated.

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

## 4A. §5 natively (E35–E41)

Sample: all 2,444 §5 sets (BHK case D | v1) in [1,40]. J123 = a stretch on which runners 1, 2, 3 are all clear;
runners 4 and 5 cut it (the cut-stretch language of §4).

| Finding | Grade |
|---|---|
| The cascade ends at the left end of the first lonely piece of J123 in 2,279 sets; the other 165 end at a single-point box. J123's right end is set by runner 3 in 2,427; one lonely piece in J123 in 1,695. A first run computed band ends in floating point and misplaced 1,023 endings; fixed (E35) | [C] |
| Every J123 window in which 4 and 5 share a clear point: the first such contains the ending in 2,299 sets; the 145 others end at single-point boxes. Endings in the first or second window: 1,851 / 429. Failing windows before the ending: 566. Some "never clear" windows start with the runner reading in band: it reads exactly at an edge, so a point, not a piece. Longest failing window 0.494 runner-4 laps; every window of 0.5 runner-4 laps or more **in this sample** has a shared point; largest failing length by d5/d4: below 1.5: 0.494; 1.5–2: 0.449; 2–3: 0.407; 3 or more: 0.25; BHK's Lemma 4 length (2/3) lies above all failures (E36) | [X] control; [C] |
| Short windows (< 1/2 runner-4 lap): success is a race between 4's entry and exit, 5's entry and exit, and the window's end (runner 3's exit), decided by one pair inequality; case logic reproduces the shared flag 1,682 / 1,682 (a first version listed only one clear piece of runner 4, which can leave and re-enter in a short window: 39 mismatches, fixed). This is the lap-box criterion restricted to these runners: it names the deciding pair, no new mechanism (E37) | [X]; reading |
| Sharp window threshold L(ρ) = max(1/3 + 1/(3ρ), (m + 1/3)/ρ), m the largest integer below (ρ+1)/3, ρ = d5/d4 ≥ 1; at most 2/3, equality at ρ = 1; resonant, e.g. L(5/2) = 8/15. Upper bound: no start exceeds L on 237 ratios, and the search comes within 3.3e-4 of it (E38) [numeric]; sharp exactly at 10 ratios (E41 control) [X]; sharpness of the general formula rests on E38's derivation [A]. E36 data: none of the 566 failing windows has l4 ≥ L(ρ); all 833 windows with l4 ≥ L(ρ) succeed [X] | as marked |
| `window_two`: speeds 0 < a ≤ b; a window of length ≥ 1/(3a) + 1/(3b) and ≥ (m + 1/3)/b for every integer m with 3ma < a + b contains an instant with both clear. `window_two_uniform`: 2/(3a) always suffices (`WindowTwoRunner_v1.lean`) | [L] |
| Against the source: BHK Lemma 4 ("a 45-block has length < 2x4/3") has the same proof structure, so `window_two_uniform` is Lemma 4 and `window_two` sharpens it by the speed ratio. Citation-verifier owed before this is cited | reading of the printed proof |
| Over one period of each §5 set, a single long-enough J123 window exists in 1,862 sets (1,416 also reach BHK's 2/3); in **582 it does not**, so "a long enough stretch occurs" fails across §5. In BHK, Case 5.1's premise (22), "Lemma 4 implies x4 > 3/4", is where the sharp L(ρ) would apply (E38) | [X] |
| Two windows, phase-free (BHK's triple configuration rewritten: for every start of runners 4, 5, one of two J123 windows has a common clear point). Pair scope: J123 windows within one period, up to three windows apart (SAFE pair found at distance 1: 331, 2: 117, 3: 128 on the N = 600 grid); the verdict is relative to this scope. E39 control: at each set's own phases the formula's first common time equals the exact one in 3,478 of 3,478 (a first control against positive-length intersection disagreed in 83: touching single points, which are lonely instants). Exact decision per window pair (E41): lines of slope ρ, finitely many critical offsets, rational arithmetic; completeness of the critical list argued. **576 of the 582 covered**; 2,811 pairs tested; four pairs the grid had called SAFE fail in slivers about 5e-4 wide (e.g. (2,18,20,28,31) pair (0,1), c = 731/1680), each such set still covered by another pair; two failing starts verified independently, margins down to 3e-4 | exact [X] given [A] |
| Of the 576: 540 in BHK's k = 1, 2 (Proposition 11's case), 36 with k = 3, 4, 6, 7 (Case 5.1) (E39) | [C] |
| The 6 left: (1,3,4,5,6), (2,6,8,10,11), (4,12,16,20,23), (4,12,16,20,25), (5,15,20,24,26), (7,21,28,36,40), all k = 1 or 2 and near k·(1,3,4,5), the first four speeds of the tight set (1,3,4,5,9) (E39); all v1/v3 = 1/4: BHK's q = 4 case, **Lemma 13**, ported in Lean (`OrderSixPropElevenN.lean`, explicit q = 4 gaps). J123 is rigid there (four windows per period, lengths 1/6, 5/18, 5/18, 1/6 in BHK time: BHK's I1, I2 and mirrors), all shorter than L(ρ). For r = 4v4/v3 = 5 (four sets: (1,3,4,5,6), (2,6,8,10,11), (4,12,16,20,23), (4,12,16,20,25)) the lonely piece is BHK's own 1234-gap [13/6, 68/30] (entered by 3, left by 4) or its mirror [26/15, 11/6]; (4,12,16,20,23) also has a shorter piece in I2, [152/69, 34/15], entered by 5; single-point lonely instants also occur (entered by 4, left by 1, at 10/3, 14/3, …). For non-integer r (24/5, 36/7: 16 and 22 lonely pieces or points per period, longest 5/18, entered by 2 or 3, left by 3 or 2): explicit inequalities show I2 is covered by neither runner 4 nor 5 alone, and then Lemma 12 (denominator argument) forces integer r, s, which these sets do not have (E40) | [X] per set; reading |

**What §4A does and does not give.** One window: proved (Lean). Two windows: exact per geometry, with the
critical-list argument not formalised. In both, the windows are read off each set, not derived from the merged
pair. The q = 4 case is open natively. For proof purposes the native §5 is BHK's architecture in framework objects
with a sharper window lemma, not a different route.

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
- "A long enough J123 stretch occurs in every §5 set" (single-window step) — **false**: 582 of 2,444 sets (E38).
- *Note on the E2 set-aside above.* E2 set aside `six_window_mechanism_v1` parts (ii)–(iii),
  `six_folded_coverage_v1` and `six_folded_failures_v1` (measure, density, sampling and covering statements),
  including exact ones: a length condition on the longest lonely component, and a phase-free test that every
  progression of openings meets the lonely set. Their object was the lonely set of four runners against flank
  openings. §4A's one-window and two-window steps have a different object (J123 windows against runners 4 and 5)
  and were taken up on the owner's direction (E38, E39). The two-window test is phase-free, the same kind of
  statement as `six_folded_coverage_v1`. Whether §4A sits inside or outside the E2 set-aside is not recorded:
  owner's call.
- Grid SAFE verdicts (E39) — **superseded** by the exact decision (E41); four grid-SAFE pairs were not SAFE.

## 6. Open

1. **§5 and §7: why a lonely opening exists where the cascade finds one** (which openings are lonely is exact;
   existence is not explained). This is the gap between native and reformulated. Along the §4A route (§5):
   1a. derive the window geometries (one long window, or a SAFE pair) from runners 1–3 with v1 + v2 = v3, in
       place of reading them off each set (BHK (31)–(32); BHK Lemma 14, a 0123-gap length lemma for the merged
       pair, read in the source but not yet in the log);
   1b. the q = 4 case natively (BHK Lemma 13, which the reformulated track already has in
       `OrderSixPropElevenN.lean`; Lemma 12's equidistribution step as a residue count);
   1c. completeness of the critical-offset list in the exact two-window test (formalise or prove);
   1d. citation-verifier on BHK Lemma 4 / Corollary 5 against `window_two` before citing the sharpening;
   1e. §7 natively.
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

v5's next step (§5's ending instants in the cut-stretch language) was done in E35–E37. My reading, not an owner
ruling: a native proof does not have to explain the cascade's earlier instants; it needs some isolation. In §5 the
framework rewrites BHK's architecture in its own objects (§4A). It has a sharper window lemma (Lean), and an
exact two-window test covers 576 of the 582 sets a single window misses. The window geometries are not yet
derived from the merged pair, and the q = 4 case (BHK Lemma 13) is not treated natively. In §5, as in §8,
native and reformulated so far share BHK's structure; the native contribution is sharper statements in
framework objects, not a different route.
