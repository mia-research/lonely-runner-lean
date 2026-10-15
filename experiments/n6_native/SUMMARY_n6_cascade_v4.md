# The order-six cascade: established, open, and against BHK — v4

2026-10-15. Supersedes v3 (kept). Source: `LOG_n6_native_v1.md` E1–E19 and the files named there.

**Purpose (owner).** Understand how the cascade proves n = 6, or how and why the BHK proof can be
reformulated. The cascade is the oracle: it stops exactly at the first lonely instant
(`lonely_iff_run_ends`, `first_isolation_of_fixed`) and never fails; flanks, residues, laps and phases are
explanations of what it does. Order eight is a separate project; it appears here only as a comparison or
as an instrument control.

**Grades.** [L] Lean, axiom-clean (`propext`, `Classical.choice`, `Quot.sound`). [X] exact over the stated
range (0 mismatches). [C] count, not a rule. [O] open.

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

## 4. Refuted or set aside in this line

- A finite signature decides the largest-flank outcome — refuted.
- Named multipliers ±c·x⁻¹ with c ≤ 5 — at chance against a same-size random list; c grows to 10 by e ≤ 120.
- A single long window, phase-free (folded) coverage, measure/density statements — set aside as imported
  framing (owner, E2); the exact identity "openings meet the lonely set of the other four" stands.
- "93% next-lap returns" as a law — it is the lap-skip criterion below threshold.

## 5. Open

1. **Why the cascade's lonely instant exists early.** `DoorFirstLap` (d_min·T <= 1) is **REFUTED at n = 6**
   (E19): (103, 246, 300, 395, 518) has earliest lonely instant T = 1/72 and d_min·T = 103/72 (13 moves;
   cascade and exhaustive enumeration of openings agree; directed search, instrument checked by an n = 8
   positive control). That set is not residual. Every residual set in [1,40] stops inside runner 1's first
   clear lap (max v1 T = 35/48) [C]; whether that holds for all residual sets is **open** — the
   residual-restricted search was void (no positive control; stalled at its seed). So "the first lap of the
   slowest runner" is not the general reason a lonely instant exists early.
2. §5 and §7: a residue explanation of why a lonely opening exists in the first meeting window (which ones
   are lonely is exact; existence is not explained).
3. §6 case by case; §8's inner sub-cases (8.2.1, 8.2.2, v4 < 2 v3) against cascade readings.
4. The BHK §6 omission of (1/N_G, ±3/N_G): independent confirmation owed.

## 6. Answer to the purpose, as it stands

The framework proves order six by carrying BHK into its objects. The cascade's own route reproduces BHK
exactly in §8; in §5 and §7 it shares BHK's reductions and regions but reaches earlier lonely instants that
BHK's length lemmas do not account for. A proof following the cascade's own route would need, in place of
those lemmas, an exact explanation of why a lonely opening exists. It cannot be the first lap of the
slowest runner in general: `DoorFirstLap` is refuted at n = 6 (item 1).
