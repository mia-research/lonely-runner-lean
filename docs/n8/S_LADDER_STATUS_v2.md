# S-ladder status v2 (v1 unchanged): the AP with one, two and three runners moved to any speed

Written 2026-10-23 (log entries E553 to E567); v2 adds `ratio_lands`, the AP-neighbourhood landing law and the cross-type section. Lean: `LonelyRunnerFresh/Fresh/` (new files; nothing committed). All statements are about
the arrangement `oneMover` / `twoMover` / `threeMover` (speeds `c + i` except the movers), a subject `k`, and the cascade statement
`Lands v k a` (`SelfMoverAllCommon.lean`): a first isolation instant `T > 0` exists, the cascade from `1/(8a)` reaches a fixed point, and every
fixed point is `T`. `a` is a disparity of the subject (the nearest runner's, or the least frozen reading). Grades: [L] Lean, standard axioms,
sorry 0; PROV-COV = inherits a [PROVISIONAL: covering] gap cover; PROV-CNT = [PROVISIONAL: counting tool].

## What is proved

| rung | statement | Lean | grade |
|---|---|---|---|
| S1, mover not the subject | any `m != k`, any `x != c + k`: `s1_nonsubject` | `OneMoverFinalNS`, `OneMoverLandingAll` (d beyond the least frozen reading), `OneMoverLandingAllC` + `OneMoverBelowLe_*` (d at most it, incl. d = a) | [L], PROV-COV |
| S1, mover is the subject, nearest-runner window | `selfLanding_<cfg>` for delta <= 1/24, 112 configurations | `SelfMoverCells_<cfg>` (cells assume N0 >= 2, delta <= 1/16; assemblies stop at 1/24) | [L] |
| S1, subject, 1/24 < delta <= 1/2 | `selfLandingAP_<cfg>` | `SelfMoverCellsN_<cfg>` (N0 = 0, 1, 2) | pilot `k0i1m` [L]; the other 111: batch (see "Running") |
| S1, subject, 1/2 <= delta <= Dmax | `selfLandingExt_<cfg>`, 28 configurations (Dmax = 1: the next runner is the subject's own old place; Dmax = 7/6: outward) | `SelfMoverCellsExt_<cfg>` | [L] (28 of 28) |
| S1, subject, delta >= 7/6 or the extreme runner moving outward | `outside_below_k_ne0`, `outside_below_k0`, `outside_above_k_ne7`, `outside_above_k7` | `SelfMoverOutside` | [L] |
| S1, subject, assembly | `subject_moving_k<k>` for each `k` (every position `x` not another runner's) | `SelfMoverAll_k<k>` (+ `SelfMoverAllLeaves`, `SelfMoverCommon2`) | generated for k = 2 only; compile waits for the `SelfMoverCellsN_*` files |
| S2, both movers >= D0 | `land2H<set>`, `landing_twoMover2_<set>`, D0 = ceil(1/L) (6 to 112 over 37 frozen sets) | `TwoMoverLarge2_*`, `TwoMoverLandingAll2` | [L], PROV-CNT, PROV-COV |
| S2, conditional form | `land2C<set>`: the landing is the first common clear instant of the pair in the first wide frozen piece whenever one exists there | `TwoMoverCond_*` (37) | [L] |
| S3, all three movers >= D | `three_movers_large`, D = ceil(4/L) (13 to 280 over 51 frozen sets) | `ThreeMoverLarge_*`, `ThreeMoverLandingAll`, `ManyClear` (`three_clear_in_all`), `ThreeMoverDefs`, `ThreeMoverCases` | [L], PROV-CNT (measure bound), PROV-COV |

## What the mechanism is

The landing is the first lonely instant of the frozen readings (integers, period 1, a union of pieces per lap) at which the movers are also
clear. For a mover not the subject the frozen set decides which piece; the mover only selects within it. For the subject moving, every other
runner's reading is `|o| tau - sigma u` on a torus with `u = delta t`; the landing depends on `tau0 = frac(1/(8 delta))` and, for delta
above `1/16`, on the integer `N0` (0, 1, 2 handled as fixed numerals; N0 >= 2 symbolic).

## What is NOT proved

* S2 below D0 (and the mixed regime, one mover large, one not): observation only (E561). 25 of the 37 frozen sets have a pair below D0 whose
  first wide piece fails; the landing then lies in a later piece. Exact failing pairs, e.g. `{1,2,3,5,7}`: `(243/8, 279/8)` against D0 = 70.
  The cell problem is two-dimensional with ownership of boundary lines; not built.
* S3 below its threshold and any mixed regime; four or more movers (the measure bound gives nothing at four blocked sets of density 1/4; a
  lonely-runner time bound would be needed).
* The cascade's path and intermediate setters (only the zone chain inside each cell proof).
* The skeleton's five holes (`ArrBlockRule8 3/4/5/6 9`, `ArrBoundedCovered8 9`): these quantify over arbitrary cores; the ladder covers
  AP cores only, and the thresholds (up to 280) are above `9 * max(F)` (for example `{1,2,3,5}`: 80 against 45).

## Relation to the ratio condition

Any arrangement whose readings satisfy `d_max <= 7 d_min` is lonely at `1/(8 d_min)` (`APNeighbourhoodN`, Thm 4.8). The ladder results above are
the cases where the movers leave that ratio (mover disparities beyond 7 times the nearest frozen or nearest-runner reading), so they fall in the
separated or bounded-gap parts of the skeleton, not in the ratio-seven part.

## Running (2026-10-23)

`experiments/n8/batch_n/run_n.sh` compiles `SelfMoverCellsN_<cfg>` for the remaining configurations; `_progress.txt` there is the record.
After it: `s3_gen_lean_selfall_v1.py <k>` for k = 0..7, compile, then `s1_all_landing` (any runner moved to any position, any subject).


## Added in v2

| rung | statement | Lean | grade |
|---|---|---|---|
| any number of movers, ratio at most 7 | `ratio_lands`: every disparity of the subject in `[m, 7m]` (m the least, attained): `1/(8m)` is the first isolation instant and `Lands` holds | `RatioLanding` | [L] |
| AP neighbourhood, every subject | `ap_nbhd_firstIso`: speeds within 1/128 of `c + i`; first isolation instant exists; end subjects: three explicit instants chosen by two linear inequalities (`apLaw_end0`, `apLaw_end7`) | `APLaw`, `APLawArr`, `APLawEnd`, `APLawEnd7`, `APLawAll`, `APLawAll2` | [L] |

## Cross-type mechanism notes (E567)

* Every certificate in the ladder is a zone chain: the landing is the upper end `(M + 1/8)/d` of the last zone, consecutive zones overlap strictly, every
  reading is clear at the end. Once the laps `M` are numerals, every chain inequality is linear in the parameters (the deviations, or `(delta, y)` for the
  subject moving). One generator shape serves S1 gap chains, the self-mover cells and the AP law.
* Near the AP the lonely classes are the units of Z/8 (instants `c/8`, `c` odd); each class has a tight pair `{c^-1, -c^-1}`; `(Z/8)^x/{+-1}` has two pairs
  `{1,7}`, `{3,5}`; each pair gives one linear condition (`x7 <= 7 x1` for class 1, `3 x5 <= 5 x3` for class 3). So a deformation faces two binary choices and
  the first instant is one of three formulas with 0, 6, 11 moves (class 7 is never first).
* Moving one reading near the AP (S1, S2 near the completion) is the law with only that reading perturbed; the subject-moving family is NOT the nearest runner's
  landing (no ordering between them in 5,376 samples).
* Farther from the AP the same mechanism gives more chambers (3, 4, 8, 20, 68 distinct paths at relative radius 1/64, 1/32, 1/16, 1/8, 1/4), each bounded by one
  more linear inequality, some with a constant term; no new kind of path was seen.
* Lands is equivalent to the subject being lonely (existence of a first isolation instant); the content of each rung is the explicit landing formula, not the
  existence.
