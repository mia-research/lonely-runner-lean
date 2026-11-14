# Integration review, 2026-10-23: how the local arrangement results connect to the n=8 proof

Written after E565 to E575. Sources: `docs/n8/S_LADDER_STATUS_v4.md`, the agent reports A to G, `LRC/Spec/Order8SkeletonN.lean` (the skeleton and its five holes), `BandRouteN.lean`.
Grades: [L] = Lean compiled with standard axioms; [OBS] = exact computation or probe; [ARITH] = arithmetic on stated [L]/[OBS] inputs, no new Lean.

## 1. The shape of the proof the framework already has

Seven readings `r1 <= ... <= r7` of the subject, scale free. By spread `W = r7 / r1`:

| region | status |
|---|---|
| `W <= 7` | [L] `ratio_lands`: first isolation instant `1/(8 r1)`, any arrangement (E566). |
| `7 < W <= 9` (band) | native `band_lonely` (existence, 105-cell cover, `LRC/Spec/BandCoverN.lean`); no landing statement. |
| `W > 9`, separated (slow core, fast block, ratio >= 9 across) | skeleton holes `ArrBlockRule8 f 9`, f = 1, 2 discharged, f = 3..6 OWED. |
| `W > 9`, every consecutive ratio < 9 | skeleton hole `ArrBoundedCovered8 9`, OWED (finite cover not built). |

## 2. Where our local families sit

* Near the AP an end subject has `x7 ~ 7 x1`: the AP lies ON the wall `W = 7` between the ratio region and the band. The AP landing law (chambers C1, C3, C5 and their larger-radius refinements, E567 to E575) is the local description of the band's lower edge. C1 is the ratio region; C3, C5 and the 39, 201, 379 leaf chambers are band chambers.
* The S2 and S3 covers (movers anywhere) sit mostly in the separated and wide regions: integer frozen core, free fast readings.
* The subject-moving family and S1 are slices through both.

## 3. Mechanisms that appear in every family (candidates for the general proof)

1. **Zone chain certificate.** Every landing is the upper end `(M + 1/8)/d` of a last zone, zones overlapping strictly, all readings clear there. With the laps `M` numeral, every inequality is linear in the parameters. One proof shape (`zone_lo`, `zone_hi`, `clear_at_end`) serves S1, the self-mover cells, the AP law, the 31 to 379 leaf chambers.
2. **Pairwise ratio walls.** Every chamber boundary found (E575: 62 split walls, up to 343 chain walls) involves exactly two readings and is `x_j / x_i = (8a +- 1)/(8b +- 1)`. The band cover contains the same walls (`9 (1 + x0) <= 7 (1 + x1)` is `9/7 = (8 + 1)/(8 - 1)`) [OBS, from reading `BandCoverN.lean`; not yet matched wall by wall]. The S2/S3 box edges `(n +- 1/8)/t*` are the same walls with one coordinate an integer (the frozen reading fixes the scale).
3. **The lonely classes of the AP are the units of Z/8.** Instants `c/8`, `c` odd; tight pair `{c^-1, -c^-1}`; two pairs `{1,7}`, `{3,5}` give two binary choices, hence three formulas with 0, 6, 11 moves (E567).
4. **Insertion lemma.** An interval of length `>= 1/(4 d)` contains a clear instant of a reading `d` (`opening_close`); of length `>= 1/d` for a pair (`two_clear_in2`); of length `>= 4/D` for three readings each `>= D` (`three_clear_in_all`, measure). All S2 and S3 covers are this lemma applied inside a piece of the frozen core, with box covers handling the small-d region.
5. **`Lands` is existence.** `Lands v k a` is equivalent to the subject being lonely; the content of each theorem is the explicit landing formula and its chamber, not the existence.

## 4. The general lemma that seems to be missing, and what it would give [ARITH]

**Core width lemma (CWL).** Let `k <= 6` readings have largest `c`. The native lonely runner theorems for `k + 1 <= 7` runners give a time `t*` at which every reading is at least `1/(k+1)` from an integer. Every reading changes by at most `c |t - t*|`, so all stay at least `1/8` away on `|t - t*| <= (1/(k+1) - 1/8)/c`. Hence a common clear interval of length at least `2 (1/(k+1) - 1/8)/c`:

| k | width * c_max (provable bound) | probe minimum over 4,000 random cores in (0, 2], c_max <= 30 c_min [OBS] |
|---|---|---|
| 1 | 0.750 | |
| 2 | 0.417 | 0.627 |
| 3 | 0.250 | 0.409 |
| 4 | 0.150 | 0.354 |
| 5 | 0.083 | 0.299 |
| 6 | 0.0357 | 0.219 |

Feeding the insertion lemma (fast readings each `>= D c_max`):

* f = 1 (core of 6): one reading needs width `>= 1/(4 d)`; `0.0357 >= 1/(4 D)` gives **D = 7**. This is exactly the ratio-seven threshold, and explains why `blockRule8_one` holds.
* f = 2 (core of 5): `two_clear_in2` needs width `>= 1/d`; `0.0833 >= 1/D` gives **D = 12** (the skeleton discharges f = 2 at 9 by a different route).
* f = 3 (core of 4): the measure bound needs width `>= 4/D`; `0.15 >= 4/D` gives **D = 26.7**.
* f >= 4: the measure bound fails (four blocked sets of density 1/4 can cover); a different argument is needed.

So with CWL, `ArrBlockRule8 3` is provable at `T = 27`, not 9, for arbitrary cores (not only AP cores). The threshold `T` is a parameter of the skeleton: raising it makes the separated side easier and the scale-free side larger (consecutive ratios < 27). The probe minima suggest the true constants are about twice the provable ones, which would bring f = 3 near `T = 11`.

## 5. What this review suggests doing next (ordered by leverage)

1. **Prove CWL in Lean** (native LRC orders 3 to 7 are already in `LonelyRunner/`; the interval step is two lines) and the insertion rules for f = 1, 2, 3 for arbitrary cores. This turns `ArrBlockRule8 1..3` into theorems at explicit `T` and tests how much of the skeleton it removes. Needs a bridge from the nested repo's order-k real-speed theorems to `Fresh` (or restating them there).
2. **Match the band cover to the wall arrangement**: extract the linear forms of the 105 cells of `BandCoverN.lean` and check they are walls `x_j / x_i = (8a +- 1)/(8b +- 1)`; compare with the AP-law chambers near `x7 = 7 x1`. If they coincide, the band cover is the AP-law chamber complex at its natural radius and the band gets a landing statement for free.
3. **Replace the fixed 3,000-leaf style covers by walls**: the S2/S3 box covers should be the pairwise-ratio arrangement restricted to the slice; generating them from the wall list would remove the ad hoc box search and give the leaf count directly.
4. **Four fast readings**: decide whether the exact covers close for f = 4 on AP cores (agent H is doing the three-mover remainder first).
5. **Do not over-read the local results**: they are slices through the reading space. They do not reduce the owed holes unless CWL-type general lemmas (item 1) or the wall-matching (item 2) turn them into statements about arbitrary cores or all chambers.
