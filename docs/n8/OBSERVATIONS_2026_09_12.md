# Observations — AP/grid mapping series

2026-09-12. n = 8, individual isolation. Record of what was observed. Method details in
`METHODS_AUDIT_2026_09_12.md`; all figures exact unless noted.

No conclusion is drawn. Items are stated with their evidence base.

---

## Definitions used

- **Grid**: 8 speeds whose reduced residues form a complete system mod 8. In coordinates
  `u_i = π(i) + 8 q_i`, `π` is the complete residue system and the shape is `q`.
- **Count**: number of maximal components of a runner's good set over one period.
- **Measure**: density of that good set. Defined for all speeds; count-per-period is not.
- **Spine**: the `φ(8) = 4` instants `t = p/(8g)`, `p` odd.
- **Reserve**: a runner's windows other than the spine.
- **`k`**: grid distance, `8 − #distinct residues mod 8` after reduction.
- **`S(t)`**: number of runners lonely at time `t`.

## Proved

1. A grid is globally isolated at exactly `φ(8) = 4` instants.
2. Those instants lie in every runner's good set simultaneously. A runner holds all four or
   none, since `8 | dp ⟺ 8 | d` for odd `p`.
3. The eighth-lattice is strictly nested: `t = k/8` requires `dk ≢ 0 mod 8`, so
   `k=4` (all `d` odd) ⟹ `k=2,6` (no `d ≡ 0 mod 4`) ⟹ `k` odd (no `d ≡ 0 mod 8`).
4. `max S = 8` ⟺ the configuration is a grid.
5. `max S ≥ (number of spine holders)`.
6. `k ≤ 6`. `k = 7` forces every difference `≡ 0 mod 8`, hence `8 | gcd`, contradicting
   primitivity.
7. With `m` distinct residues, a box `[0..N]` offers about `m(N/8+1)` slots, so small `m`
   forces large `N`.
8. Count 1 is impossible when any constraint is even (palindrome/parity).
9. Every component of `G_D` has length `≤ 3/(4·max D)`, hence `count ≥ (4·max D/3)·|G_D|`.

## Observed — grids

10. `base min = 4 + (fewest extras)`. Exhaustive over 6,305 grid shapes `q ∈ {0,1,2}⁸`, no
    exceptions.
11. Base-min distribution `{4:311, 6:1441, 8:2467, 10:1441, 12:532, 14:96, 16:15, 18:2}`;
    with `q ∈ {0..3}` it extends to 20. Never below 4.
12. Reserve profiles: tight AP `0,4,4,2,2,4,4,0`; alternating `8,12,8,2,2,8,12,8`;
    two clusters `6,14,12,8,8,12,14,6`; wide linear `10,14,10,14,12,10,18,10`.
13. Vulnerability to one move tracks base min: 80% of base-4 shapes reach 2, 76% at base 6,
    32% at 8, 16% at 10, 0% at 16 and 18.
14. For the 17 shapes with base min ≥ 16, the one-move floor is 4 or 6 and is identical at
    search spans 10, 25, 60 and 150. Two moves reach 2.
15. Every grid shape tested reaches 2 within two moves; near-tight grids need one.

## Observed — grid distance

16. Complete map:

    | `k` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
    |---|---|---|---|---|---|---|---|---|
    | min count | 4 | 2 | 2 | 2 | 2 | 4 | 8 | impossible |
    | `max S` | 8 | 6 | 4–6 | 3–6 | 4,6 | 4–6 | 4,6 | — |

17. `k = 1 ⟹ max S = 6`. At `k = 1` exactly one residue is doubled, so 6 runners hold the
    spine and `max S ≥ 6` follows from (5); the configuration is not a grid so `max S ≤ 7`
    follows from (4). **The observation is that 7 never occurs**: `max S = 6` in 1,792 configs
    `[0..14]`, 5,824 `[0..16]`, 14,688 `[0..18]`, and 600 random from `[0..59]` — 22,304 in
    total, including a wide sample outside the small-box regime.
18. `k = 6`: 1,320 constructed configurations, min count 8–26, zero spine holders in every one.
19. Min count by number of runners sharing a runner's residue mod 8, exhaustive `[0..24]`:

    | shares with | 0 others | 1 other | 2 others | 3 others |
    |---|---|---|---|---|
    | instances | 4,044,814 | 3,778,096 | 791,910 | 23,436 |
    | **min count** | 4 | **2** | 4 | **8** |

    After the dip at one collision the minimum climbs monotonically: 2, 4, 8. One collision is
    a strict minimum over the number of collisions. Earlier figures at `[0..16]` (5,988
    instances in the two-collision class) and `[0..20]` (127,890) agree.

## Observed — leaving the reference

20. A move removes the spine from exactly the runners it puts into residue collision.
21. Reserve across a move, for 3,657 runners that kept the spine: up 30.4%, unchanged 40.8%,
    down 28.8%; mean 5.84 → 5.87.
22. Of 5,136 floor-of-2 runners `[0..22]`, 2-power tower levels `{1:1474, 2:2056, 3:1404,
    4:202}`; zero at level 0. General population `[0..18]`: `{0:297396, 1:204556, 2:86408,
    3:15500, 4:364}`.
23. Moving a runner toward the centre of the pack costs more than moving it the same distance
    away — all 8 runners, no exceptions.
24. Holding the deviation multiset fixed and varying only which residue each attaches to swings
    the floor up to 4× (one multiset: 4 to 16 over 560 assignments). The worst assignment
    reaches count 4 in 13 of 14 multisets.

## Observed — scale and continuity

25. The measure is generic (≈ 0.1302) between rationals and jumps at every commensurate point:
    `1 → 0`, `4/3 → 0.1129`, `3/2 → 0.1136`, `9/5 → 0.1293`, `13/10 → 0.1326`, `5/4 → 0.1333`,
    `7/4 → 0.1420`. Sweep 1.300–1.310 gives 0.130192–0.130219.
26. The generic value is 0.1302, not `(3/4)⁷ = 0.13348`.
27. Near-collision: as the gap `ε` closes, cycle, largest reduced speed and count all grow like
    `1/ε` (count 300 at `ε = 1/100`); rate converges to 3.
28. Count at a varied speed `p/q` grows close to linearly in `q`: min count 8, 8, 9, 10, 19,
    19, 27, 43, 89, 131, 263 for `q` = 2, 3, 4, 5, 6, 8, 12, 20, 40, 60, 120.
29. From an integer grid base, non-integer positions are uniformly safer: min count by
    denominator 1, 2, 3, 4, 6, 8, 12, 24 is 2, 10, 12, 13, 25, 25, 37, 71.
30. A window is the intersection of a fixed `A`-component with a sliding bad interval: one
    endpoint fixed, the other sliding until it clamps at `A`'s boundary. At the AP the sliding
    interval clips each component to a single point.

## Observed — interaction

31. A grid has exactly one maximal simultaneously-lonely set, containing all eight runners.
    `k=0`: `(1 maximal set, largest 8)` in all 64 grids.
32. `k=1`: largest maximal set always 6; count varies 3–6. `k ≥ 2`: both vary.
33. Of 2,032 configs with `k ≥ 2` where `max S` exceeds the spine count, the max-S set is not a
    superset of the spine set in 1,760 (87%).
34. Example: `(0,1,2,3,4,5,8,13)` has spine `{2,3,4,5}` at `t = 1/8` and max-S coalition
    `{1,3,4,5,6,8}` at `t = 237/1664`.
35. After one move from the AP, the crashed runner appears as a maximal set by itself.
36. `S(t) = 0` occurs in every configuration examined.

## Observed — floors

37. No count below 2 was found in any population: 12,569,075 difference sets to span 38;
    exhaustive half-integer displacement at every `k = 1..8`; all grid shapes; non-grid bases;
    all transits both directions; annealed searches.

## Errors recorded

38. Nine retractions, all from experimental design rather than arithmetic: search boxes too
    small; a slice that could not reach the minimiser; a gcd changing with scale; random-sample
    minima read as box minima; windows printed in scaled time; patterns generalised from single
    examples. Listed in `METHODS_AUDIT_2026_09_12` §4.
39. Three-way method control: 0 disagreements between exact interval-merge, exact BSM and
    integer BSM over 495 sets; 0 BSM cell anomalies throughout.

## Open

40. The popcorn structure of the measure — jump magnitude as a function of denominator.
41. Window trajectories on paths where the varying constraint is not the largest, or where more
    than one constraint moves.
42. A measure-based statement of the floor. Every count result lives on reduced integer
    configurations and has no analogue at irrational speeds.
43. `k = 6` reached by construction, not enumeration; a second generator not yet run.

**n = 8 is not proved. Nothing above bounds any count below.**
