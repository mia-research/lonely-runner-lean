# Order seven native — working log v1

Band [1/7, 6/7], six positive speeds v1 < ... < v6, whole numbers, primitive (gcd 1). Target non-strict, so
isolated instants count. All counts below are float band-interval computations (EPS 1e-12) except where an exact
fraction is quoted; grade **EMPIRICAL** throughout. Nothing here is in Lean.

## E1 (2026-10-17) Phase 1: window types at 1/7, the map, exceptions, tight sets

**Window types ported** (`o7_map_v1.py`), classified by the fewest runners whose laps are tracked:
- **T4**: a 4-runner block window [L, U], the other two (a <= b) handled by the two-runner window,
  U - L >= 2/(7a) + 2/(7b).
- **T5**: a 5-runner block window, sixth runner (speed c) folded: c (U - L) >= 2/7.
- **T6**: a lap box (positive-length interval with all six in band).
- **TIGHT**: lonely only at isolated instants.

**Map** (`o7_map_v1_18.out`, `o7_map_v1_30.out`):

| range | sets | T4 | T5 | T6 | TIGHT |
|---|---|---|---|---|---|
| primitive <= 18 | 18,479 | 17,383 | 1,069 | 26 | 1 |
| primitive <= 30 | 588,559 | 582,712 | 5,810 | 36 | 1 |
| random, 3,000 sets <= 3000 | 3,000 | 3,000 | 0 | 0 | 0 |

At <= 30, 554,456 of the T4 sets use the handled pair (v5, v6). In the random sample all 3,000 use (v5, v6).
No set is "not lonely" in either range.

**Tight sets by our own search:** exactly one in each range, (1,2,3,4,5,6). Its exact lonely length is 0. The
instant is t = 1/7, where runner 1 is at the 1/7 edge and runner 6 at the 6/7 edge, because v6 = 6 v1
(`o7_exc_v4.out`). This is the same edge relation as the order-six tight set (1,2,3,4,5) at t = 1/6, with v5 = 5 v1.
Order six's second tight set (1,3,4,5,9) has no order-seven tight extension in <= 30.

**Exceptions (T5, T6), what is known per the standing rule.**

(i) *Feature.*
- Common factor in a prefix (`o7_exc_v3.out`). The exception rate is 10.1% when gcd(v1..v5) > 1 (5,429 sets),
  4.4% when only gcd(v1..v4) > 1 (15,095 sets), and 0.81% when both prefixes are coprime (568,035 sets).
  The normalised 4-prefixes of the g4 > 1 exceptions lead with (1,3,4,5) 225, (1,4,5,6) 104 and (1,2,3,4) 96.
  These are prefixes of the order-six tight sets, scaled.
- Arithmetic progressions (`o7_exc_v5.out`). The share of sets whose longest AP has at least 4 terms is:

  | class | sets with a 4+ term AP |
  |---|---|
  | T4 | 6.6% |
  | T5 | 19.2% |
  | T6 | 80.6% (29/36) |
  | TIGHT | 1/1 (a 6-term AP) |

  Examples of the runs: (4,5,6,7), (6,7,8,9), (9,10,11,12), (12,13,14,15), 2(1,2,3,4,5), 3(1,2,3,4,5).
- Feature split (`o7_exc_v2.out`), where slow means v2 large against v1. T5: slow 3,506, other 2,304.
  T6: slow 9, other 27. The cluster feature carries none.

(ii) *What forces the witness* (`o7_exc_v4.out`).
- T5: the folded runner is v6 in 5,402 of 5,810 sets, then v5 282, v4 105, v3 21. Sets closed by exactly one
  5-block: 513.
- T6: every one of the 36 longest lonely intervals is pinched between two band edges: one runner's 1/7 edge
  (entering) at L and a different runner's 6/7 edge (leaving) at U. The exact lengths run from 3/539 to 1/42.
  So each T6 witness is a positive neighbourhood of a two-edge instant, not a long window.

(iii) *Same mechanism as order six?*
- TIGHT: yes, by the edge relation v6 = 6 v1 shown above.
- T6 with a 4+ term AP (29 sets): **not understood.** The AP run is the observed feature. No artifact yet shows
  that the run forces the pinch.
- T6 with longest AP 3 (7 sets): **not understood.**
- T5: **not understood** beyond the folded-runner distribution.

**Consequence:** the order-seven exceptions concentrate on AP runs and on scaled order-six tight prefixes. Phase 2
should test whether an AP run of length 4 or more forces the two-edge pinch: derive the instant from the run,
then check it on all 36 T6 sets.

Scripts: `o7_map_v1.py`, `o7_exc_v1.py` .. `o7_exc_v5.py`, `o7_prefix_v1.py`. The 4-prefix criterion W4 v4 >= 4/7
(`o7_prefix_v1.out`) leaves 41,281 of 455,041 prefixes short at every ratio, so it does not separate the exceptions.
