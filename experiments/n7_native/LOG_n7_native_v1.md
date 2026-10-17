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

## E2 (2026-10-17) Phase 1 extended: map to 60, tight search to 70

`o7_map_v2.py` uses the same window types as `o7_map_v1.py`, run in parallel over (v1, v2). It computes exact
fractions for every T6 and TIGHT set. It reproduces the <= 30 counts of E1 exactly (`o7_map_v2_30.out`).

| range | sets | T4 | T5 | T5 share | T6 | TIGHT | not lonely |
|---|---|---|---|---|---|---|---|
| <= 30 | 588,559 | 582,712 | 5,810 | 0.99% | 36 | 1 | 0 |
| <= 40 | 3,797,877 | 3,785,588 | 12,249 | 0.32% | 39 | 1 | 0 |
| <= 50 | 15,705,403 | 15,684,107 | 21,254 | 0.14% | 41 | 1 | 0 |
| <= 60 | 49,430,584 | 49,397,778 | 32,764 | 0.066% | 41 | 1 | 0 |

**Tight search** (`o7_tight_v2_70.out`): 129,389,133 primitive sets <= 70 were searched. The only tight set is
(1,2,3,4,5,6), with exact longest length 0. No set is not lonely.

**T6 above 30.** Five new sets appear, all at most 47. Nothing new appears between 50 and 60.

| set | exact longest length | longest AP | relation to the <= 30 families |
|---|---|---|---|
| (2,8,10,12,14,31) | 3/392 | 4 | 2(1,4,5,6,7) prefix |
| (2,12,14,16,18,35) | 1/126 | 4 | 2(1,6,7,8,9) prefix |
| (3,12,15,18,21,46) | 1/196 | 4 | 3(1,4,5,6,7) prefix |
| (3,12,15,18,21,47) | 1/196 | 4 | 3(1,4,5,6,7) prefix |
| (4,12,16,20,29,31) | 25/3248 | 3 | 4(1,3,4,5) prefix |

Each one is a scaled order-six-type prefix plus one or two free speeds. That is the g4 > 1 / g5 > 1 feature of E1.
At <= 60 the 41 T6 sets split as coprime prefixes 23, g4 > 1 6, g5 > 1 12. Their longest-AP split is 3: 8,
4: 26, 5: 7, the same as at <= 50.

**T5 at <= 60.**
- Folded runner: v6 31,077, v5 1,186, v4 437, v3 64.
- Prefix gcd: coprime 19,148, g4 > 1 5,408, g5 > 1 8,208.
- The T5 share falls about 15-fold from 30 to 60. The T6 count is flat from 50 to 60.

**Consequence:** in these ranges the T6 exceptions are a finite list of 41 sets with v6 <= 47 (EMPIRICAL to 60).
The T5 exceptions keep growing in count and fall in share. Phase 2 targets are:
- (a) a closed form for the 41 T6 sets as two-edge pinches (E1 (ii));
- (b) the T5 sets as a 5-block with the fastest runner folded, which needs a region description, not a list.

The single tight set holds to 70.

## E3 (2026-10-17) Phase 2: pinch closed form for the 41 T6 sets; the T5 region with v6 folded

**Map:** order seven, exception class T6 (lap box only) and class T5 with v6 folded, from E1–E2.

### Pinch instants (closed form)

A **pinch** is an entering edge (speed a, lap m) and a leaving edge (speed b, lap m'):

- L = (7m+1)/(7a)
- U = (7m'+6)/(7b)
- delta = (7m'+6) a - (7m+1) b > 0
- U - L = delta/(7ab)

Scaling all speeds by c maps the interval [L, U] to [L, U]/c, shifted by k/c for k in 0..c-1. So the invariant is
the normalised pinch (a/g, m, b/g, m') with g = gcd(a, b); laps are reduced by a common period.

Admissible speeds:
- A speed x is in band throughout [L, U] iff, with n = floor(xL), we have xL - n >= 1/7 and xU <= n + 6/7.
- Since x(U - L) <= 5/7, every admissible speed satisfies x <= 5ab/delta, so each pinch's admissible list is finite.

Results (`o7_pinch_v1.out`, `o7_pinch_v2.out`, `o7_pinch_v3.out`):
- The 41 T6 sets (<= 60) fall into **20 normalised pinches**, or **17 up to time reversal**.
  - Reversal t -> -t swaps the 1/7 and 6/7 edges: (a, m, b, m') -> (b, b-1-m', a, a-1-m).
  - The reversal pairs present are (1,0,5,0)~(5,4,1,0), (2,1,3,1)~(3,1,2,0) and (4,2,7,3)~(7,3,4,1).
- Largest classes:

  | pinch | delta | interval | sets |
  |---|---|---|---|
  | (7,3,4,1) | 3 | [22/49, 13/28] | 9 |
  | (4,2,7,3) | 3 | [15/28, 27/49] | 5 |
  | (1,0,5,0) | 1 | [1/7, 6/35] | 4 |
  | (2,1,3,1) | 2 | [4/7, 13/21] | 3 |
  | (3,1,2,0) | 2 | [8/21, 3/7] | 3 |

  The other 15 pinches hold one or two sets each. Delta ranges over 1..34.
- Certificate check, exact fractions: all 41 sets are in band on their pinch interval at some shift (41/41).
  `[VERIFIED-INSTANCE]` for these 41 sets.
- **Consequence:** every T6 set is lonely at the instant t* = (7M+1)/(7 v_i), where v_i is the entering runner at
  lap M. One runner sits exactly at 1/7 there. The instant has the form K/(7P) with K ≡ 1 (mod 7) and P a speed of
  the set. It is reached here by the edge construction, not by a 7-adic argument.

### T5 region with v6 folded

Folding v6 at the 5-prefix window: with W5(P) the longest window where all of P = (v1..v5) are in band at 1/7, any
v6 >= 2/(7 W5(P)) closes the set, because runner 6 sweeps an arc of length >= 2/7, which meets the closed band.
W5 scales as 1/c, so the scale-free form is:

- kappa(P) = v5 W5(P), which lies in (0, 5/7];
- the T5 region is v6/v5 >= rho(P) = 2/(7 kappa(P)).

W5(P) > 0 for every P by native order six: the band [1/6, 5/6] lies inside [1/7, 6/7], and an order-six tight
point at 1/6 is interior at 1/7.

Results (`o7_t5_v1_30.out`, `o7_t5_v1_60.out`, `o7_t5_v2.out`):
- Over the 5,302,911 primitive 5-prefixes <= 60, **min kappa = 3/28**, so rho <= 8/3. It is attained only at
  (1,3,4,5,7) and (1,4,5,6,7). The minimum is the same at <= 30. The value is exact; the search is float.
- Exactly **9 prefixes have kappa < 5/28**, identical at <= 30 and <= 60 (exact values):

  | prefix | kappa | rho |
  |---|---|---|
  | (1,3,4,5,7), (1,4,5,6,7) | 3/28 | 8/3 |
  | (1,2,3,4,5), (1,2,4,5,6), (1,6,7,8,9) | 1/7 | 2 |
  | (1,4,10,11,12) | 12/77 | 11/6 |
  | (1,7,8,9,11), (2,7,8,9,11) | 33/196 | 56/33 |
  | (1,10,11,12,13) | 6/35 | 5/3 |

- The level 5/28 is attained by a large class: v5 W(1,3,4,5) = 5 · 1/28, the 4-prefix of order six's tight set
  (1,3,4,5,9). It recurs in its scalings, for example (1,3,9,12,15), (1,4,12,16,20) and (4,5,15,20,25), and also in
  (1,6,8,9,10) and (1,12,13,14,15).

Grades:
- **EMPIRICAL (5-prefixes <= 60):** v6 >= (8/3) v5 closes every order-seven set by the v6 fold. Outside the 9
  prefixes, v6 >= (8/5) v5 suffices.
- **Not proved:** a lower bound kappa(P) >= 3/28 for all P. It is the quantitative statement that phase 3 would
  need, an order-six-type window bound at 1/7.

**Consequence:** order seven reduces, through the v6 fold, to the bounded-ratio region v5 < v6 < rho(P) v5 together
with a bound on kappa. The T6 exceptions are explicit edge-instant certificates.

Still not understood:
- why these 17 pinch classes and not others: the T4/T5 failure at those sets has no derived explanation;
- whether the T6 list is finite beyond 60.

## E4 (2026-10-17) Phase 3a: kappa lower bound — 1/21 proved; 3/28 needs a certificate

**Map:** order seven, the v6-fold region of E3; target kappa(P) = v5 W5(P) >= 3/28 for all integer 5-prefixes.

**Proved (Lean, nested repo 89b3faa, `LRC/Spec/OrderSevenKappaN.lean`):**
- `LRC.O7Kappa.window_of_six`: at most five positive whole numbers bounded by V are all at distance >= 1/7 on a closed
  interval of half-width 1/(42V).
- `LRC.O7Kappa.kappa_ge`: as an interval [L, L + 1/(21V)].
- Proof: the native order-six instant (`lonely_six_nat`, distance >= 1/6), plus `circDist_lipschitz`. Each reading
  moves at most V/(42V) = 1/42.
- `#print axioms` for both: [propext, Classical.choice, Quot.sound]. Checked with `lake env lean` on the file. The
  module is not yet imported by a build target.

**Consequence `[PROVED]`:** kappa >= 1/21 for every 5-prefix, so v6 >= 6 v5 closes every order-seven set by the v6
fold (E3). The T5 fold step itself is not yet in Lean.

**Why elementary lemmas stop short of 3/28** (`o7_kappa_chain_v1_40.out`):
- Chain bound: take a block B of k runners; native order k+1 gives a margin of 1/(k+1); fold the rest in worst case
  with f(l) = clip((l - 2/7)/2, 0, 5/7).
- This reaches 3/28 on only 38,771 of 641,166 primitive prefixes <= 40 (6.05%).
- The rest concentrate at small v5/v4 (358,448 in the bin [1, 1.25)). Every run of five consecutive integers sits
  at 1/21.
- So worst-case folding loses the structure that gives the true windows (3/28 and above).

**Real-ratio landscape** (`o7_kappa_real_v1.out`, `o7_kappa_real_v2.out`):
- Random real tuples (v5 = 1, ratios in (0.02, 1), 4,000 each) have min kappa 0.282 at T = 20, 0.354 at T = 100
  and 0.443 at T = 400. None fall below 3/28.
- Real perturbations of the minimisers (1,3,4,5,7), (1,4,5,6,7) and (1,2,3,4,5) at relative sizes 1e-2, 3e-3 and
  1e-3 (400 each) gave min kappa >= 0.130. None fall below 3/28.
- So small kappa sits at rational points: the 9 prefixes of E3, plus one-parameter families whose 4-subset is a
  scaled low point. For example c(1,3,4,5) with v5 = 5c forces kappa <= 5 W(1,3,4,5) = 5/28 whatever the fifth speed.

**What a 3/28 proof needs** (design, same pattern as §5/§6 of order six):
- A box tree over the ratios x_i = v_i/v5 in (0, 1)^4.
- Window leaves: an explicit lap box [L, U] in units 1/v5 with laps n_i, valid on the box through term-wise linear
  bounds (the `tlo`/`pairOK` pattern), with T <= 20 enough for generic boxes.
- The 9 rational points and the 4-subset families: kappa equals 3/28 exactly at two of the points. A real box around
  them loses the pinch window linearly, and the recovering windows appear only after time ~1/epsilon. This is the
  tight-point situation of order six §5: integer-exact handling, or a 2D-orbit / resonant-direction treatment as in
  §6.
- Relaxed alternative: a target kappa0 < 3/28 (for example 1/10, so rho = 20/7) leaves slack 1/140 at every low
  point. Then fixed neighbourhoods with bounded-time windows suffice and no tight-point work is needed. The bounded
  region becomes v5 < v6 < (20/7) v5 instead of (8/3) v5.

**Not understood:** why the minimum is 3/28, attained at (1,3,4,5,7) and (1,4,5,6,7). The exact window structure
at those two points has not been derived.

## E5 (2026-10-17) Phase 3a: box-tree prototypes for kappa >= 1/10 and kappa >= 3/28, compared

**Map:** order seven, the kappa bound of E4; prototype certificates over real ratios x_i = v_i/v5.

**Leaf** (`o7_kbox_v1.py`, `o7_kbox_v2.py`):
- A lap box [L, L + K] in time units 1/v5, L <= T, with laps n_i.
- On the ratio box [a_i, b_i], it needs a_i L >= n_i + 1/7 and b_i (L + K) <= n_i + 6/7. These are the term-wise
  linear bounds, the same shape as the order-six `tlo` leaves.
- Otherwise split the widest coordinate. Boxes with no increasing x are dropped.
- v2 splits at a point k/7 when one lies inside the box, which puts the minimisers on box faces.

**Results** (float, `o7_kbox_v1_K110.out`, `o7_kbox_v1_K328.out`, `o7_kbox_v2.out`, `o7_kbox_v2_slow.out`):

| x1 slice | T | K = 1/10 leaves | K = 3/28 leaves | failures |
|---|---|---|---|---|
| [0.2, 0.3] | 40 | 40 | 40 | 0 / 0 |
| [0.1, 0.2] | 40 | 8,777 | 9,895 | 0 / 0 |
| [0.05, 0.1] | 40 | 25,045 | 26,270 | 0 / 0 |
| [0.02, 0.05] | 200 | 120,934 | 126,330 | 0 / 0 |
| [0.01, 0.02] | 200 | 633,369 | 653,105 | 0 / 0 |

- Above x1 = 2/7 one leaf per slice suffices: at tau ~ 1/2 every ratio in [0.3, 1] reads inside [1/7, 6/7].
- **v1 midpoint splitting for 3/28** failed in 193 boxes, all within about 0.01 of (1,3,4,5)/7 and (1,4,5,6)/7.
  **Sevenths splitting removes every failure.** At a minimiser the window that reaches 3/28 has zero margin, and
  the windows differ on each side of the face, so kappa is a V-shaped minimum there and both one-sided leaves hold
  on the face.
- Exact rational check (`o7_kbox_exact_v1.out`): the 3/28 tree with sevenths splitting on x1 in [1/10, 1/5],
  which contains both minimisers, closes with 9,981 leaves and 0 failures. `[VERIFIED-INSTANCE]` for that slice and
  that leaf rule, not yet in Lean.

**Comparison.**
- **3/28 costs 1–13% more leaves than 1/10 on every slice, and needs no tight-point treatment.** The minimisers
  are handled by face placement.
- 3/28 gives rho = 8/3. 1/10 gives rho = 20/7.
- On this evidence 3/28 is the better target.

**Shared obstacle, independent of K:** the slow region x1 -> 0.
- Leaves grow from about 1.2e5 on [0.02, 0.05] to about 6.3e5 on [0.01, 0.02], and x1 = v1/v5 >= 1/v5 is not
  bounded below.
- A box tree cannot close x1 near 0. It needs a slow-runner lemma: for x1 <= epsilon, the fast four (v2..v5) need a
  K-window inside a band stretch of runner 1, of length 5/(7 x1) in tau.
- That statement is about where the fast four's windows fall, not about their existence. The analogue in order six
  is §5 small alpha (IVT box lemma, step lemma, strip).
- **Not understood / open:** the form of that lemma at 1/7.

## E6 (2026-10-17) Exact re-check of E1–E5

Owner: *"You can use float, but you need to know that any result has to them be double checked with exact before its
committ3ed"*. E1–E5 were committed with float classification and float box trees, so those counts were float-only.
They are re-checked here in exact arithmetic. `o7_exact.py` scales time by 7 lcm(S), so every band edge is an
integer and the T4/T5 thresholds are integer comparisons.

| entry | float result | exact re-check | artifact |
|---|---|---|---|
| E1/E2 map <= 30, 40, 50, 60 | counts, patterns, T6 list | **identical line for line** (all but the elapsed time) | `o7_map_v3.py`, `o7_map_v3_{30,40,50,60}.out` |
| E2 tight search <= 70 | only (1,2,3,4,5,6); 0 not lonely | **identical** | `o7_tight_v3_70.out` |
| E3 kappa over 5-prefixes <= 30, 60 | min 3/28; 9 below 5/28 | **identical**: min 3/28 at (1,3,4,5,7); the same 9 prefixes with exact kappa; 57 (<= 30) and 227 (<= 60) at exactly 5/28 | `o7_t5_v3.py`, `o7_t5_v3_{30,60}.out` |
| E3 pinch data | already exact Fractions | input list now exact (identical) | `o7_pinch_v1..v3` |
| E4 chain bound <= 40 | 38,771 / 641,166 | **identical** (formula-only Fractions) | `o7_split_an_v1_40.out` |
| E4 real-ratio landscape | floats | rational inputs, exact W: none below 3/28; perturbation minima 0.137–0.204 at 1e-3; random min 0.305 (T = 20), 0.477 (T = 100) | `o7_kappa_real_v3.py/.out` |
| E5 box trees | float leaves | superseded by the exact trees of E8 (0 failures) | `o7_kbox_exact_v2.py` |

No float result changed. The float scripts stay on disk as search tools, and every number cited from E7 on names an
exact artifact.

## E7 (2026-10-17) Slow-runner lemma: components proved, observation exact

**Map:** order seven, kappa for small x1 = v1/v5; order-six analogue §5 small alpha (`ivt_box`).

**Proved (Lean, `LRC/Spec/OrderSevenSplitN.lean`, namespace `LRC.O7Split`):**
- `split_fold`: a window of S of length >= G plus `GapProp F G w` give a window of length w for S ∪ F.
  `GapProp F G w` means every time interval of length G contains a window of length w for F.
- `gap_empty`.
- `gap_stretch` (stretch recursion): from `GapProp F G w` with G <= 5/(7u), get
  `GapProp (insert u F) (2/(7u) + 2G) w`.
- `ivt_window`: the intermediate-value window with a margin.
- `cluster_window`: for speeds b + e_d with offsets 0 <= e_d <= c and fixed laps, an envelope gap >= (b + c) w on
  [alpha, alpha + 1/b] gives a window of length w starting there. This is order six's `ivt_box`, with a window in
  place of an instant.

**Observation (exact):**
- Slow lemma alone (j = 1: runner 1's band stretch must contain a full G-interval of the fast four)
  (`o7_slow_v1_{30,40}.out`):
  - closes 77.48% of primitive prefixes <= 30 and 75.31% <= 40;
  - sup h = v2 G(Q) grows along consecutive runs: 6.23 at (27,28,29,30), 8.21 at (35,36,37,38);
  - G itself stays near 0.23 on those runs.
- Split fold with exact per-block gaps, every split j (`o7_split_v1_{30,40}.out`):
  - closes 99.84% (<= 30) and 99.91% (<= 40);
  - the smallest v1/v5 not closed is 3/23 (<= 30) and 3/31 (<= 40); 3/31 is (3,9,12,15,31), the family
    3(1,3,4,5) + X;
  - probes (`o7_split_probe_v1.out`): (v1, n..n+3) and (a, b, n, n+d, n+2d) up to n = 200 are all closed.
- Provable split chain: native-order windows, single-runner gap and stretch recursion, formula-only.
  - It closes 6.05% (<= 40) and 6.60% (<= 60) (`o7_split_an_v1_{40,60}.out`).
  - On 200,000 random primitive prefixes with v5 > 100 v1 it closes 32.03% (`o7_slow_sample_v1.out`).
  - The prefixes it leaves open have fast blocks with consecutive ratios below about 1.5. The stretch recursion
    needs G(inner) <= 5/(7u), which fails there.

**Reading:**
- Every ingredient the split fold uses has a proof except uniform gap bounds for fast blocks of three or four
  runners with bounded internal ratios.
- `cluster_window` reduces a cluster block to its offset pattern. Bounding the offset patterns uniformly is the
  open piece.
- A measure (union) bound fails for 3+ runners at w = 3/(28 v5): the bad fraction 6/7 + sum v_k w can exceed 1.
- The cluster-coverage run (`o7_split_an_v2.py`) was stopped: its lap-vector enumeration is too slow. It is owed in
  a faster form.

**Consequence:** kappa >= 3/28 in the slow region is not needed for the fold.
- kappa >= 1/21 holds for all prefixes (E4, proved).
- So v6 >= 6 v5 closes order seven everywhere (E8, `lonely7_of_fast6`), and v6 >= (8/3) v5 closes it wherever the
  3/28 tree holds.
- The slow region then sits in the bounded-ratio problem v5 < v6 < 6 v5, which needs the six-runner slow-runner
  lemma anyway. The components above are stated for arbitrary blocks and carry over.

## E8 (2026-10-17) Lean: kappa >= 3/28 on v5 <= 100 v1, and the fastest-runner fold

**Map:** order seven, the v6 fold (E3) and the kappa bound (E4–E5); tree in place of float prototypes.

**Exact trees** (`o7_kbox_exact_v2.py`): one root box x_i in [X, 1], sevenths splitting, exact rationals, 0 failures.

| X | leaves | empty | trees file |
|---|---|---|---|
| 1/4 | 1 | 0 | `o7_tree_q4.txt` |
| 1/8 | 979 | 44 | `o7_tree_q8.txt` |
| 1/12 | 1,349 | 60 | `o7_tree_q12.txt` |
| 1/16 | 1,946 | 94 | `o7_tree_q16.txt` |
| 1/20 | 3,144 | 156 | `o7_tree_q20.txt` |
| 1/50 | 12,342 | 573 | `o7_tree_q50.txt` |
| 1/100 | 48,900 | 1,672 | `o7_tree_q100.txt` |

Using one root box instead of 40 slices cuts the tree by about a factor of 10 against E5.

**Proved (nested repo d26e49b; `#print axioms` = [propext, Classical.choice, Quot.sound] for every theorem listed,
`o7_lean_axioms_v1.out`; no `sorry` / `native_decide` / `admit` in the new modules):**
- `LRC/Spec/OrderSevenKappaTreeCoreN.lean` (`LRC.O7KTree`):
  - the checker `check` (leaf, empty and split rules mirror the generator);
  - `check_sound`;
  - split trees: skeleton `TS`, `boxesOf_cover`, `skelOK` and `split_sound`;
  - `kappa_of_win`, which turns the window on ratio boxes into `InBandOn {v1..v5}` on an interval of length
    3/(28 v5).
- `OrderSevenKappaTree100P0N` … `P23N`: 24 parts, each a single `decide +kernel`. Generator:
  `o7_kbox_lean_v2.py`, MAXLEAVES 3000.
- `OrderSevenKappaTree100N`: `skel_ok` (`decide +kernel`), `all_ok`, `win`, and `LRC.O7KTree100.kappa`: kappa >= 3/28
  whenever v5 <= 100 v1.
- `OrderSevenFoldN` (`LRC.O7Fold`):
  - `fold_one`;
  - `lonely7_of_window`;
  - `lonely7_of_fast6`: **v6 >= 6 v5 closes order seven, any v1 < … < v5**;
  - `lonely7_of_kappa`.
- `OrderSevenFold100N`: `lonely7_fold100`: **8 v5 <= 3 v6 and v5 <= 100 v1 close order seven.**
- `OrderSevenSplitN` (E7): `split_fold`, `gap_stretch`, `ivt_window`, `cluster_window`.

**Build note:** a plain `lake build` of the 24 parts ran ten Lean processes at once and thrashed (80 MB free,
2% CPU each). Built three at a time instead (`xargs -P 3`): 4 min 8 s in total, 23 s per part, assembly 6 s.

**Consequence `[PROVED]`:** in order seven, the region left for other mechanisms is v5 < v6 < 6 v5 when
v5 > 100 v1, and v5 < v6 < (8/3) v5 when v5 <= 100 v1.

**Owed:**
- the bounded-ratio region (a five-dimensional problem);
- uniform gap bounds for three- and four-runner fast blocks with bounded internal ratios (E7), which the six-runner
  slow-runner lemma also needs.

## E9 (2026-10-17) Gap bounds for three- and four-runner blocks

**Map:** order seven, slow-runner lemma (E7). Gap = `GapProp F G w` of `LRC.O7Split`.

**Three runners: uniform, any real speeds (instant version, w = 0)** — `[PROVED]`
- `LRC.O7Gap3.gap_three` (`OrderSevenGapThreeN.lean`): for at most three positive speeds,
  `GapProp F (5 Σ 1/d) 0` holds.
- Proof by union bound (measure): each speed is out of band on at most dG + 2 open intervals of length 2/(7d).
  Over three speeds the total is <= 6G/7 + (4/35)G < G.
- Four speeds would need 8/7 < 1, so the argument stops at three.
- With a window w > 0, the same count needs w Σ d < 1/7. At the kappa window w = 3/(28 v5) this fails (up to 9/28),
  so kappa gets nothing from it.

**Four runners: no uniform bound exists** (exact, E7 data):
- h = v2 G(Q) grows along consecutive runs: 6.23 at (27,28,29,30), 8.21 at (35,36,37,38). G stays near 0.23 there.
- The gap of a cluster is set by its offsets (beat period ~ 1/offset), not by its speeds.

**Pattern window `[PROVED]`:** `LRC.O7Split.pattern_window` generalises `cluster_window` to speeds d = c Q_d + e_d
(Q an integer pattern, c real, 0 <= e_d <= kappa Q_d). This covers near-resonant blocks such as (2c, 3c+1, …) as
well as clusters.

**Joint closure, observation** (`o7_joint_v1.py`, `o7_joint_v2.py`; float search, **every closure re-verified
exactly**; `o7_joint_v1_s1.out`, `o7_joint_v2.out`):
- The pattern window combined with the slow block's band, at one time alpha (all conditions linear in t, checked at
  both ends) closes:
  - 300/300 random six-runner sets with v5 > 100 v1, v6 < 6 v5;
  - 1,187/1,187 structured ones: runs (v1, n..n+4d), scaled order-six tight patterns c(1,2,3,4,5)+o and
    c(1,3,4,5,9)+o, two clusters, random sets with v1 up to 60.
- The j = 1 split closes almost all of them (293/300).
- The joint closure is **existential in one time alpha**, unlike the split fold, which needs a universal gap. So a
  box tree over the slow ratios (S together with the offsets e) can in principle certify it.

**Provable split mechanisms on the six-runner slow region** (`o7_slow6_an_v1.out`, exact, formula-only):
- Native windows for S; gaps for F from single runner, stretch recursion, `gap_three`, and block recursion.
- Coverage: 6,912 of 20,000 random sets (34.56%).
- Every unclosed set has its largest consecutive ratio at j = 1: a slow v1 followed by a five-runner block with
  bounded internal ratios.

**Reading:** the slow region needs time-localised order six — a lonely instant of a bounded-ratio five-runner block
inside each band stretch of the slow block. It holds per instance (joint closure). No uniform argument exists here
yet. A union bound cannot give it (10/7 > 1), and a gap bound cannot either (clusters).

## E10 (2026-10-17) Bounded-ratio region: six-runner box tree, kernel-checked for v6 <= 12 v1

**Map:** order seven, bounded region (complement of the fold, `lonely7_of_fast6`).

**Exact prototype** (`o7_box6_v1.py`; ratios x_i = v_i/v6, x5 >= 1/6; leaves are single instants tau with laps; splits at
the point k/42 nearest the midpoint):

| x1 >= | leaves | empty | failures | file |
|---|---|---|---|---|
| 1/4 | 1 | 0 | 0 | `o7_box6_v1_q4.out` |
| 1/8 | 2,243 | 129 | 0 | `o7_box6_v1_q8.out` |
| 1/12 | 7,096 | 476 | 0 | `o7_box6_v1_q12.out` |
| 1/20 | 22,564 | 1,278 | 0 | `o7_box6_v1_q20.out` |
| 1/50 | 190,117 | 8,263 | 0 | `o7_box6_v1_q50.out` |

- No failures anywhere, the tight set (1,2,3,4,5,6) included: with k/42 splitting, (1,2,3,4,5)/6 lies on box faces,
  and each side has its own instant. The T6 pinch sets need no special leaves.
- Leaf count grows roughly like x1^-2.3.

**Proved (nested repo f0b3341; axioms [propext, Classical.choice, Quot.sound], `o7_lean_axioms_v2.out`):**
- `OrderSevenBox6CoreN` (`LRC.O7Box6`):
  - checker, `check_sound`, split trees, `lonely_of_inst`;
  - split nodes carry their split value p/q, and the kernel checks only that the halves cover the box.
- `OrderSevenBox6Tree12P0..2N` and `OrderSevenBox6Tree12N`: 7,096 leaves, `LRC.O7Box6T12.lonely`.
- `OrderSevenSpreadN`: **`LRC.O7Spread.lonely7_spread12`: order seven holds whenever v6 <= 12 v1** (fold for
  v6 >= 6 v5, tree otherwise).

**Build note:** the first encoding recomputed the k/42 split point in the kernel (41 candidates per split). A part
was still unfinished after more than 15 minutes, with swap at 12 GB. Storing the split value (`o7_box6_exact_v3.py`,
`o7_box6_lean_v2.py`) brought a part down to 18 s.

## E11 (2026-10-17) Order seven for v6 <= 50 v1, kernel-checked

- Tree: `o7_box6_exact_v3.py 1 50 1 6 300` gives 190,117 leaves and 8,263 empty boxes, exact, 0 failures, in 655 s.
- Split into 96 parts by `o7_box6_lean_v2.py`, MAXLEAVES 3000. Built three at a time, about 10 minutes.
- `LRC.O7Box6T50.lonely` and **`LRC.O7Spread.lonely7_spread50`: order seven holds whenever v6 <= 50 v1**.
  Axioms [propext, Classical.choice, Quot.sound] (`o7_lean_axioms_v2.out`). Nested repo commit after f0b3341.

**Where order seven stands (proved):**
- every set with v6 <= 50 v1;
- every set with v6 >= 6 v5;
- every set with 3 v6 >= 8 v5 and v5 <= 100 v1.

**Open:** v6 > 50 v1 with v6 < 6 v5. There is always a slow runner block followed by a faster block. It needs the
time-localised order-six statement of E9. That statement holds per instance by the joint pattern closure; no
uniform argument exists yet.

The tree boundary moves at a cost of roughly x1^-2.3 leaves, so 1/100 means about 1M leaves (about 330 parts). The
slow region itself has no lower bound on x1, so trees alone do not finish it.

## E12 (2026-10-17) Toward a uniform slow-region argument: what the closures use; first-stretch localisation

> **DRIFT (marked 2026-10-17, owner):** this entry follows an imported proof shape, not global isolation. Its targets (first-stretch localisation FS50/FS100 — a `DoorFirstLap`-type cap, set aside at n=6 E19/E20/E26–E27; Fourier/equidistribution; the "Diophantine dichotomy"; measure union bounds — set aside as imported framing, n=6 E2) are **not native routes**. True theorems proved here stay true; the direction is withdrawn. See E17.

**Map:** order seven, slow region v6 > 50 v1, v6 < 6 v5 (E11 open item).

**What the per-instance closures use** (`o7_joint_mine_v1.py`, 80 random slow-region sets, split j = 1; float search,
every closure verified exactly; `o7_joint_mine_v1.out`):

| restriction | closed |
|---|---|
| R0: 4 best patterns with q1 <= 12, any runner-1 stretch | 80/80 |
| R1: first stretch only | 80/80 |
| R2: pattern q1 = 1 only, Q = round(F/v2) | 80/80 |
| **R3: q1 = 1 and first stretch** | **80/80** |
| R4: pure cluster form Q = (1,1,1,1,1) | 5/80 |

- Every R0 closure lies in runner 1's first band stretch.
- The offsets are not small: sigma = e_max/c is 0.1–0.6, so the closure is not a slow-offset argument.

**Claim R (exact, `o7_claimR_v1.out`, `o7_claimR_v2_30.out`):** a five-runner block F has a lonely instant (1/7) in
[1/(7 v1), 6/(7 v1)].
- 0 failures on 24,000 random bounded-ratio blocks with v2/v1 in {2, …, 50}, 1,155 runs and 2,137 scaled tight
  patterns.
- Real (rational) speeds w = F/v1 with theta in [1/7, 6/7]: 0 failures on 6,400 random tuples and 3,200 resonant ones
  (c Q + offsets), min w from 1.5 to 1,000.
- So integrality is not what makes it true.

**First-stretch property, exhaustive and exact** (`o7_firststretch_v1.py`, `o7_firststretch_v2.py`): is every primitive
six-set lonely in [1/(7 v1), 6/(7 v1)]?
- <= 30: yes, all 588,559.
- <= 45: one failure, (7,19,26,32,35,43).
- <= 60: 11 failures out of 49,430,584. **Every failure has v2/v1 in [2.56, 2.89] and v6/v1 in [6.1, 7.0]**, so all of
  them lie inside the proved region v6 <= 12 v1 (`lonely7_spread12`).
- The latest first lonely position is exactly 6/7 of runner 1's lap, at (6,16,22,27,30,37).
- Caution, not imported: in the n=8 project a first-lap localisation (`DoorFirstLap`) was refuted, so localisation
  is not automatic across orders.

**Uniform target `[CONJECTURE — EMPIRICAL: exhaustive to 60, real-speed samples]`:**
- **FS(spread > 7):** for real speeds 1 = w0 < w1 < … < w5 with w5 > 7, some theta in [1/7, 6/7] has every w_k theta in
  band.
- Combined with `lonely7_spread50` (v6 <= 50 v1), FS(spread > 50) would finish order seven.
- Its time domain is compact. Only w -> infinity is non-compact, and that is the multi-scale regime.

**Routes assessed for proving FS** (no proof yet):
1. *Multi-scale IVT* (`pattern_window` at each scale). With infinitely separated scales it reduces to native order six
   for an integer direction M u with no zero entry. Finite separation and the unseparated regimes are compact, so box
   trees can take them. This is the route in progress.
2. *Fourier positivity on the window [1/7, 6/7]* with a smooth minorant. Main term (5/7)(5/14)^5 ≈ 0.0042 for the
   triangle minorant, 5.5e-4 for a 5-fold box minorant.
   - A single relation of height <= 3 already costs 12–42% of the main term, and the tail needs relation heights up to
     about 17 (5-fold box) or about 1,000 (triangle).
   - **Not viable** without handling resonances in bulk.
3. *Union bound:* 10/7 > 1 for five runners. **Not viable.**

**Consequence:** the open part of order seven is now one statement, FS(spread > 50), on a compact time window, true
on every instance tested. Route 1 is next. Meanwhile the six-runner tree is being pushed to v6 <= 100 v1
(`o7_box6_exact_v4.py`, float leaf search with exact verification of every leaf; on 1/12 it matches v3's tree shape).

## E13 (2026-10-17) The geometric-window form of Claim R; the rational-pattern base case

> **DRIFT (marked 2026-10-17, owner):** this entry follows an imported proof shape, not global isolation. Its targets (first-stretch localisation FS50/FS100 — a `DoorFirstLap`-type cap, set aside at n=6 E19/E20/E26–E27; Fourier/equidistribution; the "Diophantine dichotomy"; measure union bounds — set aside as imported framing, n=6 E2) are **not native routes**. True theorems proved here stay true; the direction is withdrawn. See E17.

**Map:** order seven, slow region; Claim R / FS(spread > 50) of E12, route 1 (multi-scale).

**Restatement:** write the fast block as F = W y (y the speed vector with min 1, W = v2/v1). Claim R says that
L(y), the lonely set at 1/7 of the block y, meets every window [a, 6a] with a >= a0 (a = W/7). This holds iff L(y)
starts by 6 a0 and every gap between consecutive components after the first has ratio L_{i+1}/U_i < 6. The ratio
is scale-free, which is the form the multi-scale route works in.

**Exact data** (`o7_geogap_v1.py`, `o7_geogap_v1.out`; `o7_geogap_patterns_v1.out`):
- Real (rational) blocks, s in [0, 120]: in 400 random and 400 near-resonant blocks the worst ratio is **4.833**, near
  (2,3,4,5,7)/2. The first lonely instant is at most 0.307.
- **Every five-runner integer pattern with entries <= 12** (792 patterns; lonely set periodic, exact): **worst ratio
  64/13 ≈ 4.92 at (3,4,5,7,11)**, then 29/6 at (2,3,4,5,7) and 25/6 at (6,7,8,9,10) and (4,6,7,9,10). Every pattern
  is lonely at its first edge instant 1/7.
- **Margin: 64/13 < 6.** The worst cases are small rational patterns, where the multi-scale route bottoms out.

**Route 1 structure** (design; nothing proved here yet):
- (i) Rational patterns: the lonely set is periodic. The ratio bound is a finite exact computation over one period,
  and `pattern_window` transfers it to blocks c Q + e with small e.
- (ii) Near a pattern: L(y) follows L(Q) up to s ~ 1/|y - Q/Q1|. Beyond that, the drift acts as slow offsets, and the
  gaps are those of a lower-dimensional offset problem with target A_Q (recursion on rank).
- (iii) Away from all patterns of height <= K: equidistribution makes gaps short relative to s.
- Each level needs the ratio margin 64/13 < 6, which leaves room for the drift errors.

## E14 (2026-10-17) Order seven for v6 <= 100 v1, kernel-checked; conditional reductions to FS50 / FS100

> **DRIFT (marked 2026-10-17, owner):** this entry follows an imported proof shape, not global isolation. Its targets (first-stretch localisation FS50/FS100 — a `DoorFirstLap`-type cap, set aside at n=6 E19/E20/E26–E27; Fourier/equidistribution; the "Diophantine dichotomy"; measure union bounds — set aside as imported framing, n=6 E2) are **not native routes**. True theorems proved here stay true; the direction is withdrawn. See E17.

**Tree:** `o7_box6_exact_v4.py 1 100 1 6 600`: float leaf search, **every leaf re-verified in exact Fractions** before
it is written. Result: 944,513 leaves, 33,456 empty, 0 failures, 4,012 s.
- On 1/12 its tree shape is identical to v3's.
- Split by `o7_box6_lean_v2.py` into 465 parts. Built three at a time (all 465 ok).
- The assembly's `all_ok` first used one `simp` over 465 lemmas, which failed. It is now an explicit rewrite chain
  (`List.all_append` per part), and the generator emits that chain.

**Proved (nested repo e3c80b1, f93a0c1; axioms [propext, Classical.choice, Quot.sound], `o7_lean_axioms_v2.out`):**
- `LRC.O7Box6T100.lonely` and **`LRC.O7Spread.lonely7_spread100`: order seven holds whenever v6 <= 100 v1.**
- `OrderSevenFirstStretchN`: `FS50 : Prop` (**owed**), `first_stretch_band`, and **`lonely7_of_FS50`: FS50 gives order
  seven for every six-set of positive whole numbers.**
- `OrderSevenSpread100N`: `FS100 : Prop` (**owed**, weaker than FS50: `FS100_of_FS50`) and **`lonely7_of_FS100`**.
- Per the n=8 lesson (a `def … : Prop` is type-checked, never proved): FS50 and FS100 are named owed items. No
  theorem concludes them, and the module docstrings say so.

**Where order seven stands:**
- Proved for v6 <= 100 v1 and for v6 >= 6 v5.
- The rest is exactly **FS100**: a lonely instant of v2..v6 inside the slowest runner's first band stretch when
  v6 > 100 v1.
- Evidence (E12–E13): exhaustive to 60 with every failure at v6/v1 <= 7; Claim R on real speeds; worst geometric gap
  ratio 64/13 < 6 over small patterns.
- Route 1 (multi-scale `pattern_window`, rational-pattern base, compact unseparated regimes) is the proof plan.

## E15 (2026-10-17) Going after FS100: the terminating parts, the residue, and what a proof needs

> **DRIFT (marked 2026-10-17, owner):** this entry follows an imported proof shape, not global isolation. Its targets (first-stretch localisation FS50/FS100 — a `DoorFirstLap`-type cap, set aside at n=6 E19/E20/E26–E27; Fourier/equidistribution; the "Diophantine dichotomy"; measure union bounds — set aside as imported framing, n=6 E2) are **not native routes**. True theorems proved here stay true; the direction is withdrawn. See E17.

**Map:** order seven, FS100 (the only open statement; `lonely7_of_FS100`).

**Why a direct pattern recursion is not a finite proof:**
- One pattern step writes the fast block as c Q + e. The offsets still wind many times across the slow runner's
  stretch: e times the stretch length is about sigma v2/v1, which is large.
- So each level is a full problem again, with a composite target, at unboundedly many levels.
- The parts that terminate are levels whose next speeds are a fixed factor faster (nesting), and blocks of at most 3
  runners (union bound).

**Proved (nested repo, `OrderSevenNestN.lean`; axioms [propext, Classical.choice, Quot.sound]):**
- `full_stretch_in` (length >= 12/(7u) contains a full band stretch);
- `hit_in` (length >= 2/(7u) contains an in-band instant);
- `nest_step`;
- **`lonely7_lacunary`**: if 5 v_{k+1} >= 12 v_k for k = 1..4, then some instant in v1's first band stretch has all six
  in band.

**Provable first-stretch chain** (`o7_fschain_v1.py`, exact, formula-only): single-runner worst-case fold, union bound
with windows for blocks of at most 3, instant at the last step.
- Coverage on v6 > 100 v1 (`o7_fschain_v1.out`):

  | family | closed |
  |---|---|
  | ratios 1.5–4 | 1,413/1,413 |
  | log-uniform speeds | 3,785/3,925 (96%) |
  | uniform middle speeds | 699/3,927 (18%) |
  | runs | 0/99 |

**Residue** (`o7_fschain_resid_v1.out`, 3,000 unclosed random sets):
- Terminal non-lacunary block: size 4 in 962 sets, size 5 in 1,621 (together 86%); size 3 in 223, size 1–2 in 194.
- Clusters (some internal ratio < 1.05): 1,256. Moderate ratios: 1,744.
- Separation Lambda (block min speed × preceding window): 1–10 in 1,224 sets, 10–100 in 372, 100–1,000 in 1,352,
  >= 1,000 in 52.

**What a proof of FS100 needs, by residue type:**
1. *Clusters* (b + small integer offsets): `pattern_window`/`cluster_window` with Q = 1s reduces the block to an
   offset problem with one runner fewer, shifted bands and integer offsets. The first stretch is early time, where
   clusters are coherent when the spread D <= 5 v1/6, which helps.
   - Recursion depth <= 5 -> 4 -> 3, then union bound.
   - Intermediate offsets (e times the window length in [0.1, 15]) form a compact regime of dimension <= 4 including
     the band shift, so box trees apply.
2. *Moderate-ratio blocks:* a **Diophantine dichotomy at the scale of the window**.
   - Either there are no small near-relations, |h·F| times window >> H for 0 < |h| <= H. Then the orbit
     equidistributes (Erdős–Turán–Koksma) and hits band^k, which has measure (5/7)^k.
   - Or F lies near a rational subspace. Then the problem reduces in rank, down to a pattern (rank 1), which is frozen
     when e times the window is <= 1/42 (order-six margin), or recurses.
   - Explicit constants are needed. The shifted (arbitrary-phase) version is false in general, so the reduction must
     keep orbit structure. This is the main new mathematics.
3. *Small separations* (Lambda 1–10): a compact regime, box trees over the normalised block plus window parameters.

**Status:** FS100 is still `[CONJECTURE — EMPIRICAL]`. Lacunary configurations are now `[PROVED]` in Lean. The rest of
the chain is formula-checked: union-bound windows for blocks <= 3 are proved only for w = 0 (`gap_three`), so the
windowed form is owed in Lean. Items 1 and 3 are concrete engineering on existing lemmas. Item 2 is a research step.

## E16 (2026-10-17) Windowed union bound; cluster step; correction: small separation is not compact; the dichotomy

> **DRIFT (marked 2026-10-17, owner):** this entry follows an imported proof shape, not global isolation. Its targets (first-stretch localisation FS50/FS100 — a `DoorFirstLap`-type cap, set aside at n=6 E19/E20/E26–E27; Fourier/equidistribution; the "Diophantine dichotomy"; measure union bounds — set aside as imported framing, n=6 E2) are **not native routes**. True theorems proved here stay true; the direction is withdrawn. See E17.

**Map:** order seven, FS100. Owner: build the cluster recursion and small-separation trees, and move on the open piece.

**Proved (nested repo; axioms [propext, Classical.choice, Quot.sound]):** `LRC.O7Gap3.gap_union`.
- If Σ_d (2L/7 + dLw + 2w/7 + dw² + 4/(7d) + 2w) < L, then `GapProp F (L + w) w`.
- This is the union bound with a window, for any finite set F. It covers the windowed step of the chain, owed in E15.

**Cluster step (product form)** (`o7_fschain_v2.py`, exact; `o7_fschain_v2.out`):
- A block b + e passes to its offsets in shifted bands fixed in advance (via `cluster_window`).
- Coverage moved only slightly: runs 0% -> 9/99, uniform 18% -> 21%, log-uniform 96% -> 96.5%.
- Reason: fixing the base shift y0 in advance turns the free-observer condition (all points within an arc of 5/7)
  into a product of bands, which loses its strength.
- Correct formulation, recorded for next time:
  - a cluster with <= 3 points always fits in an arc <= 2/3 < 5/7 (some gap >= 1/3);
  - 4- and 5-point clusters fail only near equally spaced configurations (every gap < 2/7).
  So the cluster recursion is a *near-equispaced avoidance* problem for the offsets.

**Correction (small-separation regime is not compact):** E15 called it compact. It is not.
- Runner 1's first stretch needs t >= 1/(7 v1). When v2 >> v1, this forces stretch indices m of v2 around
  v2/(7 v1).
- There the block's phases r (m + phi) depend on the arithmetic of r m, and fixed-size boxes in r cannot certify
  that.
- The prototype `o7_sstree_v1.py` checked the wrong side of runner 1's band (it allowed m <= M with v2 large). Its
  output is kept as `o7_sstree_v1_WRONGSIDE.out` and **does not stand**.
- Position arithmetic is the same obstruction as in the moderate-ratio case, so E15's three residue types collapse to
  one open piece.

**The dichotomy, quantified:**
- *Equidistribution branch:* on the window, with a 5-fold box minorant, the main term is about 7.7e-4. The tail
  needs heights H >= 17.
- Among the 35^5 integer vectors of height <= 17, pigeonhole gives a near-relation |h·y| ≲ 10^-5. So the criterion
  needs separation about 10^8. **It never applies at realistic scales.**
- *Resonant branch:* therefore always the operative one. A proof must recurse on the rational-subspace structure of
  the fast block (F = M z + e, M an integer 5 x r matrix), at the actual stretch positions, one dimension per level.
- The free-observer (arc) formulation is the target that composes across cluster levels.

**Status:** FS100 is open. The obstruction is a multi-scale Diophantine recursion at the true positions. The tools so
far (nesting, union bound with windows, `pattern_window`, `cluster_window`) are proved, but no finite certificate
scheme covers the recursion yet.

*E16 correction:* nested commit 5726f8b did not build. A parameter rename broke a reference in `bad_measure_w`, and
the chained shell command still committed. Fixed in 97210d1. `gap_union` now builds and its axiom check is clean.


## E17 (2026-10-17) Restart from global isolation: the order-seven cascade, read through flanks and cells

**Map:** order seven, native. Start from global isolation: the cascade is the oracle, and flanks, residues and cells
explain it, as at n=6 (`SUMMARY_n6_cascade_v5.md`). Observation only; no proof step.

**Cascade** (`cascade/seven_cascade_observe_v1.py`, exact; `seven_cascade_observe_v1_30.out`, `.tsv`): all 588,559
primitive six-sets <= 30.
- It always stops (cap 2,000 never reached). Moves: 0 in 348,631 sets (lonely at 1/(7 v1)), then 107,526 / 72,211 /
  34,516 / …, at most 16.
- Final flank rank: 1: 348,631; 2: 16,828; 3: 42,193; 4: 61,069; 5: 65,183; 6: 54,655.
- The final flank is a multiple of 7 in 93,825 sets.
- When only v6 is a multiple of 7 (51,066 sets), the cascade stops at v6 in 10,540 and at a coarse cell opening
  j = u E in 5,174. The cascade gives the *first* isolation; existence needs any isolation (n=6, E30).

**Flanks and cells** (`cascade/seven_cells_v1.py`, exact residue criterion d(7j+1) mod 7e in [e, 6e];
`seven_cells_v1_30.out`):
- **No multiple of 7:** lonely at t = 1/7, since every reading (v mod 7)/7 lies in [1/7, 6/7]. 228,429 sets.
- **Some multiple of 7**, by shape (|U| non-multiples, |M| multiples):

  | (|U|, |M|) | lonely opening at a 7-divisible flank (of which a coarse cell opening j = uE) | none |
  |---|---|---|
  | (2, 4) | 325 (325) | 0 |
  | (3, 3) | 10,400 (9,271) | 0 |
  | (4, 2) | 88,966 (65,118) | 19 |
  | (5, 1) | 245,711 (144,284) | 14,709 |

- Derivation behind the coarse cells (framework form of the n=6 E1 cell criterion at n=7):
  - At a flank e = 7E, opening j = u E, a runner d = 7q + s slower than e is clear iff (s u) mod 7 lies in {1..5}.
  - So if e is the fastest speed and no other speed is a multiple of 7, each of the five others excludes exactly one
    nonzero shift u. There are 6 nonzero shifts, so one is free and gives a lonely flank opening.
  - Faster runners shift the residue (a ≠ 0) and can block two shifts each. That is where the exceptions come from.
  - Correction to my statement to the owner: n=6 E1 records only "n = 7: no coarse blocking pattern"
    (`cells_general_n_v1.out`). The phi argument (n=6 E45) says blocking is impossible at n = 3, 4, 5, 7, not
    "possible iff phi(n) <= n − 2".

**Exceptions** (no lonely opening at any 7-divisible flank: 14,728; `seven_cells_exc_v1_30.out`,
`seven_cells_exc_v2_30.out`):
- *(i) Feature:* the multiple of 7 is slow: rank 2 in 9,696, rank 3 in 4,150, rank 4 in 797, rank 5 in 66, plus 19
  with two multiples. Runners faster than it: 4 in 9,696 sets, 3 in 4,158.
- *(ii) What forces the witness:* the cascade's instant always has 7 in its denominator. It is a flank opening
  (7j+1)/(7d) or (7j+6)/(7d) of a runner d that is not a multiple of 7. Example: (1,2,3,4,7,12) at 5/28 = 15/84, the
  entry flank of 12.
  - **The fastest runner's flank carries a lonely opening in 14,718 of the 14,728.** Runners 5 and 6 carry one in
    every listed pattern.
  - The remaining 10, e.g. (1,6,7,8,9,10), (2,6,7,8,15,16), are phase-1 pinch sets (E3), lonely only on short
    windows.
- *(iii) Same mechanism:* **not understood yet.** At a flank e coprime to 7, the modulus 7e splits into a mod-7 class
  of j and a mod-e residue (the coprime-flank form, n=6 `six_crt_coprime_v1`). Whether one residue argument covers all
  14,718 has not been derived.

**Next:** read the exceptions' v6 flank openings in the coprime-flank form (which j mod 7, which residues mod v6),
then the 10 pinch sets, then the 19 (4, 2) exceptions.

## E18 (2026-10-17) Order seven on 7-adic residue grids; the cell descent

**Map:** order seven, native: global isolation on residue grids (the framework's own object, as for the AP and
residue-grid sets). Observation and derivation; nothing in Lean yet.

**Cascade order** (`cascade/seven_core_v1.py`; `seven_core_v1_{30,45}.out`), first closer:

| closer | <= 30 | <= 45 |
|---|---|---|
| A: first instant 1/(7 v1), residue form d mod 7v1 in [v1, 6v1] | 348,631 | 4,609,861 |
| B: t = 1/7 | 68,831 | 1,140,655 |
| C: 7-divisible flank cell | 163,526 | 2,228,702 |
| D: core | 7,571 | 86,146 |

- The core is closed by windows and folds (`seven_core_classes_v1_30.out`): T4 7,523, T5 46, T6 2 (the phase-1
  pinches (1,6,7,8,9,10) and (2,7,9,11,13,15)).
- The fastest runner's flank carries a lonely opening in all but the 10 pinch-type sets (`seven_core_flank_v1_30.out`).
- Region v6 > 100 v1 (3,000 random sets, `seven_core_slow_v1.out`): A 744, B 861, C 1,375, D 20. Every D set has
  v1 = 7.
  - On 20,000 more (v1 <= 60, `seven_core_slow_v2.out`): 24 D sets, all with v1 a multiple of 7 (not of 49), all closed
    by the grid k/49.

**Residue grids** (`cascade/seven_grids_v1.py`, `seven_grids_v2.py`, `seven_grids_v3.py`, exact):
- Grid level a means the instants k / 7^a with 7 not dividing k. Such an instant is lonely iff every d k mod 7^a lies in
  [7^(a-1), 6·7^(a-1)].
- **Every primitive six-set <= 45 (8,065,364) is lonely at grid level a = nu_max + 1, or else nu_max + 2**
  (nu_max = largest 7-adic valuation of the speeds):

  | nu_max | level 1 | level 2 | level 3 |
  |---|---|---|---|
  | 0 | 3,233,748 | — | — |
  | 1 | — | 4,823,767 | 7,849 |

  Nothing else occurs. <= 30: the same with 228,429 / 359,444 / 686.
- High valuations (1,470 random sets with planted multiples of 7^b, b = 1..4, speeds up to 10^6; `seven_grids_v3.out`):
  level nu_max + 1 in every case.

**Why, in framework terms (the cell criterion read 7-adically):**
- At level a = nu + 1 (nu = nu_max), a speed of valuation nu reads (d' k mod 7)/7. That is in band for every unit k,
  so the top stratum is automatic.
- Write k = k0 + 7^nu s, with s the top 7-adic digit.
  - A multiple of 7, d = 7 d'', reads d'' k0 / 7^nu: independent of s. So the multiples M behave as the set M/7 at
    level nu.
  - A unit runner's top digit is c_d(k0) + (d mod 7)·s (mod 7). It is blocked for exactly 2 of the 7 values of s.
    This is the coarse-shift structure of `cell_criterion` (n=6 E1): shift u <-> top digit s, fine index i <-> k0.
- **Descent.** If M/7 has a lonely grid instant k0/7^nu and the units leave a free top digit, S is lonely at
  (k0 + 7^nu s)/7^(nu+1).
  - With r <= 3 units, at most 6 of the 7 values of s are blocked, so a free s exists for every k0. S then reduces to
    M/7, which has fewer runners: induction on the number of runners, base t = k/7 when no multiple of 7 is present.
    Consistent with the data: shapes (2,4) and (3,3) close at level 2 without exception.
  - With r = 4 or 5 units (|M| = 2 or 1), the excluded values can cover all 7 choices of s, and k0 has to be chosen. This
    is the remaining case, the same shapes as the cell exceptions of E17. Level nu + 2 is needed exactly for some of
    these (7,849 sets <= 45).
- For |M| = 1, M/7 is a single runner and is lonely at level nu for every unit k0. So k0 ranges over all units mod
  7^nu, and the case is a residue problem for the five units at level nu + 1 (or nu + 2).

**Status:**
- The grid statement is `[EMPIRICAL — exact, exhaustive <= 45; high-valuation samples]`.
- The descent for r <= 3 is `[A]` (argued). It is next for Lean, in residue form.
- Open: the r in {4, 5} case. Next: its structure at level nu + 1 (which (k0, s) work), and the level nu + 2 sets.
