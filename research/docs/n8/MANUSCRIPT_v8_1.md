# A Bounding Framework for Eight Lonely Runners

**T. Palelei.** Draft v8.1, 2026-09-15.

---

## Abstract

Eight runners start together on a circle of circumference 1 and run at distinct constant speeds. The Lonely Runner
Conjecture at eight runners asserts that each of them is, at some instant, at distance at least `1/8` from every
other. The case was settled by computer verification (Rosenfeld 2025), and the computational line has since reached
thirteen runners (Sungkawichai and Trakulthongchai 2026). No analytic proof is known at eight runners.

We present a local framework and a construction that names instants. For each runner separately it reads the other
runners against the runner's own nearest speed difference `d_min`, and runs a **cascade**: from the instant
`1/(8·d_min)` it moves to the latest next opening of the runners in its way, which is the same as changing to the
arithmetic-progression scale at which that runner sits exactly one slot away. Nothing is sampled or estimated; for
commensurate speeds every quantity is an exact rational, and the same construction runs on real speeds.

Its results are stated as three outcomes in the framework's own objects.
**Construction** — if the cascade reaches a fixed point, the runner is lonely there, no earlier positive instant is
lonely, and that instant is the end of the run of lap-completion zones from `1/(8·d_min)`. **Proved.**
**Localisation** — every instant at which the runner is lonely lies at or after every step of the cascade, and is
matched by a lonely opening of one of its own differences no later than it. **Proved.**
**Existence** — the cascade reaches a fixed point: it arrives at a scale at which no reading lies within 1 of a
multiple of 8. **Open.** It is proved in several families (§4.5), and holds in every case computed, including an
exhaustive sweep of all integer arrangements with speeds up to 40.

Two Lean 4 artefacts carry the verification: `Construction8` (85 theorems, frozen since v7) and `Cascade` (135
theorems), both with no `sorry` and every theorem on `propext`, `Classical.choice` and `Quot.sound` alone. The φ(n)
count of isolation instants for an arithmetic progression, the one dependency v7 cited, is now derived in Lean. §7
maps every numbered statement to its declaration.

The construction is not specific to eight runners. At every threshold `1/n` Construction and Localisation hold, and
Existence is proved for every arrangement with two differences (every `n ≥ 3`), three (`n ≥ 4`), four (`n ≥ 6`), and
`k` differences whenever `n ≥ max(9, 2^(k−1))` (§8). **This paper does not establish Existence at eight runners.**

---

## 1. Introduction, and the Boundary Set Method

### 1.1 The shift

The framework fixes one runner, forms that runner's own scale from its two speed-neighbours, and reads every other
runner's position as a lap count relative to it. Each runner is treated independently: the construction is performed
identically and separately for each of the eight, and no runner is held stationary.

**On frames.** Reading `v_j − v_i` is what "`i` is lonely" *means*; it is not a normalisation that privileges `i`, and
it is not the stationary frame. The construction is carried out for every `i`.

**Exactness, and where it holds.** For commensurate speeds every position, lap count and phase is a rational computed
from the speeds, and the clearing test is integer arithmetic (§2.2): an isolation instant is *named*. For incommensurate
speeds the construction is unchanged and returns an irrational instant; the test is then the band condition on the reals
(§2.2). Lean covers both: `Irrational` proves every runner of `(1, 1 + √2/100, 3, …, 8)` lonely at its named instant,
the second runner at the irrational `75√2/4` (§6.8).

### 1.2 The Boundary Set Method

Isolation is decided on the boundary set: the finite, named set of instants at which some runner sits exactly on the
threshold. **Open cells and boundary points are evaluated separately, and touching zones are never merged.** An
in-the-way zone is the set where the circle distance is strictly below `1/8`, so it is an **open** interval and its
endpoints are clear.

**A cell is decided by an interior point, not by its two ends.** The ends of a cell can both be clear while the cell is
an in-the-way zone: at speeds `(0, 12, 14, 16, 30, 35, 38, 53)`, for the runner at 53, the cell `(7/424, 9/424)` has both
ends clear and is the open zone of difference 53. (v7 §1.2 said the ends settle the cell; that is withdrawn.)

In the arithmetic progression `(1, …, 8)` the first runner's lonely instants during its nearest neighbour's first
relative lap are exactly `1/8, 3/8, 5/8, 7/8`. An implementation that closes those brackets, or samples cell interiors
as if they were boundary points, reports the progression's end runners as never isolated — and compiles.

### 1.3 The cascade, and the three outcomes

**The author's statement of the method** (2026-09-14): *"any speed is determined/can be found with reference AP and or
Grid with Dmin and Dmax. So at AP gap of 1, the speed set of 1,2,3.2335,4,5,6,7,8, each runner's isolation can be found
and Dmin gives a proportionate outcome, one resolution … The issue is sometimes speed arrangements don't quite work to AP
times of just 1. So that is where the cascade happens to give you the appropriate AP scale to use."*

Every arrangement is read as an ideal arithmetic progression plus deviations (§2.3). At the runner's own scale `d_min`
the instant `1/(8·d_min)` is the progression's first spine point. When some reading sits in the way there, the cascade
moves to the next scale; the move is determined, not searched (§6.2). §6 proves what the cascade returns
(Construction), what it cannot miss (Localisation), and states what remains (Existence).

v7 confined its evaluation to the nearest neighbour's first relative lap and made that confinement the open claim. The
framework does not require it (revision-list items 1–3), and v8 has no such window: the cascade runs over every lap.

---

## 2. Foundations: the local scale, the integer plane, the ideal

### 2.1 The autonomous scale

Let the speeds be distinct and sorted, `v_1 < … < v_8`. For a subject `i`, put `D = { d_j = |v_j − v_i| : j ≠ i }` and
`d_min = min D`. The minimum is attained at a **speed-neighbour**, exactly: for the extremal runners it is one-sided,
`d_min(r_1) = v_2 − v_1`, and `|v_8 − v_1|` is the largest difference, never a candidate for the smallest. Cyclic
adjacency (§4) is a property of the **track**, not of the speed ordering.

The readings are `s_j = d_j/d_min ≥ 1`, with equality possible — in the progression the second runner's readings are
`1, 1, 2, 3, 4, 5, 6`. **Seven differences, one of which realises `d_min`, leave six readings to evaluate**; the second
speed-neighbour is read like every other runner. Omitting it changes the answer: at `(4, 12, 29, 37, 101, 121, 176,
196)` the runner at 37 has `d_min = 8` and a second neighbour at difference 64, which sits on its lap line at
`1/(8·d_min)`; the cascade's instant is `9/512` (`u = d_min·t = 9/64`). The two readings differ in 3,276 of 48,000
runner-instances.

**The reading is ratio-native.** Dilating every speed by `k` multiplies every `d_j` and `d_min` alike, so the readings
are unchanged and every instant scales by `1/k`. Every dilate `(k, 2k, …, 8k)` of the progression gives each runner
the readings it has in the progression. The doubled progression `(1, 3, 5, …, 15)` is the progression at `d_min = 2`:
every reading is an integer from 1 to 7, so by Theorem 4.8 all eight runners are lonely at `1/16`.

### 2.2 The `(a, m)` coordinates — the commensurate representation

> **Proposition 2.1.** For `t = a/m` and a relative speed `d` (all natural numbers), `‖d·a/m‖ ≥ 1/n` **iff**
> `m ≤ n·R` and `n·R + m ≤ n·m`, where `R = (d·a) mod m`.  `[PROVED — coord_iff]`

Both conditions are on `ℕ`, so the threshold case is in the statement. This is the exact integer form of the clearing
test for commensurate speeds. *(Checked against a direct test on 121,722 triples, zero mismatches.)*

For real speeds the same test is the **band identity**: at the instant `1/(8D)` a runner of reading `s = d/D` is in the
way iff `s` is within 1 of a multiple of 8 (`MomentIterationN.inWay_at_scale_iff`, every real `D > 0`). The integer form
is its representation when the readings are rational.

### 2.3 Every arrangement is an ideal plus deviations

> **Proposition 2.2.** For every arrangement and every real gap `D > 0`, the speeds read as an ideal arithmetic
> progression of gap `D` plus deviations in `[0, D)` (`CascadeRule.reading`, `reading_dev_bounds`); coding the gap as 1
> changes no distance (`gap_is_a_scale`). At the ideal's instant `t = r/(8D)`, runner `j` sits `(idx_j − idx_i)·r`
> eighths from the subject plus its deviation times `r/D` (`position_in_eighths`), and is clear exactly when that is at
> least one eighth from every multiple of 8 (`clear_iff`). A runner with no deviation is clear at every `r` coprime to 8
> unless its index difference is a multiple of 8 (`on_ideal_clear`). Read at gap `d_min`, the nearest runner is on the
> ideal (`nearest_on_ideal_above`, `_below`).  `[PROVED — Cascade/Reading.lean]`

The progression is the reference; the deviations are what the cascade reads.

**Fitting the arrangement between the AP locations.** `[OPEN — how the fit feeds each runner's reading]` The author's
statement (2026-09-14): *"Its about fitting them in between the spaces they can be, so for ap r1 can be 0 to <2, r2 can be
[1] to <3, their is overlap between them."* Stated exactly: against a progression of gap `D`, runner `k` may sit strictly
between its neighbours' locations, `(A_k − D, A_k + D)`, and adjacent bands overlap by one gap; the arrangement **fits** when
every runner is inside its band. Anchoring at the slowest and fastest speeds makes the gap `S/7`. `(1, 31, 75, 97, 128, 160,
176, 225)` fits at gap 32 with deviations `0, −2, 10, 0, −1, −1, −17, 0`; `(1, 2, 3, 4, 5, 6, 7, 100)` does not. The fit
alone does not give every runner an instant `r/(8D)` of the fitted progression `[VERIFIED — exact]`: of the 45,568
eight-subsets of `[1, 20]` that fit, 34,462 give every runner one; of the 80,357 that do not fit, 58,800 still do. And
`(1, 2, 3, 4, 5, 6, 7, 9)` fits while the runner at 2 has no instant `7r/64`, though its own `d_min` reading isolates it at
`1/8` (Theorem 4.8). The fitted progression is the ideal; the runner's instant is read at its own `d_min`. How the fit
decides which runners then need the cascade is the step still to be written down (revision-list item 24,
`experiments/n8/ap_fit_spread_v1.py`).

---

## 3. Local restrictions: the clear-interval bound

Fix a subject and a reading `s`. The instants at which that runner is in the way are the open zones
`((8k − 1)/(8s), (8k + 1)/(8s))` in the lap coordinate `u = d_min·t`, one per lap `k` of the reading.

> **Proposition 3.1.** Each zone has width `1/(4s)`, and consecutive zones are separated by a clear interval of width
> `3/(4s)`.  `[PROVED — blocked_width, clear_width]`

Closing the zones would put `u = 1/8` in the way for `s = 7`, and the progression's spine would vanish.

> **Corollary 3.2 (contiguous reach).** A single reading is in the way contiguously for at most `1/(4s)`.

> **Proposition 3.3 (single-reading exclusion).** Let `σ` be the smallest reading other than the baseline `s = 1`. No
> single reading other than the baseline is in the way throughout a clear interval of `σ`: it would need
> `1/(4s′) ≥ 3/(4σ)`, that is `s′ ≤ σ/3`, while `s′ ≥ σ`.  `[PROVED — no_solo_closure, solo_closure_forces_smaller]`

Excluding the baseline is necessary: with `σ = 8` (the subject at speed 1 of `(0, 1, 9, …)`) the clear interval
`[57/64, 63/64]` lies inside the baseline's zone `(7/8, 9/8)`. *(The formal statement `no_solo_closure` already carries
the hypothesis `σ ≤ s′`; the gap was in v7's prose.)*

So a clear interval of the slowest reading throughout which no instant is clear is in the way either of the baseline, whose
zones are `((8k − 1)/8, (8k + 1)/8)` in `u`, or of at least two readings acting together. Away from the baseline's zones it
is always at least two. v7 dropped the first alternative by confining the evaluation to `[1/8, 7/8]`, which meets no
baseline zone; without that confinement the alternative stays in the statement.

---

## 4. Global structure: gaps, the regular `n`-gon, the reference

### 4.1 Loneliness is a two-neighbour condition

At any instant the eight runners cut the circle into eight cyclic gaps summing to 1.

> **Theorem 4.1.** Runner `i` is lonely **iff** both gaps flanking it on the track are `≥ 1/8`.  `[PROVED —
> lonely_iff_flanks, _first, _last]`

Adjacency is adjacency mod `n`: the first runner's gap before it and the last runner's gap after it are the same wrap
gap. Both directions are proved, and the converse needs only the two flanking pairs — not the attainment of any minimum.

### 4.2 Conservation and the regular `n`-gon

> **Theorem 4.2.** All eight runners are lonely **iff** every gap is exactly `1/8`.  `[PROVED — gaps_all_eq]`

> **Theorem 4.3.** `n` positions in `[0, 1)`, pairwise at circle distance at least `1/n`, are in sorted order an
> arithmetic progression of step `1/n`.  `[PROVED — grid_of_pairwise]`

> **Corollary 4.4.** The number of simultaneously lonely runners lies in `{0, …, 6} ∪ {8}`; it is never 7.  `[PROVED —
> lonely_ne_pred; also exhaustive over all 12,870 eight-subsets of [1,16]]`

### 4.3 The reference instant

Write `V = A + e` against a progression `A_k = v₀ + k·d`, and fix `t = r/(nd)` with `gcd(r, n) = 1`.

> **Theorem 4.5.** The progression part places the `n` runners on the `n` distinct `n`-ths, one each — for every runner
> simultaneously.  `[PROVED — ap_reference]`

> **Theorem 4.6.** The deviation displaces runner `k` by exactly `e_k·r/d` eighths.  `[PROVED — displacement; 15,289
> checked]`

The reference is globally isolated — the φ(n) law (§5) — and deviations from it are then read runner by runner.

### 4.4 When the reference survives

> **Theorem 4.7.** With `v₀` chosen so that `e₀ = 0`, the instant survives **iff** every displacement is a whole number of
> eighths and `k ↦ kr + e_k·r/d (mod n)` is a bijection.  `[PROVED — survives_of; int_of_pairwise_sep, not_dvd_of_sep;
> 12,135 checked]`

The normalisation `e₀ = 0` pins one position at 0, so the regular `n`-gon of 4.3 sits at 0 and every displacement is
integral. The reference is commensurate necessarily: global isolation forces commensurable speeds (`commensurable`).

### 4.5 Families in which the cascade stops at once

Each row gives a class of runners whose first cascade step is already clear, so Existence holds for them.

> **Theorem 4.8 (the ratio condition).** If `d_max ≤ 7·d_min` then `u = 1/8` isolates the subject.  `[PROVED —
> ratio_condition; 35,467 checked]`

Every reading lies in `[1, 7]`, at distance at least 1 from `8ℤ`; sharp at `s = 1` and `s = 7`.

> **Theorem 4.9 (the wide-gap lemma).** If the two speed gaps flanking a runner are each at least the average `S/7`, where
> `S` is the spread, the runner satisfies 4.8. An extremal runner needs only its one gap.  `[PROVED — wide_gap_core,
> wide_gap_end, wide_gap_speeds]`

Contraposed: if 4.8 reaches no runner, no two above-average gaps are adjacent and none is at either end, so there are at
most three. *(Exhaustive over all 24,310 eight-subsets of `{0,…,16}`.)*

4.9 is the case in which a runner's own `d_min` already reaches `S/7`; it says nothing about progressions of gap `S/7`
for runners whose `d_min` is smaller.

> **Theorem 4.10 (integral readings).** If every reading is an integer, the spine instant indexed by a unit `p` clears a
> reading `s` exactly when `8 ∤ s`, the same for every `p`.  `[PROVED — spine_all_or_nothing]`

**Consequences.** (a) **Exact progression readings with no slot-sharer.** When every difference is a whole multiple of
`d_min` and none is a multiple of `8·d_min`, the subject is lonely at `1/(8·d_min)`, and at each of the four instants
`u = r/8`, `r ∈ {1, 3, 5, 7}`. (Run at order 8: 7,950 random seven-reading arrangements from `2…60` without a slot-sharer,
every one clear at the bound; with a slot-sharer the cascade's `R = d_min/D_final` stayed at most `5/2` in 12,050.)
(b) **The residue test, beyond grids.** Any runner whose `d_min` divides every difference reads in integers and is decided
by 4.10; 7,112 of 7,152 such cases checked were not grids. (c) **Grids.** Call the arrangement a grid when its reduced
residues form a complete system mod 8, and let `g` be the gcd of its differences. If every runner has a neighbour at
distance exactly `g`, every runner has `d_min = g` and no difference is a multiple of `8g`, so this is case (a): every
runner is lonely at `1/(8g)` (`GRID_THEOREM_v1`; 485 of 485, including dilates). Without the neighbour hypothesis a grid
need not pass the residue test: runner 1 of `(1, 3, 5, 7, 10, 12, 14, 16)` fails it and all four `u = r/8`, and is lonely
at `t = 1/8`; over grids with differences at most 24, 8,740 of 17,488 grid runners fail the residue test (revision-list
item 14).

(d) **Integral readings localise.** If every reading is an integer and 1 is among them, a subject lonely at some `u` is
lonely at some `u ∈ [1/8, 7/8]`. `[PROVED — localisation_free]`

**How many runners each shortcut settles at once** (v7's measurements, ranges across its populations):

| shortcut | condition | runners settled at once |
|---|---|---|
| the bound, `u = 1/8` | no reading within `1` of a multiple of `8` | ≈ 47–58% (49.5% in the development record) |
| the four instants `u = r/8`, `r ∈ {1, 3, 5, 7}` | the same with `r·s` in place of `s` | ≈ 71–76% |
| Theorem 4.8 | `d_max ≤ 7·d_min` | ≈ 28–33% |
| the residue test, (b) | `d_min` divides every difference, none a multiple of `8·d_min` | ≈ 3–34% |
| grids with the neighbour hypothesis, (c) | a special case of the row above | ≈ 0.4–15% |

The nesting is arithmetic: `d_max ≤ 7·d_min` puts every reading in `[1, 7]`, hence clear at `u = 1/8`; the residue test is the
same band condition with integral readings. So rows 3–5 lie inside row 1, and row 1 is the `r = 1` case of row 2; measured,
rows 3–5 add nothing beyond row 2. Testing all four instants matches the progression's own four (§1.2); v7 recorded that
testing only `1/8` understated it.

**These percentages are not the construction's reach.** They count what a shortcut settles without running the cascade. The
cascade produced a lonely instant for every runner computed (§6.7); reading a shortcut's share as a limit of the construction
is an error recorded in Appendix C.

### 4.6 Where the reference first degrades

At the **global start** `1/(8·m*)`, `m*` the smallest speed gap anywhere, every speed gap reads at least `1/8`, so the only
gap that can be short is the wrap gap between `r_8` and `r_1`; and if `S ≤ 7·m*` the seven speed gaps, each at least `m*`
and summing to `S`, all equal `m*`: the arrangement is the progression. `[PROVED — arithmetic]` If `7·m* < S ≤ 8·m*`,
exactly six runners are lonely there, the short pair being `(r_1, r_8)`. `[VERIFIED — 35 of 35; both regimes exhaustive
over v_8 ≤ 20]` Beyond `S = 8·m*` the short gap moves into the interior as runners
cross; between crossings every gap changes linearly, so a short gap lengthens where speeds separate and a gap shortens only
where runners cross. Of the 77,400 anchored arrangements to `v_8 ≤ 20`, 77,364 are of this migrated kind; per runner the
families of §4.5 still settle large fractions (Theorem 4.8 alone about 31% of runners in random arrangements).
`[VERIFIED — development record]`

**The obligation in the gap frame.** `[OPEN]` Once the short gap has left the wrap: the moving short gap misses both flanks of
runner `i` at some instant. The development record states it with "at some `u ≤ 7/8`"; that bound is the first-window
restriction withdrawn in revision-list items 1–3, and is not part of the obligation here. By Theorem 4.1 and Corollary 6.4
this obligation for runner `i` is Existence for runner `i`, read in gaps.

**Perturbations of the progression are read by `d_min`.** `[VERIFIED at the ε shown]` Each runner's window re-anchors at its
own `1/(8·d_min)`. A **one-sided** perturbation creates a far-end runner on its lap line: `r_8` of `(1 − ε, 2, …, 8)` and
`r_1` of `(1, …, 7, 8 + ε)` are both lonely at `u = 3/8` for `ε ∈ {1/40, 1/10, 1/4}`, the latter at an isolated point
pinched between the readings `9/8` and `15/8` — a boundary point, evaluated separately (§1.2). A **symmetric** perturbation
`(1 − ε, 2, …, 7, 8 + ε)` is absorbed: the end runners' `d_min` grows to `1 + ε` with `d_max = 7 + ε`, so 4.8 gives both at
`u = 1/8` (`ε ∈ {1/10, 1/4}`). The reference state degrades by moving its instant, not by losing it.

---

## 5. No external dependency

v7 cited one ingredient: that for an arithmetic progression the instants of global isolation are exactly `{δt} = r/n`
with `gcd(r, n) = 1`, and that there are `φ(n)` of them per period (Palelei 2026, Theorem 3.1(a)–(b)). **It is now derived
in Lean at general `n`** from the framework's own objects, in `ConstructionN/Instants.lean`:

| declaration | says |
|---|---|
| `isolation_iff_coprime` | integer speeds distinct mod `n` (the progression's residues) are all isolated at `p/n` iff `gcd(n, p) = 1` |
| `card_coprime_eq_totient` | there are `φ(n)` such `p` in `[0, n)` |
| `instants_on_grid`, `coprime_of_isolation`, `isolation_forces_coprime_grid` | for integer speeds with gcd 1, global isolation at any real `t` forces `t = p/n` with `gcd(n, p) = 1` |

That development is outside the two artefacts of §7 (it sits in the general-`n` line with its own gate). The progression's
four instants `1/8, 3/8, 5/8, 7/8` also follow from Theorem 4.3 alone: the eight points `j·t` are pairwise at least `1/8`
apart. Nothing else is cited: no equidistribution, no result at another order, no proof sketch.

---

## 6. The cascade

Throughout, the subject has positive speed differences `ds`, nearest difference `m = d_min`, threshold `1/8`.

### 6.1 The move

> **Definition.** A runner at difference `d` is **in the way** at `t` when `‖d·t‖ < 1/8`. Its **next opening** after `t` is
> the least `(k + 1/8)/d` at or after `t`. The **move** sends `t` to the largest next opening among the runners in the way
> at `t`, and leaves `t` fixed if none is. The **cascade** is the sequence of moves from the **bound** `1/(8m)`.
> (`MomentIterationN.inWay`, `nextOpening`, `move`.)

A runner in the way at `t` stays in the way until its next opening (`inWay_until_opening`), and the next opening is later
than `t` (`lt_nextOpening`). Each move lands on the opening of one runner in the way (`move_eq_self_or_opening`).

### 6.2 The move changes the scale

The bound is the first spine point of the progression of gap `m`. At the instant `1/(8D)` a runner of reading `s = d/D`
is in the way iff `|s − 8N| < 1` for some `N` (`inWay_at_scale_iff`), and its next opening is the first spine point of the
progression of gap `d/(8N + 1)` (`nextOpening_at_scale`). So the cascade is a recursion on the scale:

    D_0 = d_min,    D_{j+1} = D_j · min{ s/(8N + 1) : |s − 8N| < 1 },    instant = 1/(8·D_final),

stopping when no reading is within 1 of a multiple of 8. The runner that sets a move reads exactly `8N + 1` at the new
scale — one slot away, at exactly one eighth. `[DERIVED; VERIFIED — 124,488 of 124,488 runners equal the BSM first
isolation instant]` The moves do not multiply a common factor: each step resets to `D′ = d/(8N + 1)` (at `(1,…,6,8,9)`,
runner 1, the chain `(8, N = 1), (7, N = 1)` ends at `D_final = 7/9`).

**The moves are the scale jumps.** A runner shares an AP slot with the subject at scale `D` when their difference is a
multiple of `8D`; such a runner is on the subject at every instant of that scale. The **dead lattice** records which
scales this rules out: step `D` is dead for difference `d` iff `d = 8k` with `D | k` (`dead_iff`), divisors of dead steps
are dead (`dead_downward`), and a live step always exists (`exists_live`). `[PROVED]` The spread `S` bounds the dead scales:
every slot multiple is at most `S/(8g)`, so at any gap `D` with `8D > S` no runner shares a slot — the scale is live for every
runner. `[PROVED — revision-list item 21]` Live is not the same as lonely: at `(1, 2, 3, 4, 5, 6, 7, 9)`, scale 2, the runner
at 2 has no lonely instant `r/16`, its odd differences `1, 1, 3, 5, 7` taking all four residue pairs mod 16. A clear instant `a/(8D)` forces
`D ≤ a·d_min` (`step_ceiling`). `[PROVED]`

**A single slot-sharer moves the instant by one slot.** For integer readings, with a slot-sharer at reading `S_b` (a multiple
of 8), at `u = p/8 + 1/(8·S_b)` the slot-sharer sits exactly at one eighth (`blocked_lands_on_threshold`), and every integer
reading `s ≤ S_b` with `s·p mod 8 ∈ [1, 6]` stays clear there (`unblocked_stays_clear`). `[PROVED]` This is one move of the
cascade; the dead-lattice scale jump is where the cascade takes several.

### 6.3 Every lonely instant is matched by an opening

> **Proposition 6.1.** If the subject is lonely at `t`, it is lonely at an opening `(⌊e·t⌋ + 1/8)/e` of one of its own
> differences `e`, no later than `t`.  `[PROVED — reading_complete, opening_le; over the reals, every lap]`

So the earliest lonely instant is the bound or one eighth past some lap line of one of the subject's differences
(Theorem 6.2(d) gives the same for the cascade's fixed point). This is a statement about the earliest instant, not about every
lonely instant: those fill intervals. `[PROVED]` The development record checked it on 91,456 of 91,456 runners; the generating
script is not identified there. v7's check of its own procedure: 4,800 of 4,800 returned instants were openings, and across
`n = 5…11` no returned instant was the closing end of a clear stretch. The finite form — the left end of a closed interval
or some zone's right end is clear whenever any point is — is `exists_clear_candidate` (general `n`).

### 6.4 Construction

> **Theorem 6.2 (Construction).** If some step of the cascade is fixed, say at `T`, then:
> (a) the subject is lonely at `T` (`lonely_of_fixed`);
> (b) no positive instant before `T` is lonely (`first_isolation_of_fixed`);
> (c) `T` is the end of a run of lap-completion zones from the bound — each zone `((N − 1/8)/d, (N + 1/8)/d)` about a
> runner's `N`-th relative lap, each containing the end of the one before — and every such run ending at a lonely instant
> ends at `T` (`first_isolation_as_zone_run`);
> (d) some runner sits at exactly one eighth, as the nearest runner ahead or the nearest behind
> (`flank_at_first_isolation`).  `[PROVED — Cascade/Iteration.lean]`

The run of (c) is the boundary set read in time order: sorting every lap-completion zone by its left end and taking one
pass from the bound gives the cascade's instant (29,320 of 29,320). The runner setting each move changes at every move
(1,036; 1,210; 17,112; 1,041 multi-move cases in four families), and the last setter is the flank of (d).

### 6.5 Localisation

> **Theorem 6.3 (Localisation).** For every positive instant `s` at which the subject is lonely:
> (a) `s ≥ 1/(8m)` (`bound_le_of_lonely`);
> (b) every step of the cascade is at most `s` (`iterate_le_of_lonely`; no move passes a lonely instant,
> `move_le_of_lonely`);
> (c) `s` is matched by a lonely opening no later than it (Proposition 6.1);
> (d) the cascade reaches a fixed point (`exists_fixed_of_lonely`): below `s` its steps lie in the finite set of openings
> `(k + 1/8)/d`, `0 ≤ k ≤ ⌈d·s⌉` (`iterate_mem_openings`), and a strictly increasing sequence cannot stay in a finite set.
> `[PROVED]`

> **Corollary 6.4.** For every subject the following are equivalent: the subject is lonely at some positive instant; the
> cascade reaches a fixed point; a run of lap-completion zones from the bound ends at a lonely instant.
> `[PROVED — lonely_iff_run_ends]`

### 6.6 The subject's own AP instants

With `d_l = (a_l + e_l)·m` — AP index `a_l ∈ ℤ`, deviation `e_l` — the instants `n/(8m)` are the subject's own AP instants.

> **Proposition 6.5 (drift lines).** At the own AP instant `n = 8K + r`, runner `l` sits at `(r·a_l + n·e_l)/8` plus `K·a_l`
> whole laps: its AP slot plus its deviation accumulated over `n` eighths (`drift_position`). It is in the way there iff
> `r·a_l + n·e_l` is within 1 of a multiple of 8 (`inWay_at_ap_instant_iff_drift`), i.e. iff
> `n ∈ ((8M − 1)/(a_l + e_l), (8M + 1)/(a_l + e_l))` for some `M` (`drift_blocked_iff_interval`) — its lap zones read at own
> AP instants (`zone_at_ap_instant_iff`).  `[PROVED]`

> **Proposition 6.6 (slot-sharers).** A runner at difference `8b·m` is in the way at every own AP instant
> (`sharer_inWay_at_ap_instant`), so with such a runner present the subject is lonely at no own AP instant
> (`not_lonely_at_ap_instant_of_sharer`).  `[PROVED]` The converse fails: runners with no exact slot-sharer and no lonely own
> AP instant exist (44, 10 and 396 in three families on `[1, 16]`; 51 random to 300).  `[VERIFIED — item 33]` The
> hypothesis "every such runner has a slot-sharer at a finer scale" (some runner with `L·s ∈ 8ℤ`, `L | q`) is refuted: it held
> for 633 of the 1,079 such runners examined.

> **Proposition 6.7 (the own-AP residue rule).** Let the readings be `s_l = c_l/q`. Put `h_l = gcd(c_l, 8q)`,
> `m′_l = 8q/h_l`, `u_l = c_l/h_l`. Runner `l` is in the way at the own AP instant `n` iff `n·u_l mod m′_l` is strictly
> within `m′_l/8` of 0. Hence `m′_l = 1` is a slot-sharer (in the way at every `n`); `m′_l` even and at most 8 is never in
> the way; otherwise `l` is in the way on explicit residue classes of `n`. The lonely own AP instants are the odd `n` outside
> every runner's classes.  `[DERIVED; VERIFIED — 40,000 of 40,000 runners, reading denominators 1 to 30+]`

At denominator `q = 2` this is the pair rule: the odd doubled readings are in the way at `n ≡ ±c⁻¹ (mod 16)`, and the
four pairs `{±1}, {±3}, {±5}, {±7}` all taken leave no lonely own AP instant. The first live lattice on the runner's own
`d_min` is at most `⌊s_max/8⌋ + 1`, `s_max = d_max/d_min` (`WHY_IT_PREDICTS_v1` §2). `[PROVED there]`

**Own AP instants are not the cascade's instant.** Near the wrap, `(1, …, 7, 9 ± δ)`, the first own AP instant at which
runner 1 is lonely recedes like `1/(8δ)`, while its first lonely instant stays at `u = 9/64` (two scales) for `δ` down to
`10⁻⁶`. `[VERIFIED — revision-list item 35]`

### 6.7 Existence

> **Existence.** For every arrangement and every runner, the cascade reaches a fixed point — it arrives at a scale at
> which no reading lies within 1 of a multiple of 8. Equivalently (Corollary 6.4), the run of lap-completion zones from the
> bound ends.  `[OPEN; not stated in either artefact]`

**What is proved of it.** Every family of §4.5; and at other thresholds and fewer differences, the rows of §8.

**What failure would require.** A cascade that never stops lands every step on an opening that lies strictly inside
another runner's zone, for ever; by Theorem 6.3(d) the subject is then lonely at no positive instant, and the steps increase
without bound through infinitely many distinct openings. Each such step is arithmetic: if a runner at difference `e` is in
the way at an opening `t = a/(8d)` at or after the bound, then `|e·a − 8q·d| < d` for some integer `q`, and since
`a ≥ d/d_min` (that is, `t ≥ 1/(8·d_min)`),

    | e − (8q/a)·d | < d_min.

A runner in the way at an opening lies within less than one `d_min` of a specific rational multiple of the difference whose
opening it is. `[PROVED — arithmetic; v7 §7.4, there for the openings of its first window]` Failure needs such a relation at
every step, for ever.

**The obligation is per runner**, not per arrangement: a runner outside the families of §4.5 needs its instant whether or not
another runner of the same arrangement is inside them.

**Evidence.** `[VERIFIED — exact rational arithmetic]`

- **The cascade equals the BSM first isolation instant** for 207,464 of 207,464 runners (one mover; two movers; every runner
  moved; push-out and spread families; all eight-subsets of `[1, 16]`; random integers to 1,000). Most moves in that
  replication: 24. No ceiling on the number of moves has been found: an adversarial climb over speeds up to 400 reached 29,
  at `(27, 70, 107, 137, 159, 188, 344, 393)`, runner 393. Each move lands on an opening before the instant, so the number
  of moves is at most `(7/8)·S·R + 7`. `[PROVED — arithmetic]`
- **Exhaustive sweep.** Every integer arrangement with `0 = v_1 < … < v_8 ≤ 40` and gcd 1 — 18,564,316 arrangements,
  148,514,528 runner-instances — has a lonely instant for every runner; by Corollary 6.4 the cascade reaches a fixed point
  for each. **The enumeration is in the pinned frame `v_1 = 0`**, which is not this framework's: §6A's first row does
  not describe it, and v7 recorded its use as a firewall violation. What carries the counts into the framework's objects is
  that a common shift of every speed leaves every difference `v_j − v_i`, and so every reading, unchanged, and that every
  runner of every arrangement was evaluated. Unpinned, eight distinct positive speeds with gcd 1 return for every runner at
  thresholds `1/5` to `1/10` over 4,025,986 runner-instances, decided by the boundary set, not sampled. Nothing above
  `v_8 = 40` is in the sweep.
- **v7's procedure.** Over 4,800 runner-instances (random integer arrangements, speeds to 1,500), v7's two families together —
  the openings of its first window and its lattice instants `p/(8D)`, `D ≤ 7·d_min` — returned for every runner, the lattice
  family alone for 0.981–0.999; 21,600 runner-instances across seven populations, including adversarial ones, all returned.
  In the `v_8 ≤ 40` record the instants v7's procedure returned (not necessarily the earliest) sit at median `u = 1/8`,
  90th percentile `0.173`, 99th percentile `0.25`, maximum `245/304 ≈ 0.806`.
- **The time ratio** `R = d_min/D_final` (the instant in units of the bound): largest found **≈ 11.96**, at spread
  `S = d_max/d_min ≈ 7.44`, converged on by independent searches on unrelated grids; no `R ≥ 16` found in one round of
  adversarial search over `S ∈ [7, 10]`. `[EMPIRICAL]`
- **Rational and irrational speeds, and the hard cases** (§6.8).

This is verification over bounded families. Nothing here bounds the number of moves or `R` for every arrangement.

### 6.8 Hard cases and incommensurate instances

| arrangement | runner | cascade | instant | check |
|---|---|---|---|---|
| `(1, 31, 75, 97, 128, 160, 176, 225)` | 1 | 23 moves, `d_min = 30` | `11/256` (`u = 165/128`) | = BSM |
| `(1, 1975, 5265, 6910, 8737, 9589, 11845, 15135)` | 1 | 22 moves, `d_min = 1974` | `73/121072` (`u = 219/184`) | = BSM |
| `(11, 21, 22, 23, 26, 34, 35, 40)` | 35 | 1 move, `d_min = 1` | `25/192` | = BSM |
| `(4, 12, 29, 37, 101, 121, 176, 196)` | 37 | 1 move, `d_min = 8` | `9/512` | = BSM |
| `(1, 2, π, 4, …, 8)` | π, 4 | `d_min = 4 − π`, Thm 4.8 | `1/(8(4 − π))`, irrational | Lean: `IrrationalDemo.all_lonely`, `time_irrational` |
| `(1, 1 + √2/100, 3, …, 8)` | 2 | Thm 4.8 fails; clear at the spine `r = 3` of scale `δ` | `75√2/4`, irrational | Lean: `IrrationalCascade.r2_lonely`, `r2_time_irrational` |
| same | 1, 3–8 | | `71/8`; `1/8` | Lean: `r1_lonely`, `others_lonely` |

**What v7 said of these arrangements.** `(1, 1975, …, 15135)`, runner 1, was v7's witness that its openings alone do not
suffice: all 23 openings admissible in its first window fail, and its lattice family clears the runner at `D = 8`, `p = 3`,
`t = 3/64` (lap 92). `(11, 21, 22, 23, 26, 34, 35, 40)`, runner 35, was its witness that the lattice family alone does not
suffice: with a difference equal to `d_min = 1` the ceiling allows only `D ≤ 7` and no such step clears, while the opening
`(d, a) = (9, 25)` does. `[VERIFIED — exact]` v7 read the second as a regime: a runner whose `d_min` is small against its
other differences has almost no lattice to run. `(1, 31, 75, …, 225)`, runner 1, refutes v7's Claim **as written**: nothing
clears in its first window, and it is lonely at `t = 9/40` (`D = 5`, lap 6) `[PROVED — exact, exhibited; revision-list items
1–2]`. The Claim's wording stopped the cascade at lap 0; the `d_min` lattice read past lap 0 isolates the runner at `43/240`
(`u = 5 + 3/8`), and the `1975…` runner at `17/15792` (`u = 2 + 1/8`). All of these are lonely instants later than the
cascade's first. (`experiments/n8/hard_cases_first_isolation_v1.py`.)

---

## 6A. The firewall

The framework's bans are part of it.

| | |
|---|---|
| **No stationary frame** | No runner is pinned to zero. The per-runner reading `v_j − v_i` is what loneliness of `i` means (§1.1) |
| **No first-instant demand** | The construction's correctness does not depend on finding the first instant. That the cascade's fixed point is the first lonely instant is a proved property of its output (Theorem 6.2(b)), not a requirement placed on a search |
| **No global clock** | No single shared isolation event is needed; each runner receives its own instant. Two qualifications: the reference ideal, the arithmetic progression, **is** globally isolated (φ(n) law, §5, Theorems 4.5–4.7), and deviations from it are read runner by runner; and the slowest runner's lap is the cycle in which instants are counted |
| **No measure or density** | Exact arithmetic and the geometry of lap zones only. No measure, density, zero-measure argument, or stability radius |
| **No covering or emptiness language** | The construction forms no complement and no set to be shown empty; it runs a cascade to a named instant |
| **Boundary discipline is mandatory** | Open cells and boundary points evaluated separately; touching zones never merged; a cell decided by an interior point (§1.2) |

Two of these were violated in earlier drafts: the first-instant demand entered v7's §7.1 and §7.2, and the pinned frame entered
v7's §7.4 evidence. v7 recorded both rather than repairing them quietly. In v8 the first is resolved — first-ness is a proved
property of the cascade's output, not a demand — and the second stands as a recorded caveat on the `v_8 ≤ 40` sweep (§6.7).

---

## 7. Formal verification

Two artefacts, Lean 4 with mathlib (§10 for toolchain and digests). Each is built by explicit target by its gate; a plain
`lake build` does not enter `LRC/`.

| | `Construction8` (v7's artefact, frozen) | `Cascade` |
|---|---|---|
| directory | `LonelyRunner/LRC/Construction8/`, 11 modules | `LonelyRunner/LRC/Cascade/`, 7 modules |
| theorems | 85 | 135 |
| `sorry`; `native_decide`, `unsafe`, `admit` | 0; 0 | 0; 0 |
| axioms | the gate checks 23 headline declarations; the 19 further `Construction8` declarations and 7 `ConstructionN` declarations cited here are checked by
`experiments/n8/v8_axiom_check_v1.lean` (output `v8_axiom_check_v1.out`, 26 of 26 within `[propext, Classical.choice, Quot.sound]`) | **every theorem** `[propext, Classical.choice, Quot.sound]`, in the gate |
| gate | `scripts/n8/gate.sh` | `scripts/cascade/gate.sh` |

**The gates.** Both purge build files evicted by file-system sync, build every module by explicit target, inventory
`sorry`, scan for `native_decide`, `unsafe` and `admit`, and run `#print axioms`. Check [4] of each searches declaration
names for a statement of the open part and fails if one is found. The cascade gate was tested to fail on a planted `sorry`
and on a planted declaration naming the open claim; the failure modes of the `Construction8` gate were tested before it
was trusted.

**Which numbered results are machine-checked.**

| result | declaration | artefact |
|---|---|---|
| Prop 2.1 | `coord_iff` | Construction8 |
| §2.2 lap and phase: for `u ∈ [0, 1)`, clear iff `u ∈ [1/8, 7/8]`; a reading clear iff its phase is | `window_iff`, `reading_clear_iff`, `lap_and_phase` | Construction8 |
| §2.1 locality and the bound | `nearest_below`, `nearest_above`, `before_floor` | Construction8 |
| band identity (§2.2, §6.2) | `inWay_at_scale_iff`, `nextOpening_at_scale` | Cascade |
| Prop 2.2 | `reading`, `reading_dev_bounds`, `gap_is_a_scale`, `position_in_eighths`, `clear_iff`, `on_ideal_clear`, `nearest_on_ideal_above/below`, `lonely_of_reading` | Cascade |
| Prop 3.1 | `blocked_width`, `clear_width` | Construction8 |
| Cor 3.2 / Prop 3.3 | `no_solo_closure`, `solo_closure_forces_smaller` | Construction8 |
| Thm 4.1 | `lonely_iff_flanks`, `_first`, `_last` | Construction8 |
| Thm 4.2 | `gaps_all_eq` | Construction8 |
| Thm 4.3 | `grid_of_pairwise` | Construction8 |
| Cor 4.4 | `lonely_ne_pred` | Construction8 |
| Thm 4.5 | `ap_reference` | Construction8 |
| Thm 4.6 | `displacement` | Construction8 |
| Thm 4.7 | `survives_of`; `int_of_pairwise_sep`, `not_dvd_of_sep` | Construction8 |
| Thm 4.8 | `ratio_condition` | Construction8 |
| Thm 4.9 | `wide_gap_core`, `wide_gap_end`, `wide_gap_speeds` | Construction8 |
| Thm 4.10, (d) | `spine_all_or_nothing`, `localisation_free` | Construction8 |
| §5, the φ(n) instants | `isolation_iff_coprime`, `card_coprime_eq_totient`, `isolation_forces_coprime_grid` | general-`n` line |
| §6.1 the move | `inWay`, `nextOpening`, `move`, `inWay_until_opening`, `lt_nextOpening`, `move_eq_self_or_opening` | Cascade |
| §6.2 dead lattice, ceiling, slot-sharer step | `dead_iff`, `dead_downward`, `exists_live`, `step_ceiling`, `blocked_lands_on_threshold`, `unblocked_stays_clear` | Construction8 |
| Prop 6.1 | `reading_complete`, `opening_le`, `clear_on_left`; `exists_clear_candidate` | Construction8; general-`n` line |
| Thm 6.2 | `lonely_of_fixed`, `first_isolation_of_fixed`, `first_isolation_as_zone_run`, `flank_at_first_isolation`, `Run.covers`, `run_of_iterate` | Cascade |
| Thm 6.3, Cor 6.4 | `bound_le_of_lonely`, `iterate_le_of_lonely`, `move_le_of_lonely`, `iterate_mem_openings`, `exists_fixed_of_lonely`, `lonely_iff_run_ends` | Cascade |
| Props 6.5–6.6 | `drift_position`, `inWay_at_ap_instant_iff_drift`, `drift_blocked_iff_interval`, `zone_at_ap_instant_iff`, `sharer_inWay_at_ap_instant`, `not_lonely_at_ap_instant_of_sharer` | Cascade |
| Prop 6.7 | derived and verified (40,000), not formalised | — |
| §6.8 incommensurate instances | `IrrationalDemo.*`, `IrrationalCascade.*` | Cascade |
| §8 small orders | `VersionB.two_diffs`, `three_diffs`, `four_diffs`, `slowest_recursion`, `order_three`, `order_four` and the sections behind them | Cascade |

The negative results of Appendix A are proved in the text with explicit counterexamples; only the `2σ` containment is
formalised (`two_sigma_zone_inside`, general-`n` line).

---

## 8. Generalisation

### 8.1 The infrastructure at every `n`

The cascade and every statement of §6.1–6.6 except Proposition 6.7 hold at threshold `1/n` for every `n ≥ 2`, over any
finite set of positive differences: the Lean statements of `Cascade/Iteration.lean` carry `n` as a parameter, and the
order-8 statements are their instances.

Of `Construction8`'s 85 theorems, 59 are stated at general `n` and a further 20 involve no runner count (statements about
reals: the contiguous-reach bound, the circle-distance identities, the index-free wide-gap core). Six carry `n = 8`, all of
them the zone geometry of §3: the two zone widths, the two ratio bounds, and the two halves of the single-reading exclusion.
Their general forms are formalised in the general-`n` line, with theorems instantiating them at `n = 8` and recovering the
`Construction8` constants:

| | general `n` | `n = 8` |
|---|---|---|
| zone width | `2/(ns)` | `1/(4s)` |
| clear interval | `(n−2)/(ns)` | `3/(4s)` |
| first-zone overlap (Appendix A, 2) | `s/s′ < (n+1)/(n−1)` | `9/7` |
| descent through consecutive integers — a chain of first zones of readings `s, s−1, …` persists only while `2s > n + 1` | `2s > n + 1` | `2s > 9`, breaking at `s = 4` |
| single-reading exclusion (Prop 3.3) | `s′ ≤ 2σ/(n−2)`, needs `n > 4` | `s′ ≤ σ/3` |
| `2σ` containment (Appendix A, 3) | needs `n > 3` (`two_sigma_zone_inside`) | holds |

The single-reading exclusion needs `n > 4`: at `n = 4` its two sides coincide. The remaining five forms hold for every `n ≥ 1`.
**The local restrictions tighten as `n` grows.** The overlap bound `(n+1)/(n−1)` decreases towards 1 — `9/7` at `n = 8`,
`13/11` at `n = 12`, `17/15` at `n = 16` — so two readings must be closer in ratio for their zones to meet; the exclusion
`2σ/(n−2)` tightens likewise. Whatever obstruction these local bounds present, it is not weaker at larger `n`.

### 8.2 Existence with few differences

With `k` differences at threshold `1/n` (the order-`n` case is `k = n − 1`). All `[PROVED — Cascade]`, each with its Version B
form: the stated step of the cascade is lonely and first.

| differences | orders | cascade stops within | theorem |
|---|---|---|---|
| 2 | every `n ≥ 3` | 1 move | `two_diffs_stop_within_one_move` |
| 3 | every `n ≥ 4` | 3 moves | `three_diffs_stop_within_three_moves` |
| 4 | every `n ≥ 6` | 7 moves | `four_diffs_stop_ge_six` |
| `k` | every `n ≥ max(9, 2^(k−1))` | `2^(k−1) − 1` moves | `stops_slowest_recursion` |

The orders `n = 3` and `n = 4` (two and three differences) are the first two rows read on the diagonal (`TerminationThree`, `TerminationFour`; at
`n = 4` the instant also satisfies `d_min·t < 3/4`).

**The tools**, every `n`: a move set at lap `Q` multiplies the instant by less than `(nQ + 1)/(nQ − 1)`
(`move_growth`); a runner that left at lap `P` is back in the way only after growth `(nP + n − 1)/(nP + 1)`
(`return_growth`), which after a single move reads `Q(n − 2) < 2P + 1` (`return_lemma`); no runner returns straight after
a move by a runner at least as fast (`no_return_after_faster`, `n ≥ 4`); no two runners set four consecutive moves
alternately (`no_four_alternation`); no return across `g` faster moves when `n ≥ 2g + 2` (`no_return_after_few_faster`);
the nearest runner's reading is at most `(1/n)·∏` of those factors (`nearest_reading_recurrence`).

**Order 5 is open.** In the cascade's quantity it is `R = d_min/D_final < 4`. `[OPEN]` What is established: `R` is a product
of step factors `(5N + 1)/(5N − 1 + δ)`; a cascade of lap-1 steps only has `R < (3/2)³ = 27/8`; exact progression readings with
no slot-sharer give `R = 1`; the runners that can be in the way at the own AP instants `R = 2, 3` fall in explicit
slot-and-deviation classes; the largest `R` found is `≈ 31/9`. `[DERIVED / VERIFIED; revision-list item 52]` The last figure is `[EMPIRICAL]`: it is
the rational recognised from the optimum of floating-point linear programs over bounded searches (item 49).
From order 6 the nearest runner itself can set a move: at `n = 6`, speeds `1, 59733/25000, 299191/100000, 392283/100000,
516561/100000`, it is in the way at the ninth step and the cascade ends at nearest reading 8.3559 (BSM agrees). Largest
nearest readings found at `n = 6, 7, 8, 9`: 8.60, 9.04, 11.66, 10.66, each below `2n − 1`. `[VERIFIED instance; EMPIRICAL
maxima]`

**What does not carry over.** The reach figures of §4.5 and the evidence of §6.7 are measurements at order 8.

---

## 9. What is and is not established

**Construction** (Theorem 6.2) — proved, in Lean: a fixed point of the cascade is lonely, first, the end of the run of
lap-completion zones from the bound, and has a flank at exactly one eighth.

**Localisation** (Theorem 6.3, Corollary 6.4) — proved, in Lean: every lonely instant is at or after every step of the
cascade and is matched by a lonely opening no later than it; a lonely instant forces the cascade to a fixed point.

**Existence** (§6.7) — open at order 8. Proved in the families of §4.5, and at the orders and difference counts of §8.2.
Verified over the families of §6.7, with no case found in which the cascade fails to stop.

If Existence held for every runner, the conjecture at eight runners would follow.

Also established: every numbered result of §§2–4 (§7 gives the declaration); §5's derivation of the φ(n) instants; the
negative results of Appendix A, proved in the text.

---

## 10. Data and code availability

**The formal development.** Lean 4, toolchain `leanprover/lean4:v4.29.1`, mathlib revision
`5e932f97dd25535344f80f9dd8da3aab83df0fe6` (tag `v4.29.1`), batteries `756e3321fd3b02a85ffda19fef789916223e578c`.

- `LonelyRunner/LRC/Construction8/` — eleven modules `Parts`, `LemmaPass`, `Coords`, `Reference`, `Gaps`, `Sorted`, `Grid`,
  `Integrality`, `Flank`, `Window`, `Bounds`; digest
  `578022e0296ce565ec601655747d1e5cdc614a9efa2cced6540162e698f43b9d`; gate `scripts/n8/gate.sh`.
- `LonelyRunner/LRC/Cascade/` — seven modules `Iteration`, `SmallOrders`, `FourDifferences`, `VersionB`, `Reading`,
  `Irrational`, `All`; digest `9657ea89bb28bb3ec03bb313a42c7e91b6750cde396cf0572e9300caab116b39`; gate `scripts/cascade/gate.sh`.
- Both digests: `shasum -a 256 *.lean | sort -k2 | shasum -a 256` in the directory.
- `LonelyRunner/LRC/ConstructionN/` — the general-`n` line (§5, §8.1), not part of either artefact, gate `scripts/nN/gate.sh`.

**Computations** (exact rational arithmetic unless stated), in `experiments/n8/` and `experiments/small_n/`:
`complete_predictor_replication_v1.py` (207,464), `scale_cascade_recursion_v1.py` (124,488), `chain_from_laps_v1.py`
(29,320), `move_setters_v1.py`, `residue_rule_q_v1.py` (40,000), `r16_search_v2.py` and `ratio_vs_spread_v1.py` (`R`),
`hard_cases_first_isolation_v1.py` (§6.8), `n8_exact_ap_v1.py` (§4.5), and for §8.2 the scripts cited in revision-list items
37–52.

**The exhaustive record of §6.7.** The `v_8 ≤ 40` sweep is a single JSON record, SHA-256
`18f8f88a0f92e08cd2110c61e75b92189baba80506cc73aa098cc86385525a7c`, produced by `exhaustive_exact.py`, SHA-256
`1589b78f939564718204a338b380283b5e0181162e4d2903205e57232be84bc3`; its `u_max_runner: 7` is a 0-based index. It sits in a
separate working tree; both will be deposited together, and the digests identify the deposited copies.

---

## References

**Barajas, J. and Serra, O. (2008).** *The lonely runner with seven runners.* Electronic Journal of Combinatorics **15**,
R48. — seven runners, the largest case with a proof that is not computer-assisted.

**Rosenfeld, M. (2025).** *The lonely runner conjecture holds for eight runners.* arXiv:2509.14111, submitted 17 September
2025, revised 16 October 2025. — eight runners by computer verification with bounds on a minimal counterexample. Rosenfeld
states the problem with a stationary runner and seven non-zero speeds; the framework here holds no runner still.

**Sungkawichai, T. and Trakulthongchai, T. (2026).** *Eleven, twelve, and thirteen lonely runners.* arXiv:2604.23906,
submitted 26 April 2026, revised 1 September 2026. — extends the computational line to `k ∈ {10, 11, 12}` non-stationary
speeds, thirteen runners. Builds on the method of Rosenfeld and the second author, which had reached `k ≤ 9`.

**Palelei, T. (2026).** *The φ(n) Law for Arithmetic Progressions in the Lonely Runner Conjecture: Algebraic Structure and
Computational Fragility.* Working paper, version 1.0, 4 January 2026. Zenodo, DOI **10.5281/zenodo.18158886**. — Theorem
3.1(a)–(b): the instants of perfect isolation for an arithmetic progression and their count; derived in Lean here (§5).

---

## Appendix A. Routes that cannot close this

Each is a route that looks natural and does not work, with the reason. Stated as contributions.

**1. Comparing the in-the-way zones' total length with the lap cannot name an instant.** In the progression the first
runner's lonely instants during its nearest neighbour's first lap are four isolated points `1/8, 3/8, 5/8, 7/8`: the set on
which such a comparison would have to find room has length zero in the case that matters. Any argument must name an instant.

**2. A chain of overlapping zones does not have a ratio to accumulate.** A route that follows a chain of overlapping
in-the-way zones (a run, in §6.4's terms) and bounds the spread of readings it can pass through fails on four exact facts.
(i) `u = 7/8` can be in the way of a reading well above `9/7`: `s = 11/5` on its second lap, `‖(11/5)(7/8)‖ = 3/40`.
(ii) The overlap bound `s/s′ < 9/7` holds for first zones only; lap `k` of `s` meets lap `k′` of `s′` when
`s/s′ < (8k + 1)/(8k′ − 1)`, giving `17/7` and `25/7` later. (iii) A run is built from zones, not runners: a reading `s` has
about `3s/4` zones per lap of the nearest runner — seven readings supply about 24 — and an observed run went 11 steps with
readings recurring; `N` runners do not give `N − 1` steps.
(iv) A single reading can be in the way at both `u = 1/8` and `u = 7/8`: `s = 8`.

*Data on runs.* Over every arrangement to `v_8 ≤ 20` whose short gap has moved off the wrap (§4.6): 231,294 runner-instances
with a reading in the way at the bound; runs of mean 2.38 zones, 99th percentile 8, maximum 19; ends at 99th percentile
`u = 0.304`, maximum `0.589` (at `(0, 2, 8, 10, 11, 13, 16, 17)`, runner 0, reading 7); none of the 231,294 reaches
`u = 7/8`. These are small integer arrangements; runs elsewhere end much later (§6.7: `R ≈ 11.96`, `u ≈ 1.5`).

**3. Counting readings against clear intervals fails.** A reading `s = 8` does split the nearest runner's first lap into 7
zones and 6 clear intervals of `3/32`; in the search below five readings closed at most three of the six, so the conclusion survives with margin, but the
counting argument for it does not. The inference that five other readings cannot be in the way on six intervals assumes
one reading per interval; readings share an interval, and one reading has zones in several. Over 300,000 draws of five
readings, the most closed was three of the six, which is neither none nor all. And no count on how many intervals one reading reaches can repair
it: with `σ` the smallest reading other than the baseline, the lap-`(2k+1)` zone of `s = 2σ` lies inside the clear interval
`((8k+1)/(8σ), (8k+7)/(8σ))` of `σ` **for every** `k` (`two_sigma_zone_inside`, needs `n > 3`). `[PROVED]` So Proposition 3.3's
"at least two readings acting together" cannot be combined with a count of how many intervals each reading reaches.

**4. Runners in the way together (H1).** The development record states H1 as: same-side runners are in the way together
only where their connecting difference is within `1/4` of a lap line. The sharper form holds. If the two runners sit at
`x`, `y` relative to the subject with `‖x‖, ‖y‖ < 1/8`, then `‖x − y‖ ≤ ‖x‖ + ‖y‖ < 1/4`; and if both lie on the same side,
in `(0, 1/8)` or in `(−1/8, 0)`, then `|x − y| < 1/8`. Since `x − y` is the connecting difference times `t`, that difference is
within `1/4` of a lap line, and within `1/8` on the same side. `[PROVED — the two lines above; not formalised]` The development record combines H1 with the overlap
bound of item 2 to argue that a long run forces near-divisibility conditions `k·b ≡ 0 (mod 8a)` on the arrangement's gaps
(`PROOF_DEV_v1` Part V). That step is stated there, not derived; it is recorded here as a direction in the framework's
objects, not as a result. The next test it names: trace the steps of the longest run (19 zones) and locate the arithmetic
that ends it.

---

## Appendix B. From v7 to v8

| v7 | v8 | reason |
|---|---|---|
| §1.3, the first-window target | removed; §1.3 now states the cascade | the framework does not confine the evaluation (items 1–3) |
| §1.2 "a cell is settled by its two ends" | withdrawn; decided by an interior point | counterexample, item 14 |
| §1.1, §2.2 unconditional exactness | exact for commensurate speeds; real band test otherwise | items 11, 13 |
| §5 external debt | §5 no external dependency | φ(n) instants derived in Lean |
| §6 negative results | Appendix A | author's decision |
| §7.1 two families; §7.2 openings; §7.3 soundness; §7.4 Claim | §6: the cascade; Prop 6.1; Theorems 6.2–6.3; Existence | items 12, 25, 27–34. The Claim is refuted as written (`(1, 31, …, 225)`, runner 1, lonely at `9/40`, lap 6; items 1–2): its wording stopped the cascade at lap 0. It is replaced by the cascade over every lap, whose Existence is open. Its witnesses and figures are kept in §6.7–6.8 |
| §7.4 settled cases table | §4.5 | kept with its figures, relabelled "settled at once" rather than "reach" (Appendix C); the grid row corrected (item 14) |
| §7.4 evidence | §6.7 | carried by Corollary 6.4; the pinned-frame caveat kept, with the difference-invariance that carries the counts stated beside it |
| §7.4 "what failure would require" | §6.7 | the same inequality, now for every opening at or after the bound |
| §7A | §6A | first-instant row reworded; global-clock qualifications (item 23) |
| §8 | §7 | two artefacts; LemmaPass declarations added (items 7, 18, 25) |
| §9 "the claim of §7.4, read at general `n`, is the conjecture itself" | removed | a relabel of the open statement |
| §9 | §8 | infrastructure plus Existence with few differences |
| §10 "This paper does not prove LRC(8)"; "n = 8 is not proved by this paper" | abstract "does not establish Existence at eight runners"; §9 | outcomes are stated in the framework's objects; the conjecture is named once, in §9 |
| §10 | §9 | the three outcomes |
| References: Rosenfeld "the two formulations agree by the standard reduction" | removed | nothing in v8 uses a reduction to a stationary runner; Existence is stated per runner on differences |
| — | §4.6 | wrap gap at the global start, gap migration and its obligation; perturbations (`LOST_FUNCTIONS_v1` §§F, H) |
| — | §2.3 | fitting between AP locations, open (item 24) |
| — | Appendix C | the objection ledger's tested objections (ruling Q4) |
| v7 §3 "the baseline has no zone inside the evaluation window" | §3 | the window is gone, so Proposition 3.3's conclusion keeps the baseline alternative |

---

## Appendix C. Objections tested

Recorded from the objection ledger (append-only). Each objection was tested rather than argued. The figures are for the
construction as it stood when tested, 2026-09-14.

**Objections that do not apply.**

| objection | outcome |
|---|---|
| Incommensurable speeds break it | 0 failures over 3,200 runner-instances with every difference irrational; now also proved on instances in Lean (§6.8) |
| Ties among the differences break it | 8,122 instances with repeated differences, 0 failures |
| It is an `n = 8` construction | the rules fired for 76.7–87.0% at `n = 5, 6, 7, 8, 9, 11, 12, 13`, and every instant produced was genuine, 23,703 of 23,703; §8 |
| It needs a global clock | `(3, 7, 12, 20, 29, 31, 44, 50)`: eight runners, five distinct instants, no instant at which all eight are lonely together |
| It needs the real-to-integer reduction | the test reads irrational differences directly (§2.2 band identity) |
| Measure or density is required | inapplicable: the quantity such an argument bounds is zero for the progression, where the framework names `t = 1/8` (Appendix A, 1) |
| Covering, or counting the candidates | inapplicable by type: both conclude that some point survives, and the construction names which |
| The test might not mean what it says | `D ≤ (a·e mod nD) ≤ (n−1)D` iff distance at least `1/n`: proved (Prop 2.1), and checked on 28,000 cases at `n = 5…13` |
| Producing an instant does not settle the conjecture | an instant at which a runner is lonely is what the conjecture asks of that runner (§9) |

Testing the first exposed a restriction imported into the test: the gap `D` had ranged over integers. The gap is a scale,
`k·d_min`; with it, the failures went to zero. The earlier restrictions of the same kind were the first window, `p ∈ {1, 3,
5, 7}`, the lap as part of the output, and `a ≡ 1 (mod 8)`.

**Objections raised and found to be false blockers.**

| objection | why it was false |
|---|---|
| "The construction is not proved to always produce", from rule shares of 81.9% and 66.0% | a rule's share is not the construction's reach: the construction produced for 12,000 of 12,000 random runners and for every runner of every hard case on file |
| "The stepping is not proved to terminate", read as an unbounded search | each step is a finite test; no search is performed. What remains open is stated as Existence (§6.7): whether the sequence of steps reaches a fixed point |
| "The gcd rule does not survive incommensurability" | the `d_min`-scaled cascade produced for 1,600 of 1,600 all-irrational runners without it |
| "§7.4 has a counterexample", from `(1, 31, …, 225)` | it refutes v7's wording, which stopped at lap 0; read past lap 0 the runner is isolated (§6.8) |
| "Theorem 4.7 is an imported global obligation" | global isolation of the progression is the framework's reference ideal (§5); the per-runner reading of deviations gives the instants where the reference instant does not survive |

The pattern in each: a restriction placed on a search the construction does not perform — how long, how much of the space,
or when — read back as a limit of the construction.

**What remains.** The first three rows above withdrew those objections as they were framed. What survives of them is the one
obligation the ledger states: prove that the construction always produces, either by rules whose conditions are exhaustive
or by proving that the stepping reaches its instant. In v8 that obligation is Existence (§6.7), open. Two objections stand
and are stated where they apply: the evidence is finite (§6.7), and exactness holds only for commensurate speeds (§1.1,
§2.2) — a claim about the method, not a failure of it; the incommensurate runners are proved lonely at their instants
(§6.8).
