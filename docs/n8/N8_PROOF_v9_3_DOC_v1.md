# The n = 8 Framework, v9.3 — Documentation

**T. Palelei.** Documentation file, v1, 2026-09-18. Not a manuscript version; it documents one.

**Source of record for the body.** `docs/n8/MANUSCRIPT_v9_3.md` (frozen 2026-09-17,
header-stamped superseded). Nothing here restates a grade the source does not carry.

**Status of v9.3 itself.** v9.3 was the manuscript of record for part of 2026-09-17 and was
superseded the same day by v9.4. As of 2026-09-18 the manuscript of record is
**`MANUSCRIPT_v9_6.md`**. Sections 1–9 below document v9.3. **Section D documents what changed
after it**, so that nothing here reads as current when it is not.

**What the framework does and does not settle.** The Lonely Runner Conjecture at eight runners is
**not proved** here. Two of the framework's three outcomes are proved; the third, **Existence**, is
open at order 8. The case is settled in the literature by computer verification (Rosenfeld 2025);
no analytic proof at eight runners is known.

---

## 0. Grade vocabulary

Grades are the source's own and are reproduced, never raised.

| tag | meaning |
|---|---|
| `[PROVED]` | a proof exists; where a Lean declaration is named, it is machine-checked |
| `[DERIVED]` | follows by stated arithmetic from a `[PROVED]` result, not separately formalised |
| `[VERIFIED — scope]` | exhaustive or exact computation over the stated finite range; not a proof |
| `[EMPIRICAL]` | sampled computation; a measurement, not a bound |
| `[OPEN]` | stated, not proved |
| `[WITHDRAWN]` | previously asserted, retracted, with the reason recorded |

A `[VERIFIED]` result is never a substitute for a `[PROVED]` one, and the source does not treat it
as one.

---

## 1. The object, and the shape of the result

Eight runners start together on a circle of circumference 1 at distinct constant speeds. The
conjecture at eight runners asserts each runner is, at some instant, at circle distance at least
`1/8` from every other.

The framework fixes **one runner at a time** and reads the others against it. For subject `i`:

- the **disparities** are `Δ_i = { d_j = |v_j − v_i| : j ≠ i }`, seven of them;
- `d_min = min Δ_i`, attained at a **speed-neighbour**;
- the **readings** are `s_j = d_j / d_min ≥ 1`;
- the **bound** is the instant `1/(8·d_min)`, the first spine point of the arithmetic progression
  of gap `d_min`.

Reading `v_j − v_i` is what "`i` is lonely" means. It is not a normalisation that privileges `i`,
and it is not a stationary frame; the construction is carried out for every `i` (§6A).

From the bound the framework runs the **cascade** (the determinator): it moves to the latest next
opening among the runners currently in the way, which is the same as changing to the progression
scale at which that runner sits exactly one slot away. The step is fixed by the speeds — nothing is
searched, sampled or picked.

**The three outcomes.**

| outcome | statement | grade |
|---|---|---|
| **Construction** | if the cascade reaches a fixed point, the subject is lonely there, no earlier positive instant is lonely, and that instant ends the run of lap-completion zones from the bound | `[PROVED]` |
| **Localisation** | every lonely instant is at or after every step of the cascade, and is matched by a lonely opening of one of the subject's own disparities no later than it; so the subject is lonely somewhere exactly when some **flank** has a lonely opening | `[PROVED]` |
| **Existence** | the cascade reaches a fixed point — it arrives at a scale at which no reading lies within 1 of a multiple of 8 | **`[OPEN]`** at order 8 |

If Existence held for every runner, the conjecture at eight runners would follow. It does not hold
by anything in v9.3.

**Real speeds throughout.** Every object the results use — the band identity, drift intervals, the
step between scales, flank openings — is stated and proved over the reals. For commensurate speeds
the clearing test also has an exact integer form, and computation is then exact rational
arithmetic. Irrational speeds are not an exception anywhere in the framework.

---

## 2. Foundations

### 2.1 The autonomous scale

All seven readings are evaluated, including the `d_min` reading and the second speed-neighbour's.
Both can be in the way and both can set a move. Reading five disparities instead of six non-`d_min`
ones changes the answer in 3,276 of 48,000 runner-instances `[VERIFIED]`.

Notation used throughout: `S = d_max/d_min` (the subject's ratio), `W = v_8 − v_1` (the spread of
the speeds), `R = d_min/D_final` (the cascade's instant in units of the bound).

**The reading is ratio-native.** Dilating every speed by `k` multiplies every `d_j` and `d_min`
alike, so readings are unchanged and every instant scales by `1/k` `[PROVED — arithmetic]`.

### 2.2 The `(a, q)` coordinates, and the band identity

> **Proposition 2.1.** For `t = a/q` and a relative speed `d` (all natural numbers),
> `‖d·a/q‖ ≥ 1/n` **iff** `q ≤ n·z` and `n·z + q ≤ n·q`, where `z = (d·a) mod q`.
> `[PROVED — coord_iff]`

Both conditions are on `ℕ`, so the threshold case is inside the statement. This is the exact
integer form of the clearing test for commensurate speeds. Checked against a direct test on
121,722 triples, zero mismatches `[VERIFIED]`.

For real speeds the same test is the **band identity**: at the instant `1/(8D)` a runner of reading
`s = d/D` is in the way iff `s` is within 1 of a multiple of 8
(`MomentIterationN.inWay_at_scale_iff`, every real `D > 0`) `[PROVED]`. The integer form is its
representation when the readings are rational.

### 2.3 Every arrangement is an ideal plus deviations

> **Proposition 2.2.** For every arrangement and every real gap `D > 0` the speeds read as an ideal
> arithmetic progression of gap `D` plus deviations in `[0, D)`; coding the gap as 1 changes no
> distance. At the ideal's instant `t = r/(8D)`, runner `j` sits `(idx_j − idx_i)·r` eighths from
> the subject plus its deviation times `r/D`, and is clear exactly when that is at least one eighth
> from every multiple of 8. `[PROVED — Cascade/Reading.lean]`

The instants `r/(8D)` with `r` odd are the **spine** of scale `D`; `r = 1` is its first spine point.
The progression is the reference; the deviations are what the cascade reads.

**Open within §2.3.** How the arrangement's *fit* between AP locations feeds each runner's reading
is `[OPEN]`. The fit alone does not give every runner an instant of the fitted progression
`[VERIFIED — exact]`: of 45,568 fitting eight-subsets of `[1, 20]` with gcd 1, 34,462 give every
runner one; of 80,357 non-fitting, 58,800 still do.

---

## 3. Local restrictions

Fix a subject and a reading `s`. In the lap coordinate `u = d_min·t` the in-the-way zones are the
**open** intervals `((8k − 1)/(8s), (8k + 1)/(8s))`, one per lap.

> **Proposition 3.1.** Each zone has width `1/(4s)`; consecutive zones are separated by a closed
> clear interval of width `3/(4s)`. `[PROVED — blocked_width, clear_width]`

> **Corollary 3.2.** A single reading is in the way contiguously for at most `1/(4s)`.

> **Proposition 3.3 (single-reading exclusion).** With `σ` the smallest reading other than the
> baseline `s = 1`, no zone of a single reading `s′ ≥ σ` other than the baseline contains a clear
> interval of `σ`. `[PROVED — no_solo_closure, solo_closure_forces_smaller]`

Excluding the baseline is necessary, and the exclusion is exhibited by a counterexample in the
source. So a clear interval of the slowest reading throughout which no instant is clear is in the
way either of the baseline or of at least two readings acting together.

**Boundary discipline is load-bearing.** Zones are open and their endpoints are clear. Closing them
would put `u = 1/8` in the way for `s = 7` and the progression's spine would vanish. A cell is
decided by an interior point, not by its two ends: at `(0, 12, 14, 16, 30, 35, 38, 53)` the cell
`(7/424, 9/424)` has both ends clear and is an in-the-way zone. (v7 §1.2 said the ends settle the
cell; that is `[WITHDRAWN]`.)

---

## 4. Global structure

### 4.1–4.4 Gaps, the regular n-gon, the reference

> **Theorem 4.1.** Runner `i` is lonely **iff** both gaps flanking it on the track are `≥ 1/8`.
> `[PROVED — lonely_iff_flanks, _first, _last]`

Adjacency is adjacency mod `n`; both directions are proved, and the converse needs only the two
flanking pairs.

> **Theorem 4.2.** All eight runners are lonely **iff** every gap is exactly `1/8`.
> `[PROVED — gaps_all_eq]`

> **Theorem 4.3.** `n` positions in `[0, 1)` pairwise at circle distance at least `1/n` are, in
> sorted order, an arithmetic progression of step `1/n`. `[PROVED — grid_of_pairwise]`

> **Corollary 4.4.** The number of simultaneously lonely runners lies in `{0, …, 6} ∪ {8}`; never 7.
> `[PROVED — lonely_ne_pred; also exhaustive over all 12,870 eight-subsets of [1,16]]`

> **Theorem 4.5.** The progression part places the `n` runners on the `n` distinct `n`-ths, one
> each, for every runner simultaneously. `[PROVED — ap_reference]`

> **Theorem 4.6.** The deviation displaces runner `k` by exactly `e_k·r/d` eighths.
> `[PROVED — displacement; 15,289 checked]`

> **Theorem 4.7.** With `e₀ = 0`, the instant survives **iff** every displacement is a whole number
> of eighths and `k ↦ kr + e_k·r/d (mod n)` is a bijection. Global isolation forces commensurable
> speeds. `[PROVED — survives_of; commensurable; 12,135 checked]`

**Perfect isolation has no slack** `[PROVED — from 4.2]`. At an instant where the ideal is isolated
every gap is exactly `1/8`, so both flanking runners sit exactly on the threshold and any deviation
toward the subject puts one in the way. That is why an arrangement near the ideal cannot borrow the
ideal's instant and the cascade moves scale instead. It is a fact about the ideal, not a limitation
of the construction.

### 4.5 Families in which Existence holds at once

> **Theorem 4.8 (the ratio condition).** If `d_max ≤ 7·d_min` then `u = 1/8` isolates the subject.
> `[PROVED — ratio_condition; 35,467 checked]`

Every reading lies in `[1, 7]`, at distance at least 1 from `8ℤ`; sharp at `s = 1` and `s = 7`.

> **Theorem 4.9 (wide-gap lemma).** If the two speed gaps adjacent to a runner in speed order are
> each at least the average `W/7`, the runner satisfies 4.8; an extremal runner needs only its one
> gap. `[PROVED — wide_gap_core, wide_gap_end, wide_gap_speeds]`

> **Theorem 4.10 (integral readings).** If every reading is an integer, the spine instant indexed by
> a unit `p` clears a reading `s` exactly when `8 ∤ s`, the same for every `p`.
> `[PROVED — spine_all_or_nothing]`

Consequences: (a) exact progression readings with no slot-sharer give loneliness at `1/(8·d_min)`
and at every spine instant; (b) any runner whose `d_min` divides every disparity reads in integers
and is decided by 4.10; (c) grids with the neighbour hypothesis are case (a), 485 of 485
`[VERIFIED]` — and without that hypothesis a grid need not pass the residue test (8,740 of 17,488
grid runners fail it).

**Census families at the bound** `[PROVED — Cascade, 1,341 theorems]`. Of the 4,413 distinct
seven-disparity arrangements in the shadowing-set census, 1,341 are lonely at their flank's `k = 0`
opening, each a Lean theorem discharged by the integer clearing test.

**Shortcut shares are not the construction's reach.** The source tabulates what each shortcut settles
without running the cascade (the bound ≈ 47–58%, the first lap's four spine instants ≈ 71–76%,
Theorem 4.8 ≈ 28–33%, the residue test ≈ 3–34%, grids ≈ 0.4–15%) and records that rows 3–5 lie
inside row 1, and row 1 is the `r = 1` case of row 2. Reading a shortcut's share as a limit of the
construction is an error logged in the source's Appendix C.

### 4.6 Where the reference first degrades

At the global start `1/(8μ)`, `μ` the smallest speed gap anywhere, every speed gap reads at least
`1/8`, so only the wrap gap can be short; if `W ≤ 7μ` the arrangement is the progression
`[PROVED — arithmetic]`. If `7μ < W ≤ 8μ`, exactly six runners are lonely there
`[VERIFIED — 35 of 35]`. Beyond `W = 8μ` the short gap migrates into the interior.

**Open.** The obligation in the gap frame — that the moving short gap misses both flanks of runner
`i` at some instant — is `[OPEN]`; by Theorem 4.1 and Corollary 6.4 it is Existence for runner `i`,
read in gaps.

---

## 5. No external dependency

v7 cited one ingredient: that for an arithmetic progression the instants of global isolation are
exactly `r/n` with `gcd(r, n) = 1`, `φ(n)` of them per period. **It is derived in Lean at general
`n`** from the framework's own objects (`isolation_iff_coprime`, `card_coprime_eq_totient`,
`instants_on_grid`, `coprime_of_isolation`, `isolation_forces_coprime_grid`), in the general-`n`
line with its own gate. Nothing else is cited: no equidistribution, no result at another order, no
proof sketch.

**The census is one theorem, not four thousand.** Each of the 4,413 census families is the same
statement instantiated. Across all 4,413 only **169 distinct `(e, k)` pairs** are used and a greedy
cover needs **78**. The criterion is `clear_at_opening_of_band`, and the search over `k` is bounded
by `circDist_periodic_of_int_flank` — the verdict at an integer flank `e` repeats with period `e`.

**The nativeness pass, scoped exactly.** It runs per version over that version's *additions*, and is
a claim about what those declarations **cite** — not that the artefact imports nothing. The artefact
imports more where it needs to: `Cascade/Irrational.lean` imports mathlib's irrationality results
deliberately, to exhibit that irrational speeds work.

---

## 6. The cascade

### 6.1 The move

A runner at disparity `d` is **in the way** at `t` when `‖d·t‖ < 1/8`. Its **next opening** after `t`
is the least `(k + 1/8)/d` at or after `t`. The **move** sends `t` to the largest next opening among
the runners in the way at `t`, and leaves `t` fixed if none is. The **cascade** is the sequence of
moves from the bound `1/(8m)`. (`MomentIterationN.inWay`, `nextOpening`, `move`.)

A runner in the way stays in the way until its next opening; the next opening is later than `t`;
each move lands on the opening of one runner in the way `[PROVED]`. There is no candidate set: the
runners in the way at `t` fix the move.

### 6.2 The move changes the scale

    D_0 = d_min,   D_{j+1} = D_j · min{ s/(8N + 1) : |s − 8N| < 1 },   instant = 1/(8·D_final)

stopping when no reading is within 1 of a multiple of 8. The runner that sets a move reads exactly
`8N + 1` at the new scale — one slot away, at exactly one eighth.
`[DERIVED; VERIFIED — 124,488 of 124,488 runners equal the BSM first isolation instant]`

The factor `s/(8N+1)` is below 1 at every step, so scales **decrease** from `d_min`
`[PROVED — from the factor; VERIFIED — 0 of 2,488 shuffled arrangements reach a scale above d_min]`.
This disjointness retires the `SKETCH_v7` "enlarged tier" (which stepped *up* under a ceiling
`D ≤ 7·d_min`) and the "mixed reading" of four spine instants tried in order: by Theorem 6.2(b) the
cascade's fixed point is already the first lonely instant, so a search over candidates cannot
improve on it.

**A step is one dilation** `[PROVED — arithmetic]`. Passing from `D` to `D′` multiplies every reading
by `λ = (8N + 1)/s_x > 1`, where `x` is the setter. The setter lands exactly on `8N + 1`: slot `≡ 1`,
deviation 0, clear at every spine instant of the new scale.

**Slot-sharers.** A runner shares an AP slot at scale `D` when `d/D ∈ 8ℤ`; it is then on the subject
at every spine instant of that scale. Since `d ≤ d_max`, no runner shares a slot at any scale with
`8D > d_max` `[PROVED — arithmetic]`. Live is not the same as lonely. A clear instant `a/(8D)` forces
`D ≤ a·d_min` (`step_ceiling`) `[PROVED]`.

### 6.3 Every lonely instant is matched by an opening

> **Proposition 6.1.** If the subject is lonely at `t`, it is lonely at an opening
> `(⌊e·t⌋ + 1/8)/e` of one of its own disparities `e`, no later than `t`.
> `[PROVED — reading_complete, opening_le; over the reals, every lap]`

So the earliest lonely instant is the bound or one eighth past some lap line of one of the subject's
disparities. This is a statement about the earliest instant, not about every lonely instant: those
fill intervals.

### 6.4 Construction

> **Theorem 6.2 (Construction).** If some step of the cascade is fixed, at `T`:
> (a) the subject is lonely at `T` (`lonely_of_fixed`);
> (b) no positive instant before `T` is lonely (`first_isolation_of_fixed`);
> (c) `T` ends a run of lap-completion zones from the bound, each containing the end of the one
> before, and every such run ending at a lonely instant ends at `T` (`first_isolation_as_zone_run`);
> (d) some runner sits at exactly one eighth, as the nearest ahead or the nearest behind
> (`flank_at_first_isolation`). `[PROVED — Cascade/Iteration.lean]`

The run of (c) is the boundary set read in time order `[VERIFIED — 29,320 of 29,320]`.

### 6.5 Localisation

> **Theorem 6.3 (Localisation).** For every positive instant `s` at which the subject is lonely:
> (a) `s ≥ 1/(8m)`; (b) every step of the cascade is at most `s`, and no move passes a lonely
> instant; (c) `s` is matched by a lonely opening no later than it; (d) the cascade reaches a fixed
> point — below `s` its steps lie in a finite set of openings and a strictly increasing sequence
> cannot stay in a finite set. `[PROVED]`

> **Corollary 6.4.** Equivalent, for every subject: the subject is lonely at some positive instant;
> the cascade reaches a fixed point; a run of lap-completion zones from the bound ends at a lonely
> instant; some flank has a lonely opening.
> `[PROVED — lonely_iff_run_ends; Flanks.lonely_iff_exists_flank]`

Corollary 6.4 is what makes "Existence" and "the conjecture at eight runners, per runner" the same
statement, and it is the hinge the rest of the document turns on.

### 6.6 The subject's own AP instants

> **Proposition 6.5 (drift lines).** At the own AP instant `ν = 8K + r`, runner `l` sits at
> `(r·a_l + ν·e_l)/8` plus `K·a_l` whole laps, and is in the way there iff `r·a_l + ν·e_l` is within
> 1 of a multiple of 8. Valid for every real reading. `[PROVED]`

> **Proposition 6.6 (slot-sharers).** A runner at disparity `8b·m` is in the way at every own AP
> instant, so with such a runner present the subject is lonely at no own AP instant. `[PROVED]`
> The converse **fails** `[VERIFIED — item 33]`, and the repair hypothesis ("every such runner has a
> slot-sharer at a finer scale") is **refuted**: it held for 633 of 1,079 such runners.

> **Proposition 6.7 (own-AP residue rule).** With readings `s_l = c_l/κ`, `h_l = gcd(c_l, 8κ)`,
> `m′_l = 8κ/h_l`, `u_l = c_l/h_l`: runner `l` is in the way at own AP instant `ν` iff
> `ν·u_l mod m′_l` is strictly within `m′_l/8` of 0.
> `[PROVED for the first three clauses — own_ap_residue_rule, slot_sharer_of_m'_eq_one,
> not_inWay_odd_of_m'_even_le; the fourth clause follows but is not separately stated in Lean.
> VERIFIED — 40,000 of 40,000 runners]`

**Own AP instants are not the cascade's instant** `[VERIFIED — item 35]`. Near the wrap,
`(1, …, 7, 9 ± δ)`, the first own AP instant at which runner 1 is lonely recedes like `1/(8δ)` while
its first lonely instant stays at `u = 9/64` for `δ` down to `10⁻⁶`.

### 6.7 Existence — the open statement

> **Existence.** For every arrangement and every runner the cascade reaches a fixed point: it
> arrives at a scale at which no reading lies within 1 of a multiple of 8. Equivalently (Cor 6.4),
> the run of lap-completion zones from the bound ends; equivalently, some flank has a lonely
> opening. **`[OPEN; not stated in either artefact]`**

**The obligation is per runner**, not per arrangement.

**The reduction** `[PROVED — the reduction; Cascade and the specification]`. Composing the
formalised links — relocation is a change of scale, `N` relocations move the nearest reading by at
most a product of lap factors (`nearest_reading_recurrence`), a capped cascade arrives
(`exists_fixed_of_capped`), what it arrives at is the first isolation
(`first_isolation_as_zone_run`), and arriving is equivalent to being lonely somewhere
(`lonely_iff_run_ends`) — leaves one statement:

> **Existence at eight runners is exactly: the cascade's instants are uniformly capped.**
> `LRC.Spec.existence_of_capped` and `capped_of_existence`, both directions.

The converse is stated deliberately. This is the obligation **restated, not weakened** — a cap is no
easier than Existence. Its worth is that what remains is one statement in the framework's own
objects with every other link proved.

**What failure would require** `[PROVED — arithmetic]`. A cascade that never stops lands every step
strictly inside another runner's zone for ever, and each such step forces
`| e − (8w/a)·d | < d_min`: a runner in the way at an opening lies within less than one `d_min` of a
specific rational multiple of the disparity whose opening it is. Failure needs such a relation at
every step, for ever.

**Computations** `[VERIFIED — exact rational arithmetic]`:

- the cascade equals the BSM first isolation instant for **207,464 of 207,464** runners; most moves
  observed 28, at `(27, 70, 107, 137, 159, 188, 344, 393)`;
- **exhaustive sweep**: every integer arrangement `0 = v_1 < … < v_8 ≤ 40` with gcd 1 — 18,564,316
  arrangements, 148,514,528 runner-instances — has a lonely instant for every runner. The
  enumeration is in the **pinned frame `v_1 = 0`**, which is not the framework's; what carries it
  across is that a common shift leaves every disparity, and so every reading, unchanged;
- other orders `n = 5…10`, unpinned, in the stated ranges: 4,025,986 runner-instances, every runner
  lonely, decided by the boundary set, not sampled;
- the largest time ratio `R` found at order 8 is **≈ 11.96** `[EMPIRICAL]`.

Existence is open; these are computations over the stated families.

### 6.8 Hard cases and incommensurate instances

| arrangement | runner | cascade | instant |
|---|---|---|---|
| `(1, 31, 75, 97, 128, 160, 176, 225)` | 1 | 23 moves, `d_min = 30` | `11/256` (`u = 165/128`) |
| `(1, 1975, 5265, 6910, 8737, 9589, 11845, 15135)` | 1 | 22 moves | `73/121072` |
| `(11, 21, 22, 23, 26, 34, 35, 40)` | 35 | 1 move | `25/192` |
| `(27, 70, 107, 137, 159, 188, 344, 393)` | 393 | 28 moves | `49/1872` |
| `(1, 2, π, 4, …, 8)` | π, 4 | Thm 4.8 | `1/(8(4 − π))`, irrational — Lean |
| `(1, 1 + √2/100, 3, …, 8)` | 2 | 2 moves | `(497/8)/(7 − √2/100)`, irrational — exact in `ℚ(√2)` |

`(1, 31, 75, …, 225)`, runner 1, refutes v7's §7.4 Claim **as written**: nothing clears in its first
window, and the runner is first lonely in its second lap. The Claim's wording stopped the cascade at
lap 0.

### 6.9 Flanks

By Proposition 6.1 every lonely instant is matched by a lonely opening of one of the subject's
disparities; call that disparity a **flank**, with openings `(k + 1/8)/e`.

> **Theorem 6.8 (loneliness is a flank statement).** The subject is lonely somewhere iff some flank
> has a lonely opening. At the flank's `k`-th opening only the ratio `ρ_j = d_j/e` enters. An integer
> ratio `A` is clear at every opening iff `8 ∤ A`; otherwise only the fractional part moves.
> `[PROVED — lonely_iff_exists_flank, position_at_flank, integer_ratio_clear_iff,
> fractional_ratio_circDist; 143,520 checks, 0 disagreements]`

> **Theorem 6.9 (one fractional ratio).** A flank at which exactly one ratio is non-integer, with
> every integer ratio not a multiple of 8, has a lonely opening, so the cascade stops.
> `[PROVED — exists_clear_step, lonely_opening_of_one_fractional, stops_of_one_fractional]`

The proof follows the nearest integer to `k·f + c` step by step. **No count is used.**

> **Proposition 6.10 (a pair of fractional ratios).** For a live flank with exactly two non-integer
> ratios: (a) if one lies on the `c`-lattice and the other does not, the flank has a lonely opening;
> (b) if both lie on lattices and shadow the flank between them, each lies on the other's lattice, so
> `c₁ = c₂`. `[PROVED — lonely_opening_of_lattice_and_free, stops_of_lattice_and_free,
> shadowing_pair_cross_lattice; no count used]`

Part (a) is **stronger** than the "rational and an irrational" statement it replaces: it needs only
that the second ratio is off the lattice.

**Withdrawn in v9.3: the former Propositions 6.10 (rational pair) and 6.11 (flank sum criterion).**
`[WITHDRAWN — CORRECTIONS_2026_09_17_v2 §5]` Their arithmetic is not in question; they are
inapplicable **as a discharge**, because both conclude that a lonely opening exists without bounding
where it is. The test is the **index bound, not the tool**: `exists_clear_step` is native and argues
by contradiction, and `exists_fixed_of_lonely` is native and uses pigeonhole. Their credited reach is
also refuted — over 958,256 live flanks the sum criterion fires only at `|J| ≤ 1`, which Theorem 6.9
already decides, and at order 8 it cannot reach `|J| ≥ 4` at all.

**The calculus for a family with a free disparity** `[PROVED — Cascade]`. Three facts, all about
openings and denominators rather than measure: clear openings repeat with period `P`
(`circDist_periodic_of_lattice`); a disparity shadowing every opening of one such class must itself
have denominator dividing `P` (`class_killer_int`, proved from `exists_clear_step` with no density,
equidistribution or rationality input); therefore the shadowing values form a **finite** set, and if
none shadows every clear opening the flank is free for every real value
(`lonely_of_flank_unkillable`).

**Computations at flanks** `[VERIFIED — exhaustive in the stated ranges]`: no runner was found with
every flank shadowed — order 8, every 8-subset of `[1, 20]`, free flanks per runner
`{1: 16, 2: 4,538, …, 7: 116,634}`. Individual flanks are shadowed routinely (2.6% of live ones),
which is why a per-flank criterion cannot discharge a per-runner obligation.

**Open at flanks.** That not every flank of a runner can be shadowed at once — Existence read at
flanks. `[OPEN]`

---

## 6A. The firewall

The framework's bans are part of it.

| ban | content |
|---|---|
| **No stationary frame** | no runner pinned to zero; `v_j − v_i` is what loneliness of `i` means. Pinned-frame enumerations carry a caveat |
| **No window, no bound on when** | evaluation is not confined to a first lap; no result requires a bound on when an instant falls |
| **No search** | the cascade is fixed by the speeds; nothing is picked or predicted |
| **No first-instant demand** | first-ness is a proved property of the output (Thm 6.2(b)), not a requirement |
| **No global clock** | each runner receives its own instant. Two qualifications: the reference progression **is** globally isolated, and the slowest speed defines a cycle |
| **No measure or density** | exact arithmetic and lap-zone geometry only |
| **No covering or emptiness language** | no complement is formed and no set is shown empty; the construction runs a cascade to a named instant |
| **Boundary discipline is mandatory** | open cells and boundary points evaluated separately; touching zones never merged; a cell decided by an interior point |

**Three of these were violated in earlier drafts**, all recorded rather than repaired quietly: the
first-instant demand (v7 §7.1, §7.2, now resolved — first-ness is a property, not a demand); the
pinned frame (v7 §7.4 evidence, standing as a recorded caveat); and **no covering or emptiness
language**, found on 2026-09-17, violated by Propositions 6.10–6.11 and withdrawn in v9.3.

`n > 2k` is **not** counted as a fourth violation: what was refuted is the *framing* of `n > 2k` as
the obstruction to beat, not its proof, which runs on a potential and produces an explicit cap.

**The test, stated once.** The bound lives in the **argument**, not in the shape of the statement.
Every result kept concludes with an unbounded `∃` in Lean, and that is not the defect; their
witnesses carry an index bound. A reader checking this table should read the proof, not the `∃`.

---

## 7. Generalisation

### 7.1 The infrastructure at every n

The cascade and every statement of §6.1–6.6, plus Theorems 6.8–6.9, hold at threshold `1/n` over any
finite set of positive disparities (Theorem 6.9 in Lean for `n ≥ 4`). The Lean statements carry `n`
as a parameter and the order-8 statements are their instances. The spine-pattern paragraph of §6.6 is
the exception: it is stated at order 8.

Of `Construction8`'s 85 theorems, 59 are stated at general `n` and 20 involve no runner count; six
carry `n = 8`, all the zone geometry of §3 and Appendix A.2, with general forms formalised in the
general-`n` line.

**The local restrictions tighten as `n` grows.** The first-zone overlap bound `(n+1)/(n−1)` decreases
towards 1 — `9/7` at `n = 8`, `13/11` at `n = 12` — and the exclusion `2σ/(n−2)` tightens likewise.

### 7.2 Existence with few disparities

| disparities | orders | cascade stops within | theorem | status |
|---|---|---|---|---|
| 2 | every `n ≥ 3` | 1 move | `two_diffs_stop_within_one_move` | `[PROVED — Cascade]` |
| 3 | every `n ≥ 4` | 3 moves | `three_diffs_stop_within_three_moves` | `[PROVED — Cascade]` |
| 4 | every `n ≥ 6` | 7 moves | `four_diffs_stop_ge_six` | `[PROVED — Cascade]` |
| `k` | every `n ≥ max(9, 2^(k−1))` | `2^(k−1) − 1` moves | `stops_slowest_recursion` | `[PROVED — Cascade]` |
| `k` | every `n > 2k` | some step | `stops_when_twice_card_lt` | `[PROVED — Cascade]` |

Five disparities at `n = 6 … 10` remain `[OPEN]`. At `n = 8` with `k = 7` the `n > 2k` row reaches no
order on the diagonal: the seven in-the-way arcs, each of width `2/8`, total `7/4`, so the union
bound on **blocked time** exceeds one and says nothing. **The proof arrives at the covering threshold
by a route that uses no covering** — no zone width or interval length enters it — and the row is kept
on that footing with the coincidence recorded (author's ruling, 2026-09-17).

That `7/4` is a union bound on blocked **time**. It is **not** a statement about the eight gaps on the
track, and the author ruled on 2026-09-18 that quoting it beside a runners-and-gaps discussion is the
wrong object (§D.4, correction 1).

**Order 5** `[OPEN]`. A stronger, sufficient statement is `R < 4`. What is established toward it:

> **`sup R = 31/9` for every arrangement of ratio `d_max/d_min ≤ 26`.**
> `[PROVED — exhaustive certificate over words `(setter, lap)`, each bounded by an exact rational
> linear program]` Attained at the word `(1,2), (2,1), (1,3), (3,1), (2,2), (1,6)` with margin
> `τ = 132/4165`. Since `31/9 < 4`, Existence holds for every such arrangement.

Four qualifications the source states because each has been misread once: the value is **computed**,
not recognised; the bound is on the **ratio** `S = d_max/d_min`, not the spread `W`; the enumeration
is a **relaxation in the sound direction**, so the optimum bounds the true supremum from above; and
the sweep is **flat, not closed** — `31/9` holds at every ratio bound from 10 through 26, but
flatness over a range is not a proof beyond it, and unbounded ratio stays open.

**Order-8 computations are order-8 computations.** The settled-at-once shares of §4.5 and the counts
of §6.7 and §6.9 do not transfer to other orders.

---

## 8. Register: what v9.3 establishes, and what it does not

**Proved, in Lean.**

- **Construction** (Theorem 6.2): a fixed point of the cascade is lonely, first, the end of the run
  of lap-completion zones from the bound, and has a flank at exactly one eighth.
- **Localisation** (Theorems 6.3, 6.8, Corollary 6.4): every lonely instant is at or after every
  cascade step and is matched by a lonely opening no later than it; a lonely instant forces the
  cascade to a fixed point; a runner is lonely somewhere exactly when some flank has a lonely
  opening.
- Every numbered result of §§2–4; §5's derivation of the `φ(n)` instants; the negative results of
  Appendix A.
- Existence in the families of §4.5 and §6.9, and at the orders and disparity counts of §7.2.

**Open.**

| item | where |
|---|---|
| **Existence at order 8** — the cascade reaches a fixed point for every arrangement and runner | §6.7 |
| equivalently, the cascade's instants are uniformly capped | §6.7 reduction |
| equivalently, not every flank of a runner can be shadowed at once | §6.9 |
| equivalently, the moving short gap misses both flanks of runner `i` at some instant | §4.6 |
| how the AP fit feeds each runner's reading | §2.3 |
| five disparities at `n = 6 … 10`; Existence at order 5 | §7.2 |
| the full list of shadowing triples at order 8 | §6.9 |

**Withdrawn in v9.3.** The former Propositions 6.10 (rational pair) and 6.11 (flank sum criterion),
and the §9 ruling that was pending on them. The author's separate ruling of 2026-09-15 — that
pigeonhole and residue counts are admissible **as tools** — is untouched and still stands.

**If Existence held for every runner, the conjecture at eight runners would follow.** It does not
follow from anything in v9.3.

---

## 9. Known defects of v9.3 as frozen

Recorded because the source is frozen and these are not repaired in it.

1. **The §10 digest defect.** v9.3's §10 records **one** SHA-256 string
   (`1af2c9f2…`) in **four** slots: the `Construction8` digest, the `Cascade` digest, the §6.7 JSON
   record and `exhaustive_exact.py`. Only the `Cascade` slot was right. `Construction8` is frozen and
   digests to `578022e0…`, which does not appear in v9.3 at all. The mechanism was a refresh that
   replaced every 64-character hex string rather than the one that had changed. Cascade gate check
   [6] greps for *presence* of the `Cascade` digest, which one correct slot satisfies, so it passed.
   The check was hardened on 2026-09-18 to require the `Construction8` digest as well and to require
   the two to differ; **v9.3 would now fail check [6]**. Corrected in v9.5. Nothing rested on the
   wrong values: no argument cites them, and `Construction8` has its own gate.
2. **The header and §10 disagree on the `Cascade` digest.** The post-freeze header stamp reads
   `d49705d1…`; §10 reads `1af2c9f2…`. The deposited gate run
   (`experiments/n8/cascade_gate_v9_3_v1.out`) matched `1af2c9f2…` at commit `b8ee8b7`.
3. **`[OPEN]` items carried unresolved**, as listed in §8 above.

---

## D. Delta — what changed after v9.3

v9.3 is superseded. This section records every change, so nothing above is read as current.

### D.1 v9.3 → v9.4 (2026-09-17)

| what | v9.3 | v9.4 |
|---|---|---|
| the mirror of Theorem 4.8 | `[DERIVED]`, prose | **Theorem 6.12**, `[PROVED]`, three declarations; `clear_at_bound_of_ratio` states the `k = 0` recovery of 4.8 in Lean |
| the search over openings | unbounded `∃ k` | **Theorem 6.13**: at a whole-number flank the verdict has period `e`, so the search is finite |
| the census | 4,413 declarations, split 1,341 "at the bound" / 3,072 "later" | one criterion at 169 `(e, k)` pairs, greedy cover 78; the split named a **false division** |
| numbered results | 25 | **27** |

Neither new theorem proves Existence. 6.12 widens what is decided and leaves `k` unbounded; 6.13
makes the whole-number case decidable, which decides each disparity set and discharges no universal.

### D.2 v9.4 → v9.5 (2026-09-18)

| what | v9.4 | v9.5 |
|---|---|---|
| the clearance criterion | real-valued, `1/8 ≤ circDist` | **Theorem 6.14**: an integer congruence, `b ≤ a(8k+1) mod 8b ≤ 7b` |
| finiteness | in the opening index only (6.13) | also in the disparity set, at a fixed flank |
| `Construction8` digest | the `Cascade` digest (the §9 defect) | `578022e0…`, computed |
| §6.7 JSON and `exhaustive_exact.py` digests | one string for both | restored from v9.2, marked `[CARRIED]` |
| numbered results | 27 | **28** |

Gate check [6] hardened as described in §9 above.

### D.3 v9.5 → v9.6 (2026-09-18) — **the target amendment**

This is the change that most alters how §6.7 above should be read.

| what | v9.5 | v9.6 |
|---|---|---|
| **the Lean target** | `LRC.Spec.ExistenceAt8`, over `ds : Finset ℝ`, `card ds ≤ 7` | **`LRC.Spec.LonelyRunnerAt8`**, over an injective `v : Fin 8 → ℝ` |
| the obligation | stated on a disparity set | `ExistenceOnArrangements`, `Iff.rfl` to the target |
| new machinery | — | `Cascade/Arrangement.lean`: `inWay_comm`, `lonelyAt_add_const`, `lonelyAt_const_mul`, and the bridge `lonelyAt_iff_lonely_diffSet` |
| `Spec/Target.lean` axiom witness | four declarations | fifteen theorems, every one in the module |
| numbered results | 28 | **28** — none added, dropped or regraded |

**Why the target moved.** `ExistenceAt8` is **sufficient** for the conjecture
(`lonelyRunnerAt8_of_existence`) but is not the same statement: `Finset ℝ` forces decidable
equality, **collapses duplicates** and so destroys the indexing, and `card ≤ 7` admits disparity sets
no arrangement can produce. Most of all, the **arrangement is gone** — gaps, the AP structure, the
coupling across the eight subjects, and "the subject and its two neighbours" are arrangement-level
and are not expressible in `ds` alone.

**Consequence for §6.7 above.** The boxed equivalence "Existence is exactly: the cascade's instants
are uniformly capped" is stated on `ExistenceAt8`, which as of 2026-09-18 is **no longer the target**.
`ExistenceAt8` is retained and still proved sufficient, but it is off the path. v9.6 carries that as
a scope note on the box.

Also proved in v9.6: `exists_lonely_of_card_le_three` — Existence holds outright for at most three
disparities. That this is the **only** excess of the difference-set form over the conjecture is
`[EMPIRICAL — 20,000 sets]`, its construction written down but not formalised.

Nothing in v9.6 proves Existence. Every `[OPEN]` of v9.5 is unchanged and still `[OPEN]`.

### D.4 After v9.6, in the tree, not yet in a manuscript

- **`LRC/Spec/Doors.lean`** (commit `4695eb6`, 2026-09-18) states the obligation's **doors on the
  arrangement**, per subject, and proves each **equivalent** to the obligation for that subject:
  `DoorFlank` (some disparity hosts a lonely opening), `DoorArrives` (the cascade from the subject's
  first reading reaches a fixed point), `DoorCapped` (the instants are bounded above), `DoorFAM`
  (each other runner is in the subject's way at only finitely many steps). Equivalence is the point:
  none is a weaker thing to aim at, and closing any one closes the target (`doors_agree`).
  `DoorThreeLargest` is **not** proved equivalent — it is a strengthening, stated so that what it
  adds is visible. Nothing in the module proves the target.
- **Commit `919b944`** (2026-09-18, landed while this document was being written) carries four
  author corrections, each checked rather than accepted:

  1. **The gap frame is eight gaps, not seven runners.** `Cascade/Arrangement.lean` gains
     `gapAhead`, `gapBehind`, `lonelyAt_iff_gaps` and `gapAhead_add_gapBehind_le_one`: the subject
     owns two of eight gaps summing to 1, so loneliness is a demand on `1/4` of a circle of 1.
     Verified against `LonelyAt` on 30,267 random instants, zero disagreements `[VERIFIED]`. The
     earlier `7/4 > 1` was a union bound on blocked **time**, a different frame (§7.2 above).
  2. **Door 2's move count does not run away.** Measured flat at 14–21 across ranges `[1, 25]` to
     `[1, 400]` `[EMPIRICAL]`. Arrival measured in the nearest runner's own laps, `τ = e·t`, never
     exceeds `33/56 = (4 + 1/8)/7` — **exhaustive over all 170,213 primitive 7-subsets of `[1, 22]`**,
     stable across `[1, 18]`, `[1, 20]`, `[1, 22]`, attained at `(2, 6, 8, 9, 11, 14, 15)`, zero
     non-arrivals `[VERIFIED — exhaustive in the stated range]`. `DoorFirstLap` names the cap `1/e`
     and `lonelyRunnerAt8_of_doorFirstLap` shows it suffices. **The cap is not proved.**
  3. **Door 5 inverts as predicted.** On 35,872 sets the best flank's rank from the large end is 1 in
     35,785, 2 in 84, 3 in 3, never 4 `[EMPIRICAL]`.
  4. **"Largest flank" alone is refuted.** `(2, 3, 5, 7, 8, 13, 16)` has no lonely opening at flank 16
     across all `j < 16`, and needs flank 13 at lap 1, `t = 9/104`, verified termwise
     `[VERIFIED — exhibited]`. `doorThreeLargest_of_doorLargestFlank` keeps the two apart, so the
     refutation touches only the strengthening (`DoorLargestFlank`), not `DoorThreeLargest`.

  See `N8_LEAN_KERNEL_v1.md` §5.4 for the effect on the gate figures.

### D.5 The one-line summary of the delta

Between v9.3 and the present tree, **Existence at order 8 did not move**. What moved is what the
obligation is *stated on* (a disparity set became an arrangement), how much of the search is provably
*finite* (6.13, 6.14), and how many equivalent *doors* onto it are machine-checked (Doors.lean). No
grade was promoted.

---

## References carried from the source

- **Rosenfeld, M. (2025).** The case at eight runners, by computer verification.
- **Sungkawichai, T. and Trakulthongchai, S. (2026).** The computational line to thirteen runners.
- **Barajas, J. and Serra, O. (2008).** *The lonely runner with seven runners.* Electron. J. Combin.
  **15**, R48 — the largest case with a proof that is not computer-assisted.
- **Palelei (2026).** Theorem 3.1(a)–(b), the `φ(n)` law — **no longer cited**; derived in Lean (§5).
