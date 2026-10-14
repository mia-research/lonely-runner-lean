# A Bounding Framework for Eight Lonely Runners

*Version 12, 2026-09-19. Supersedes v11 (2,411 lines), carried forward with **no deletions** — no
numbered result removed, weakened or regraded, every `[OPEN]` item still `[OPEN]`, Existence at
order 8 unchanged and still `[OPEN]`. Numbered results 51 → 63. Four insertions: **§13** (Theorems
13.1–13.12), **Appendix A routes 6–9**, the **v12 paragraphs of §9**, and a **scope paragraph in §7**
recording that §13's artefacts are outside the gated tree.*

**Checked for v12.** A `compile-diff` against v11 was run before promotion (2026-09-19) and reported
a **deletion set of zero lines**: all 51 numbered results present at the same numbers with identical
statement text, all 27 `[OPEN]` sites carried, all 8 retractions carried and none re-claimed, no
grade moved in either direction. It also returned nine findings against the **added** material; all
nine are fixed in this file. The gates of §7 were **not** re-run, because §13 adds nothing to the
gated tree and §7's figures are unchanged.

**T. Palelei.** v11, 2026-09-18. **Supersedes v10**, which held the record earlier the same day.
v10 is carried forward: **no numbered result of it is removed, weakened or regraded**, and every
`[OPEN]` item of it is still `[OPEN]`. **Existence at order 8 is unchanged and remains `[OPEN]`.**
Numbered results 32 → 51.

v11 adds **§4.7** (the cage, Theorems 4.11–4.15), **§6.12** (the clearance criterion, Theorems
6.19–6.22), **§6.13** (the move in closed form, Theorems 6.23–6.24), **§6.14** (the dilation bound,
Theorems 6.25–6.26), **§6.15** (exact blocks, Theorems 6.27–6.29), **§11** (the ratio `R` and what
Existence reduces to, Theorems 11.1–11.3) and **§12** (depth on the profile space, empirical).

**Three things a reader should not miss.**

1. **Theorem 4.8's constant is not about order 8.** Corollary 6.21 derives `S ≤ n − 1 ⟹` clearance at
   `d_min` at every order, from the residue criterion of Theorem 6.19: `n − 1` is one below the first
   multiple of `n`. The constant `7` is a consequence, not an input.
2. **`R` has a closed form with no cascade in it** (Theorem 11.1), and lies in bands
   `[1,7] ∪ [9,15] ∪ …` (Theorem 11.2). So Existence is equivalent to a cascade-free statement, and
   `R < 16` — a *bounded* question in six parameters — would suffice for it.
3. **No bound is proved.** `R < 12` rests on 12.2 million profile evaluations; no route found exceeds
   28 cascade moves. Both are statements about searches. §12 and §11.2 say so in their own words, and
   §11.1 records what a proof would have to supply.

**Checked for v11.** A **compile-diff against v10** (all 32 numbered results carried at the same
numbers and statements, every `[OPEN]` item still open, every withdrawal and version map, and a
**deletion set of zero lines**); its findings are answered and recorded in Appendix B.11. And the
cascade gate, run against **this** manuscript and deposited at
`experiments/n8/cascade_gate_v11_v1.out`:

> **GATE PASS: 4,759 theorems, axiom-clean** (coverage 4,759 of 4,759 on disk), 283 structural,
> 21 modules, no `sorry`, no `native_decide`/`unsafe`/`admit`, the open statement unstated, the
> named irrational coverage present, and check [6] **clean** — this file's recorded figures match the
> tree (4,759 theorems, 21 modules, digest `c54d9843`, commit `c023d10`); 920s.

The gate's closing line is kept here because it is the point: *"Existence at order 8 is NOT proved —
it remains open and unstated."* The v11 development files of §10.1 are **not** in that tree, so the
figures above are unchanged by them, exactly as §7 records.

**A method ruling carried here.** §11.1 argues by covering, which §6A's row bans in terms that are
**formal, not a provenance test**. It is admitted by the **author's ruling of 2026-09-18** that the
ban targets *importing* such an argument, and that one built from the framework's own objects is not
that. §11.1 states the change of scope in full; Theorems 11.1–11.2 do not depend on the ruling.

**Not carried into v11.** A parallel line examined whether the Barajas–Serra prime-filtering
machinery bears on order 8. It is kept out of the manuscript by the author's direction; the record is
in `BS_TRANSFER_v1`, `BS_TRANSFER_v2` and `CEILING_CLAIM_v1`, and **nothing in v11 depends on it.**
Theorem 4.13's gcd invariance is stated and proved here from the framework's own objects; its
prime-power case is classical.

**Two claims examined and not adopted.** A `K ≤ 28` "geometric ceiling" and a piecewise `R < 12`
bound were both proposed as established. Neither is: adding half-spaces contracts a cone without
emptying it, the `89` in the first branch is the empirically observed binding lap, and the second
branch ("six-runner comb capacity") is the covering question itself. Since `doorCapped_iff` is an
`↔`, either would have settled the conjecture. `CEILING_CLAIM_v1` and
`experiments/n8/RCapObligation_v1.lean` carry the analysis; the latter states the obligation in Lean
with the cap as an explicit hypothesis, and proves `RCapped B → DoorCapped → LonelyRunnerAt8`.

**New formal development.** **Twenty-seven theorems in seven files**, all axiom-clean, zero
`sorry`, no `native_decide`. The axiom check is **deposited** at
`experiments/n8/v11_new_axioms_v1.out` — 27 of 27, no `sorryAx`, no error; `slot_gcd` and the
`ExactBlock` theorems need only `propext` and `Quot.sound`. **They live in `experiments/n8/` and are not in the gated tree**, so §7's
figures and the gate counts are unchanged by them. Migrating them into `LonelyRunner/LRC/` is a
decision for v12; until then they are cited as development files with exact reproduction commands in
§10.

```
  DminClearance_v1.lean   7   the clearance criterion, general n
  GridNeighbour_v1.lean   8   the cage; laps invisible
  ExactBlock_v1.lean      5   only colliding disparities block exactly
  MoveRule_v1.lean        2   the move's lap is exact
  DilationBound_v1.lean   2   λ < 9/7
  RBand_v1.lean           1   R mod 8 ∈ [1,7]
  RCapObligation_v1.lean  2   RCapped B → LonelyRunnerAt8 (hypothesis explicit)
```

*Header carried from v10, unaltered:*


**T. Palelei.** v10, 2026-09-18. **Supersedes v9.6**, which held the record earlier the same day.
v9.6 is carried forward: **no numbered result of it is removed, weakened or regraded**, and every
`[OPEN]` item of it is still `[OPEN]`. v10 adds **§6.10** (the obligation with no time and no
iteration, Theorems 6.15–6.17), **§6.11** (two walkers, Theorem 6.18), the
grid-as-progression-plus-whole-laps paragraph in §4.5(c), and **Appendix D** (the seven-flank
margin); it corrects §10's figures and records four withdrawals in **Appendix B.10**.
**Existence at order 8 is unchanged and remains `[OPEN]`.** Numbered results 28 → 32.

**Checked for v10.** A compile-diff against v9.6 (all 24 numbered results, 14 `[OPEN]` items, every
withdrawal record and every caveat carried verbatim; no grade raised; a 12-line deletion set
containing only figure lines). And the cascade gate, run against **this** manuscript and deposited at
`experiments/n8/cascade_gate_v10_v1.out`:

> **GATE PASS: 4,759 theorems, axiom-clean** (coverage 4,759 of 4,759 on disk), 283 structural,
> 21 modules, no `sorry`, no `native_decide`/`unsafe`/`admit`, the open statement unstated, the
> named irrational coverage present, and check [6] **clean** — this file's recorded figures match the
> tree (4,759 theorems, 21 modules, digest `c54d9843`, commit `c023d10`). Tree fingerprint unchanged
> start to end; 903s.

The gate's own closing line is kept here because it is the point: *"Existence at order 8 is NOT
proved — it remains open and unstated."*

*Header carried from v9.6, unaltered:*

**T. Palelei.** v9.6, 2026-09-18. **The manuscript of record.** Supersedes v9.5, which held that status earlier on
2026-09-18. v9.6 records the **target amendment** and the machinery rebuilt on it. The Lean target is now
`LRC.Spec.LonelyRunnerAt8`, the conjecture at eight runners stated on an **arrangement** `v : Fin 8 → ℝ` with `v` injective,
and the obligation is `LRC.Spec.ExistenceOnArrangements`, which is `Iff.rfl` to it — the conjecture itself, not a sufficient
condition. The difference-set form `ExistenceAt8` is retained, still proved sufficient, and is no longer on the path.
`LRC/Cascade/Arrangement.lean` is new and carries the machinery there. See §6.7 and Appendix B.9, and
`ARRANGEMENT_MACHINERY_v1` for the module-level record.

Carried from v9.5: **Theorem 6.14** (the clearance criterion at a whole-number flank is an integer congruence, so the finite
search of 6.13 becomes a finite computation in `ℤ` with no real number in it) and the §10 SHA-256 **correction** — v9.2–v9.4
recorded one digest in four slots, of which at most one could be right; §10 carries the computed values and gate check [6]
tests for the defect. See Appendix B.8.

See `CORRECTIONS_2026_09_17_v2` §5–§6 for the Propositions 6.10–6.11 withdrawal and the audit that bounded it.

**Why the figures below are gated.** They drifted three times on 2026-09-17 — each was computed, Lean was committed, and
nothing noticed. Gate **check [6]** now fails if the theorem count, structural count, module count, digest or artefact commit
disagree with the tree, and the gate fails if the tree moves mid-run. The record is kept because the guard is only
intelligible with it.

Checked for v9.6: the cascade gate (**PASS, 4,748 theorems axiom-clean, every check**, tree fingerprint unchanged
start to end; deposited at `experiments/n8/cascade_gate_v9_6_v1.out`), a full axiom check of `Spec/Target.lean`
(`experiments/n8/v9_6_spec_axioms_v1.lean` and `.out`, all fifteen theorems), and a compile-diff against v9.5, whose seven
findings are answered in Appendix B.9. Carried unchanged from v9.4: the §5 nativeness pass and the review against v1 and v7.

**A counting defect found by the v9.6 gate run, and fixed.** The first run reported 4,749 theorems and then **failed** check
[3] on `Unknown constant Flanks.on`. A `/-- -/` doc comment in `Flanks.lean` had wrapped so that a continuation line began
with the word `theorem`; the extractor counted it as a declaration, and so did the coverage assertion beside it, because both
read raw lines and therefore agreed. Only Lean caught it. The comment is rewrapped and every count in checks [3] and [6] now
reads through a comment stripper. **The declaration count is 4,748, not 4,749** — the figure a proxy had inflated by one.

---

## Abstract

Eight runners start together on a circle of circumference 1 and run at distinct constant speeds. The Lonely Runner
Conjecture at eight runners asserts that each of them is, at some instant, at distance at least `1/8` from every
other. The case was settled by computer verification (Rosenfeld 2025), and the computational line has since reached
thirteen runners (Sungkawichai and Trakulthongchai 2026). No analytic proof is known at eight runners.

We present a local framework and a construction that names instants. For each runner separately it reads the other
runners against an ideal arithmetic progression whose gap is set by the runner and a neighbour, and runs a **cascade**
(the **determinator**): from the instant `1/(8·d_min)` it moves to the latest next opening of the runners in its way,
which is the same as changing to the progression scale at which that runner sits exactly one slot away. The step is
fixed by the speeds; nothing is searched, sampled or picked. The construction and its proofs are real-valued throughout;
for commensurate speeds every quantity is also an exact rational.

Its results are stated as three outcomes in the framework's own objects.
**Construction** — if the cascade reaches a fixed point, the runner is lonely there, no earlier positive instant is
lonely, and that instant is the end of the run of lap-completion zones from `1/(8·d_min)`. **Proved.**
**Localisation** — every instant at which the runner is lonely lies at or after every step of the cascade, and is
matched by a lonely opening of one of its own differences no later than it; so the runner is lonely at some instant
exactly when some **flank** (one of its differences) has a lonely opening. **Proved.**
**Existence** — the cascade reaches a fixed point: it arrives at a scale at which no reading lies within 1 of a
multiple of 8. **Open.** It is proved in several families (§4.5, §6.9), and holds in every case computed, including an
exhaustive sweep of every integer arrangement `0 = v_1 < … < v_8 ≤ 40`.

Two Lean 4 artefacts carry the verification: `Construction8` (85 theorems, frozen since v7) and `Cascade` (4,759
theorems, of which **283 structural** and 4,476 generated census instances — see §7). Both have no `sorry`, and every theorem in both depends on at most `propext`, `Classical.choice` and
`Quot.sound`. The φ(n) count of isolation instants for an arithmetic progression, the one dependency v7 cited, is derived
in Lean. §7 maps every numbered statement to its declaration.

The construction is not specific to eight runners. At every threshold `1/n` Construction and Localisation hold, and
Existence is proved for every arrangement with two differences (every `n ≥ 3`), three (`n ≥ 4`), four (`n ≥ 6`), and
`k` differences whenever `n ≥ max(9, 2^(k−1))` or `n > 2k` (§8). **This paper does not establish Existence at eight
runners.**

---

## 1. Introduction, and the Boundary Set Method

### 1.1 The shift

The framework fixes one runner, forms that runner's own scale from its neighbours, and reads every other runner's position
as a lap count relative to it. Each runner is treated independently: the construction is performed identically and
separately for each of the eight, and no runner is held stationary.

**On frames.** Reading `v_j − v_i` is what "`i` is lonely" *means*; it is not a normalisation that privileges `i`, and
it is not the stationary frame. The construction is carried out for every `i`.

**The ideal is scale-free.** The author (2026-09-15): the arithmetic progression's global isolation is absolute at any
gap; *"the slots are almost scale invariant the ideal transcends any scale"*. The gap is applied by the runner and its
neighbour, so whatever the difference between them the isolation at that gap is determined; ordering the speeds is
bookkeeping for the calculation. In the objects of §6: at every opening of a flank `e` the subject and `e` sit exactly one
eighth apart, which is the progression's spacing at their gap `d_e`, and every other runner is read by its ratio `d_j/d_e`,
where the relocation has put it in that pair's progression (§6.9).

**Real speeds throughout.** Every object the results use — the band identity, drift intervals, the step between scales,
flank openings — is stated and proved over the reals. For commensurate speeds the clearing test also has an exact integer
form (§2.2), and computation is then exact rational arithmetic. The instant is named in both cases; only the arithmetic of
the test differs. Lean proves every runner of `(1, 1 + √2/100, 3, …, 8)` lonely at a named instant; for the second runner the
instant proved is `75√2/4`, a lonely instant later than the cascade's first, `(497/8)/(7 − √2/100) ≈ 8.8930` (§6.8).

### 1.2 The Boundary Set Method

Isolation is decided on the boundary set: the finite, named set of instants at which some runner sits exactly on the
threshold. **Open cells and boundary points are evaluated separately, and touching zones are never merged.** An
in-the-way zone is the set where the circle distance is strictly below `1/8`, so it is an **open** interval and its
endpoints are clear.

**A cell is decided by an interior point, not by its two ends.** The ends of a cell can both be clear while the cell is
an in-the-way zone: at speeds `(0, 12, 14, 16, 30, 35, 38, 53)`, for the runner at 53, the cell `(7/424, 9/424)` has both
ends clear and is the open zone of difference 53. (v7 §1.2 said the ends settle the cell; that is withdrawn.)

In the arithmetic progression `(1, …, 8)` the first runner is lonely exactly at the instants `≡ 1/8, 3/8, 5/8, 7/8 (mod 1)`,
isolated points, every lap. An implementation that closes those brackets, or samples cell interiors as if they were
boundary points, reports the progression's end runners as never isolated — and compiles.

### 1.3 The cascade, and the three outcomes

**The author's statement of the method** (2026-09-14): *"any speed is determined/can be found with reference AP and or
Grid with Dmin and Dmax. So at AP gap of 1, the speed set of 1,2,3.2335,4,5,6,7,8, each runner's isolation can be found
and Dmin gives a proportionate outcome, one resolution … The issue is sometimes speed arrangements don't quite work to AP
times of just 1. So that is where the cascade happens to give you the appropriate AP scale to use."* And (2026-09-15):
*"Not picking. Our cascade work shows it is directed by the speeds in the arrangement."*

Every arrangement is read as an ideal arithmetic progression plus deviations (§2.3). At the runner's own scale `d_min`
the instant `1/(8·d_min)` is the progression's first spine point. When some reading sits in the way there, the cascade
moves to the next scale; the move is fixed by the speeds (§6.2). §6 proves what the cascade arrives at (Construction),
what it cannot miss (Localisation), and states what remains (Existence).

v7 confined its evaluation to the nearest neighbour's first relative lap and made that confinement the open claim. The
framework does not require it (revision-list items 1–3), and there is no window here: the cascade runs over every lap,
and no bound on when an instant falls is a requirement of any result.

---

## 2. Foundations: the local scale, the integer plane, the ideal

### 2.1 The autonomous scale

Let the speeds be distinct and sorted, `v_1 < … < v_8`. For a subject `i`, put `Δ_i = { d_j = |v_j − v_i| : j ≠ i }` and
`d_min = min Δ_i`. The minimum is attained at a **speed-neighbour**, exactly: for the extremal runners it is one-sided,
`d_min(r_1) = v_2 − v_1`, and `|v_8 − v_1|` is the largest difference, never the smallest. Cyclic adjacency (§4) is a
property of the **track**, not of the speed ordering.

The readings are `s_j = d_j/d_min ≥ 1`, with equality possible — in the progression the second runner's readings are
`1, 1, 2, 3, 4, 5, 6`. **All seven readings are evaluated**, the `d_min` reading and the second speed-neighbour's
included: the `d_min` runner can be in the way (§3) and can set a move (§8.2). Omitting the second neighbour changes the
answer: at `(4, 12, 29, 37, 101, 121, 176, 196)` the runner at 37 has `d_min = 8` and a second neighbour at difference 64,
which sits on its lap line at `1/(8·d_min)`; the cascade's instant is `9/512` (`u = d_min·t = 9/64`). Reading five
differences instead of six non-`d_min` ones changes the answer in 3,276 of 48,000 runner-instances.

**Notation used throughout.** `S = d_max/d_min`, the subject's ratio of largest to smallest difference. `W = v_8 − v_1`, the
spread of the speeds. `R = d_min/D_final`, the cascade's instant in units of the bound (§6.2).

**The reading is ratio-native.** Dilating every speed by `k` multiplies every `d_j` and `d_min` alike, so the readings
are unchanged and every instant scales by `1/k`. Every dilate `(k, 2k, …, 8k)` of the progression gives each runner
the readings it has in the progression. The doubled progression `(1, 3, 5, …, 15)` is the progression at `d_min = 2`:
every reading is an integer from 1 to 7, so by Theorem 4.8 all eight runners are lonely at `1/16`.

### 2.2 The `(a, q)` coordinates — the commensurate representation

> **Proposition 2.1.** For `t = a/q` and a relative speed `d` (all natural numbers), `‖d·a/q‖ ≥ 1/n` **iff**
> `q ≤ n·z` and `n·z + q ≤ n·q`, where `z = (d·a) mod q`.  `[PROVED — coord_iff]`

Both conditions are on `ℕ`, so the threshold case is in the statement. This is the exact integer form of the clearing
test for commensurate speeds. *(Checked against a direct test on 121,722 triples, zero mismatches.)*

For real speeds the same test is the **band identity**: at the instant `1/(8D)` a runner of reading `s = d/D` is in the
way iff `s` is within 1 of a multiple of 8 (`MomentIterationN.inWay_at_scale_iff`, every real `D > 0`). The integer form
is its representation when the readings are rational.

**Lap and phase.** A reading's product `s·u` splits as a whole number of laps plus a phase in `[0, 1)` (`lap_and_phase`); the
reading is clear exactly when its phase lies in `[1/8, 7/8]` (`reading_clear_iff`), and for `u ∈ [0, 1)` the circle distance
is at least `1/8` exactly when `u ∈ [1/8, 7/8]` (`window_iff` — a statement about one lap's phase, not an evaluation window).
`[PROVED]`

### 2.3 Every arrangement is an ideal plus deviations

> **Proposition 2.2.** For every arrangement and every real gap `D > 0`, the speeds read as an ideal arithmetic
> progression of gap `D` plus deviations in `[0, D)` (`CascadeRule.reading`, `reading_dev_bounds`); coding the gap as 1
> changes no distance (`gap_is_a_scale`). At the ideal's instant `t = r/(8D)`, runner `j` sits `(idx_j − idx_i)·r`
> eighths from the subject plus its deviation times `r/D` (`position_in_eighths`), and is clear exactly when that is at
> least one eighth from every multiple of 8 (`clear_iff`). A runner with no deviation is clear at every `r` coprime to 8
> unless its index difference is a multiple of 8 (`on_ideal_clear`). Read at gap `d_min`, the nearest runner is on the
> ideal (`nearest_on_ideal_above`, `_below`).  `[PROVED — Cascade/Reading.lean]`

**Spine.** The instants `r/(8D)` with `r` odd are the **spine** of scale `D`; `r = 1` is its first spine point. Read from
the subject's own speed, runner `j` has a whole **slot** `a_j = idx_j − idx_i` and a **deviation** `ε_j ∈ [0, 1)` in gap units,
and sits at `r·a_j + r·ε_j` eighths at spine instant `r`.

The progression is the reference; the deviations are what the cascade reads.

**Fitting the arrangement between the AP locations.** `[OPEN — how the fit feeds each runner's reading]` The author's
statement (2026-09-14): *"Its about fitting them in between the spaces they can be, so for ap r1 can be 0 to <2, r2 can be
[1] to <3, their is overlap between them."* Stated exactly: against a progression of gap `D`, runner `k` may sit strictly
between its neighbours' locations, `(A_k − D, A_k + D)`, and adjacent bands overlap by one gap; the arrangement **fits** when
every runner is inside its band. Anchoring at the slowest and fastest speeds makes the gap `W/7`. `(1, 31, 75, 97, 128, 160,
176, 225)` fits at gap 32 with deviations `0, −2, 10, 0, −1, −1, −17, 0`; `(1, 2, 3, 4, 5, 6, 7, 100)` does not. The fit
alone does not give every runner an instant `r/(8D)` of the fitted progression `[VERIFIED — exact]`: of the 45,568
eight-subsets of `[1, 20]` with gcd 1 that fit, 34,462 give every runner one; of the 80,357 that do not fit, 58,800 still do.
And `(1, 2, 3, 4, 5, 6, 7, 9)` fits while the runner at 2 has no instant `7r/64`, though its own `d_min` reading isolates it
at `1/8` (Theorem 4.8). The fitted progression is the ideal; the runner's instant is read at its own `d_min`. How the fit
decides which runners then need the cascade is the step still to be written down (revision-list item 24,
`experiments/n8/ap_fit_spread_v1.py`).

---

## 3. Local restrictions: the clear-interval bound

Fix a subject and a reading `s`. The instants at which that runner is in the way are the open zones
`((8k − 1)/(8s), (8k + 1)/(8s))` in the lap coordinate `u = d_min·t`, one per lap `k` of the reading.

> **Proposition 3.1.** Each zone has width `1/(4s)`, and consecutive zones are separated by a closed clear interval of
> width `3/(4s)`.  `[PROVED — blocked_width, clear_width]`

Closing the zones would put `u = 1/8` in the way for `s = 7`, and the progression's spine would vanish.

> **Corollary 3.2 (contiguous reach).** A single reading is in the way contiguously for at most `1/(4s)`.

> **Proposition 3.3 (single-reading exclusion).** Let `σ` be the smallest reading other than the baseline `s = 1`. No
> zone of a single reading `s′ ≥ σ` other than the baseline contains a clear interval `[(8k+1)/(8σ), (8k+7)/(8σ)]` of `σ`:
> its zones are no longer than `1/(4s′) ≤ 1/(4σ)`, and the clear interval is `3/(4σ)` long.
> `[PROVED — no_solo_closure, solo_closure_forces_smaller]`

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

**Perfect isolation has no slack.** At an instant where the ideal is isolated every gap is exactly `1/8`, so both runners
flanking the subject sit exactly on the threshold. Any deviation that moves either flank toward the subject puts it in the
way. That is why an arrangement near the ideal cannot borrow the ideal's instant and the cascade moves scale instead (§4.6).
It is a fact about the ideal, not a limitation of the construction. `[PROVED — from 4.2]`

> **Theorem 4.3.** `n` positions in `[0, 1)`, pairwise at circle distance at least `1/n`, are in sorted order an
> arithmetic progression of step `1/n`.  `[PROVED — grid_of_pairwise]`

> **Corollary 4.4.** The number of simultaneously lonely runners lies in `{0, …, 6} ∪ {8}`; it is never 7.  `[PROVED —
> lonely_ne_pred; also exhaustive over all 12,870 eight-subsets of [1,16]]`

### 4.3 The reference instant

Write the speeds as `A + e` against a progression `A_k = v₀ + k·d`, and fix `t = r/(nd)` with `gcd(r, n) = 1`.

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

### 4.5 Families in which Existence holds at once

Theorems 4.8–4.10 and consequences (a)–(c) give classes of runners whose first cascade step is already clear. §6.9 adds
classes decided at a flank's openings.

> **Theorem 4.8 (the ratio condition).** If `d_max ≤ 7·d_min` then `u = 1/8` isolates the subject.  `[PROVED —
> ratio_condition; 35,467 checked]`

Every reading lies in `[1, 7]`, at distance at least 1 from `8ℤ`; sharp at `s = 1` and `s = 7`.

**The census families that clear at the bound.** `[PROVED — Cascade, 1,341 theorems]` Of the 4,413 distinct seven-difference
arrangements arising from the shadowing-set census (§6.9), **1,341 are lonely at their flank's bound**, the `k = 0` opening —
Existence holding at once, in this section's sense. Each is a Lean theorem discharged by the integer clearing test
(`Flanks.clear_of_residue_band`, Proposition 2.1 in integers): the arrangement is lonely at that opening exactly when every
`d·(8k+1) mod 8e` lies in `[e, 7e]`, which is decidable arithmetic, so each family closes by `decide`
(`PinnedBatch1–4`). The remaining 3,072 are decided at a later opening and are read in §6.9.

That `1,341/4,413 = 30.4%` sits near the `31%` quoted above for Theorem 4.8 is a **coincidence of two different
populations** — census families against random arrangements — and is not evidence about either.

> **Theorem 4.9 (the wide-gap lemma).** If the two speed gaps adjacent to a runner in speed order are each at least the
> average `W/7`, where `W` is the spread, the runner satisfies 4.8. An extremal runner needs only its one gap.
> `[PROVED — wide_gap_core, wide_gap_end, wide_gap_speeds]`

Contraposed: if 4.8 reaches no runner, no two above-average gaps are adjacent and none is at either end, so there are at
most three. *(Exhaustive over all 24,310 eight-subsets of `{0,…,16}`.)*

4.9 is the case in which a runner's own `d_min` already reaches `W/7`; it says nothing about progressions of gap `W/7`
for runners whose `d_min` is smaller.

> **Theorem 4.10 (integral readings).** If every reading is an integer, the spine instant indexed by a unit `p` clears a
> reading `s` exactly when `8 ∤ s`, the same for every `p`.  `[PROVED — spine_all_or_nothing]`

**Consequences.** (a) **Exact progression readings with no slot-sharer.** When every difference is a whole multiple of
`d_min` and none is a multiple of `8·d_min`, the subject is lonely at `1/(8·d_min)`, and at every spine instant. (Run at
order 8: 7,950 random seven-reading arrangements from `2…60` without a slot-sharer, every one clear at the bound; with a
slot-sharer the cascade's `R` stayed at most `5/2` in 12,050.) (b) **The residue test, beyond grids.** Any runner whose
`d_min` divides every difference reads in integers and is decided by 4.10; 7,112 of 7,152 such cases checked were not grids.
(c) **Grids.** Call the arrangement a grid when its reduced residues form a complete system mod 8, and let `g` be the gcd of
its differences. If every runner has a neighbour at distance exactly `g`, every runner has `d_min = g` and no difference is a
multiple of `8g`, so this is case (a): every runner is lonely at `1/(8g)` (`GRID_THEOREM_v1`; 485 of 485, including dilates).
Without the neighbour hypothesis a grid need not pass the residue test: runner 1 of `(1, 3, 5, 7, 10, 12, 14, 16)` fails it
and all four `u = r/8`, `r ≤ 7`, and is lonely at `t = 1/8`; over grids with differences at most 24, 8,740 of 17,488 grid
runners fail the residue test (revision-list item 14).

**What a grid is to an arithmetic progression: whole extra laps.**  `[PROVED — WHICH_GRIDS_ISOLATE_v1 §1–§2]`
Reduce by `g`, so the speeds are integers `u_i` of gcd 1, and split each as `u_i = π(i) + n·q_i` with
`π(i) = u_i mod n`. At `t = p/(n·g)` runner `i` sits at `u_i·p/n`, and

    u_i·p  =  π(i)·p  +  n·q_i·p ,      so the position is  (π(i)·p mod n)/n  plus  q_i·p whole laps.

**The `q` part contributes `q_i·p` complete revolutions and vanishes mod 1.** So a grid is an
arithmetic progression whose runners have lapped the circle some whole number of extra times, and
`{0, 1, …, n−1}` is simply the representative with `q = 0`. Hence the criterion: **global isolation
holds iff the reduced speeds form a complete residue system mod `n`**, and it then occurs at exactly
`φ(n)` instants per period — the spread is invisible, living entirely in `q`.
`[VERIFIED — exhaustive, 11,258 sets at `n = 4…7`, 0 disagreements against direct evaluation]`

**And it says exactly when global isolation fails: when two runners share a residue.** Sharing a
residue means their disparity is a multiple of `n·g` — the pair slot-share (Prop 6.6). So the
arrangement-level failure and the subject-level slot-sharer are **one condition**, and the cure in
both cases is a scale at which "whole cycles" becomes "whole cycles plus one slot" (§6.10). Worked:
`(11, 21, 22, 23, 26, 34, 35, 40)` has residues `[3,5,6,7,2,2,3,0]`, collisions at 2 and 3, and the
four runners not lonely at any instant of scale `g = 1` are exactly `26, 34` and `11, 35`.
`[VERIFIED — exact]`

**The integer-scale layer reaches about half.** Taking the scale `g` and testing "no `d/g` is a
multiple of 8" — Theorem 4.10, the grid and progression families together — settles **40–48%** of
subjects (`ap_grid_layer_v1`, speeds in `[0,20)`, `[0,60)`, `[0,200)`). The rest need a scale that
divides nothing, which is §6.10's object.

**Integral readings recur each lap.** If every reading is an integer and 1 is among them, the positions repeat with period
1 in `u`, so any lonely instant has a copy with `u ∈ [1/8, 7/8]` (`localisation_free`). `[PROVED]` This is a periodicity
fact; it gives no class of runners by itself.

**How many runners each shortcut settles at once** (v7's first-lap measurements, ranges across its populations):

| shortcut | condition | runners settled at once |
|---|---|---|
| the bound, `u = 1/8` | no reading within `1` of a multiple of `8` | ≈ 47–58% (49.5% in the development record) |
| the first lap's four spine instants `u = r/8`, `r ∈ {1, 3, 5, 7}` | the same with `r·s` in place of `s` | ≈ 71–76% |
| Theorem 4.8 | `d_max ≤ 7·d_min` | ≈ 28–33% |
| the residue test, (b) | `d_min` divides every difference, none a multiple of `8·d_min` | ≈ 3–34% |
| grids with the neighbour hypothesis, (c) | a special case of the row above | ≈ 0.4–15% |

The nesting is arithmetic: `d_max ≤ 7·d_min` puts every reading in `[1, 7]`, hence clear at `u = 1/8`; the residue test is the
same band condition with integral readings. So rows 3–5 lie inside row 1, and row 1 is the `r = 1` case of row 2; measured,
rows 3–5 add nothing beyond row 2. v7 recorded that testing only `1/8` understated the progression's own spine.

**These percentages are not the construction's reach.** They count what a shortcut settles without running the cascade. The
cascade gave a lonely instant for every runner computed (§6.7); reading a shortcut's share as a limit of the construction
is an error recorded in Appendix C.

### 4.6 Where the reference first degrades

At the **global start** `1/(8·μ)`, `μ` the smallest speed gap anywhere, every speed gap reads at least `1/8`, so the only
gap that can be short is the wrap gap between `r_8` and `r_1`; and if `W ≤ 7·μ` the seven speed gaps, each at least `μ`
and summing to `W`, all equal `μ`: the arrangement is the progression. `[PROVED — arithmetic]` If `7·μ < W ≤ 8·μ`,
exactly six runners are lonely there, the short pair being `(r_1, r_8)`. `[VERIFIED — 35 of 35; both regimes exhaustive
over v_8 ≤ 20]` Beyond `W = 8·μ` the short gap moves into the interior as runners cross; between crossings every gap changes
linearly, so a short gap lengthens where speeds separate and a gap shortens only where runners cross. Of the 77,400
arrangements `0 = v_1 < … < v_8 ≤ 20` with gcd 1, 77,364 are of this migrated kind; per runner the families of §4.5 still
settle large fractions (Theorem 4.8 alone about 31% of runners in random arrangements). `[VERIFIED — development record]`
That enumeration fixes the slowest speed at 0, a common shift of every speed that leaves every difference, and so every
reading, unchanged; it is not the framework's frame (§6A).

**The obligation in the gap frame.** `[OPEN]` Once the short gap has left the wrap: the moving short gap misses both flanks of
runner `i` at some instant. The development record states it with "at some `u ≤ 7/8`"; that bound is the first-window
restriction withdrawn in revision-list items 1–3, and is not part of the obligation here. By Theorem 4.1 and Corollary 6.4
this obligation for runner `i` is Existence for runner `i`, read in gaps.

**Perturbations of the progression are read by `d_min`.** `[VERIFIED at the ε shown]` Each runner's bound moves to its
own `1/(8·d_min)`. A **one-sided** perturbation creates a far-end runner on its lap line: `r_8` of `(1 − ε, 2, …, 8)` and
`r_1` of `(1, …, 7, 8 + ε)` are both lonely at `u = 3/8` for `ε ∈ {1/40, 1/10, 1/4}`, the latter at an isolated point
pinched between the positions `9/8` and `15/8` of the readings 3 and 5 — a boundary point, evaluated separately (§1.2).
A **symmetric** perturbation `(1 − ε, 2, …, 7, 8 + ε)` is absorbed: the end runners' `d_min` grows to `1 + ε` with
`d_max = 7 + 2ε ≤ 7·(1 + ε)`, so 4.8 gives both at `u = 1/8` (`ε ∈ {1/10, 1/4}`). The reference state degrades by moving its
instant, not by losing it (§4.2, no slack).

---

### 4.7 The cage: which runners can ever bind

At a grid instant `t = p/(n·g)` runner `j` sits at `(π j − π i)·p / n` relative to the subject, where
`π` is the residue of the reduced speed. Two facts follow, and both are about the residue offset
alone.

**Theorem 4.11 (position is a residue).** *`gridPos n p d = ((d·p) mod n)/n`, so a relative position
at a grid instant depends on the disparity only through `d mod n`.* `[PROVED]` `GridNeighbour.gridPos_eq`,
`gridPos_congr`.

**Theorem 4.12 (whole laps are invisible).** *Two arrangements with the same residues and any
whole-lap parts present the subject with the **identical** position function. Every selection stated
in it — nearest ahead, nearest behind, the whole cyclic order — agrees.* `[PROVED]`
`laps_invisible`, `neighbour_laps_invisible`. Verified 16,000 of 16,000.

This is why the target had to be stated on an arrangement (§6.7, Appendix B.9): the structure here is
arrangement-level and is not expressible against a difference set, which fixes `|offset|` but not
offset. Measured: with ties excluded, `ds` fails to fix the ordered neighbour pair 38.7% of the time
and the unordered pair 34.2%.

**Theorem 4.13 (the cage).** *As the instant `p` runs over the units mod `n`, the slot `(d·p) mod n`
keeps the same gcd with `n`. Hence a runner whose offset shares a factor with `n` is confined:*
```
      gcd(d,n)/n  ≤  position  ≤  1 − gcd(d,n)/n .
```
`[PROVED]` `slot_gcd`, `slot_ge`, `gridPos_caged`, stated for arbitrary `n`. (The prime-power case of
the gcd invariance is classical; the statement here is general and is what the corollaries use.)

**Corollary 4.14 (`n = 8`).** *An even residue offset is caged at quarter distance or beyond, at
every grid instant, in every arrangement.* `[PROVED]` `even_offset_caged`. Exhaustively, the closest a
runner at offset `d` ever comes is `2^ν₂(d)/8`:

```
    d :  1     2     3     4     5     6     7
        1/8   1/4   1/8   1/2   1/8   1/4   1/8
```

So **offsets 2, 4 and 6 can never be the binding pair at a grid instant** — the grid-instant problem
is a four-runner problem — and offset 4 is antipodal at every one of them.

**Corollary 4.15 (the neighbour rule).** *At the instant `p/8` the binding pair is the runners at
residue offset `±p`, using `p⁻¹ = p` in the Klein group `(ℤ/8)ˣ`.* `[PROVED — in the text]` from
Theorem 4.11: the runner ahead is the one minimising `(Δ·p) mod 8`, which is `1` exactly when
`Δ ≡ p⁻¹`. `[VERIFIED — 12,800 of 12,800 on grids]` as a check, not as the ground.

**The perturbation budget.** Read as slack, a runner at offset `d` may have its speed moved by
`min(d, 8−d) − 1` in reduced units at `p = 1` — `0, 1, 2, 3, 2, 1, 0` — derived exactly and
reproduced by direct simulation. An arrangement's rigidity at a grid instant is carried entirely by
the two residue-adjacent runners; the residue-antipodal one may move by 3 with no effect.

---

## 5. No external dependency

v7 cited one ingredient: that for an arithmetic progression the instants of global isolation are exactly `{δt} = r/n`
with `gcd(r, n) = 1`, and that there are `φ(n)` of them per period (Palelei 2026, Theorem 3.1(a)–(b)). **It is derived
in Lean at general `n`** from the framework's own objects, in `ConstructionN/Instants.lean`:

| declaration | says |
|---|---|
| `isolation_iff_coprime` | integer speeds distinct mod `n` (the progression's residues) are all isolated at `p/n` iff `gcd(n, p) = 1` |
| `card_coprime_eq_totient` | there are `φ(n)` such `p` in `[0, n)` |
| `instants_on_grid`, `coprime_of_isolation`, `isolation_forces_coprime_grid` | for integer speeds with gcd 1, global isolation at any real `t` forces `t = p/n` with `gcd(n, p) = 1` |

That development is outside the two artefacts of §7 (it sits in the general-`n` line with its own gate). The progression's
four instants `1/8, 3/8, 5/8, 7/8` in each lap also follow from Theorem 4.3 alone: the eight points `j·t` are pairwise at
least `1/8` apart. Nothing else is cited: no equidistribution, no result at another order, no proof sketch.

**The census is one theorem, not four thousand.** Each of the 4,413 census families is the *same* statement — every
difference in the band at some `(flank, opening)` — instantiated. Across all 4,413 only **169 distinct `(e, k)` pairs** are
used, and a greedy cover needs **78** (`experiments/n8/census_unification_v1`). The criterion is `clear_at_opening_of_band`;
the search over `k` is bounded by `circDist_periodic_of_int_flank`, which says the verdict at an integer flank `e` repeats
with period `e`, so openings `0 … e−1` carry every verdict the flank can give — confirmed on the census, 13,239 of 13,239,
with no instance using `k ≥ e`.

**So §4.5 and §6.9's split is a false division.** "1,341 clear at the bound" against "3,072 decided at a later opening" reads
as two phenomena; it is one criterion evaluated at different `k`. The counts are correct and are verified here against the
files, but they divide by an artefact of the search, not by anything in the mathematics.

**What the theorem count is and is not.** 4,476 of the 4,759 — **94%** — are the census: one generated
theorem per arrangement, each the *same* one-line application of `lonely_of_band_list` with a different seven-element list,
discharged by `norm_num` and `decide`. They are a machine-checked enumeration, not 4,476 distinct results. The artefact's
mathematical content is the **283 structural** theorems; the census is evidence of a different kind, and §4.5 and §6.9 report
it as such (1,341 clear at the bound, 3,072 at a later opening, verified here against the files). The gate prints the split on
every run so the headline figure cannot be read as 4,759 independent facts.

**v9.3's 27 additions were checked against that claim too** (`experiments/n8/nativeness_v9_3_v1`), and 26 of them use only
`Int.fract` and its lemmas, `Int.cast_abs`, `Int.mul_ediv_add_emod`, `Fact.out` and ordinary order and field algebra.
**The scope of this pass, stated exactly, because it is easy to over-read.** It runs per version over that version's
*additions*, and it is a claim about what those declarations **cite** — not a claim that the artefact imports nothing. The
artefact has always imported more where it needs to: `LRC/Cascade/Irrational.lean` imports `Mathlib.NumberTheory.Real.Irrational`
and `Mathlib.Analysis.Real.Pi.Irrational` **deliberately**, to exhibit that irrational speeds work (§6.8).

One v9.3 addition, `Flanks.off_lattice_of_irrational_ratio`, uses `Irrational`. That name is a *definition*
(`x ∉ Set.range ((↑) : ℚ → ℝ)`), not a theorem, and Lean's own dependency list confirms the proof cites exactly one constant
from that import — `Irrational` itself. **No external result enters.** The mathematical content sits in
`off_lattice_of_not_ratio`, which states the hypothesis in the framework's own words, needs no import, and is *stronger*: a
rational ratio whose denominator does not divide `P` satisfies it too, which is what `shadowing_pair_cross_lattice` uses.

**The corollary is kept on purpose, and pinned.** The general theorems are stated on the framework's object — "off the
`P`-lattice" — which does not contain the word *irrational*, and a reader searching for that word could mistake its absence
for a gap. Irrational speeds are **not an exception anywhere in this framework**: the cascade is real-valued throughout,
`class_killer_int` covers rational and irrational ratios in one case with no rationality input, and §6.8 tabulates worked
irrational arrangements verified in Lean. Check [5] of the cascade gate fails if any of those named declarations is removed,
so the coverage cannot lapse silently.

**The v9.2 additions were checked against that claim, declaration by declaration.** Every non-local identifier they use is
`Int.fract` and its four lemmas, `Nat.cast`, `Nat.cast_sub`, `Nat.div_add_mod`, `Nat.mul_pos`, `List.mem_map`,
`List.mem_toFinset`, `Finset.eq_empty_or_nonempty` and `Function.iterate_add_apply` — the fractional part, integer division,
casts, membership, iteration. Nothing from measure theory, topology, filters or number theory appears in them, and no
statement of equidistribution, Weyl, Kronecker or Dirichlet type is used in any of them. (v9.2 noted here that Propositions 6.10–6.11, proved in the text and not
formalised, used Dirichlet's pigeonhole and a residue count, with the ruling on whether they sit inside the framework still
pending. Both are **withdrawn in v9.3** and the ruling with them; what replaces 6.10 is formalised and uses no count. The
author's ruling of **2026-09-15**, that pigeonhole and residue counts are **admissible as tools**, stands and is unaffected:
`CORRECTIONS_2026_09_17_v2` §5 confirms it from the other side, since `exists_fixed_of_lonely` uses pigeonhole and is native.
What is withdrawn is the separate §9 ruling on whether Propositions 6.10–6.11 sit inside the framework, which lapses with the
propositions. The test that settles it is whether an argument **bounds where the instant is**, not which tool it uses.) `exists_clear_step`, on which the shadowing argument of
§6.9 rests and which replaced an appeal to the density of an irrational orbit, uses **no non-local identifier at all** in its
eighty-four lines: it follows the runner's successive positions and compares consecutive nearest integers. The new modules
import only `Cascade` and `ConstructionN.LemmaPass`; none refers to a result at another order.

---

## 6. The cascade

Throughout, the subject has positive speed differences `ds`, nearest difference `m = d_min`, threshold `1/8`.

### 6.1 The move

> **Definition.** A runner at difference `d` is **in the way** at `t` when `‖d·t‖ < 1/8`. Its **next opening** after `t` is
> the least `(k + 1/8)/d` at or after `t`. The **move** sends `t` to the largest next opening among the runners in the way
> at `t`, and leaves `t` fixed if none is. The **cascade** — the determinator — is the sequence of moves from the **bound**
> `1/(8m)`. (`MomentIterationN.inWay`, `nextOpening`, `move`.)

A runner in the way at `t` stays in the way until its next opening (`inWay_until_opening`), and the next opening is later
than `t` (`lt_nextOpening`). Each move lands on the opening of one runner in the way (`move_eq_self_or_opening`). There is no
set of candidates: the runners in the way at `t` fix the move.

### 6.2 The move changes the scale

The bound is the first spine point of the progression of gap `m`. At the instant `1/(8D)` a runner of reading `s = d/D`
is in the way iff `|s − 8N| < 1` for some `N` (`inWay_at_scale_iff`), and its next opening is the first spine point of the
progression of gap `d/(8N + 1)` (`nextOpening_at_scale`). So the cascade is a recursion on the scale, fixed by the speeds:

    D_0 = d_min,    D_{j+1} = D_j · min{ s/(8N + 1) : |s − 8N| < 1 },    instant = 1/(8·D_final),

stopping when no reading is within 1 of a multiple of 8. The runner that sets a move reads exactly `8N + 1` at the new
scale — one slot away, at exactly one eighth. `[DERIVED; VERIFIED — 124,488 of 124,488 runners equal the BSM first
isolation instant]` The moves do not multiply a common factor: each step resets to `D′ = d/(8N + 1)` (at `(1,…,6,8,9)`,
runner 1, the chain `(8, N = 1), (7, N = 1)` ends at `D_final = 7/9`). Scales are real and decrease from `d_min`.

**The enlarged tier, and why it is not here.** `SKETCH_v7` §7c gives the cascade as three tiers tried in order — AP at the
gcd `g`, grid at the runner's `d_min`, and an **enlarged** step, *"some `D` beyond those"*, stepping up until the lattice is
usable, under the ceiling `D ≤ 7·d_min`. The recursion above is not that third tier renamed: it runs the other way. Its
factor `s/(8N+1)` is below 1 for every step, so its scales decrease from `d_min` and never enter `d_min < D ≤ 7·d_min` at
all. `[PROVED — from the factor; VERIFIED — 0 of 2,488 shuffled arrangements reach a scale above `d_min`,
`experiments/n8/scale_recursion_check_v1.py`]` The two are disjoint.

The tier is nonetheless **superseded, and provably so, rather than dropped.** By Theorem 6.2(b) the fixed point is the first
lonely instant, and by Corollary 6.4 the cascade fails to reach one only when the subject has no lonely instant at all. So
any instant a search over enlarged steps could return is a lonely instant, hence at or after the cascade's — and when the
cascade returns nothing there is nothing for that search to find. A tier tried in order can improve on a determinator that
already lands on the first isolation only by finding it sooner, and Theorem 6.2(b) forbids that. The word is absent from
this manuscript for that reason and not by oversight.

The same argument retires `SKETCH_v7` §7b's **mixed reading** — the four spine instants `t = p/(8·d_min)`, `p ∈ {1,3,5,7}`, tried in
order, the lower runners taking `p = 1` and a tight pair taking `p = 3`. Its mechanism is Theorem 4.10: the four points
stand or fall together exactly when the reading is integral, and separate otherwise. On its own worked example
`(10, 65, 101, 126, 159, 222, 256, 271)` it gives runners 256 and 271 the instant `t = 1/40`; the cascade gives them
`9/1040` and `17/1648`, both earlier. A search over four candidates cannot beat a determinator that lands on the first.

**A step is one dilation.** `[PROVED — arithmetic]` Passing from `D` to `D′` multiplies every reading by the same factor
`λ = D/D′ = (8N + 1)/s_x > 1`, where `x` is the setter. The setter lands exactly on `8N + 1`: slot `≡ 1`, deviation 0, clear at
every spine instant of the new scale (an odd reading `8N + 1` is never within 1 of a multiple of 8 at odd `r`). Every other
reading moves by `(λ − 1)·s_y = g·(d_y/d_x)`, where `g = 8N + 1 − s_x ∈ (0, 2)` is how far the setter sat below `8N + 1`, and the
ratios `d_y/d_x` are fixed by the speeds. (`A4_SPINE_BLOCKING_v1` §4.)

**Slot-sharers at a real scale.** A runner shares an AP slot with the subject at scale `D` when `d/D ∈ 8ℤ`; it is then on
the subject at every spine instant of that scale. Since `d ≤ d_max`, no runner shares a slot at any scale with `8D > d_max`.
`[PROVED — arithmetic; the earlier form, revision-list item 21: every slot multiple is at most `W/(8g)`, `g` the gcd of the
differences, so a gap with `8D > W` is live for every runner]` The integer form: step `D ∈ ℕ` is dead for difference `d ∈ ℕ` iff `d = 8k` with `D | k` (`dead_iff`),
divisors of dead integer steps are dead (`dead_downward`), and a live integer step always exists (`exists_live`). `[PROVED]`
These are statements about a scale, not about the cascade's path: the cascade's scales are fixed by the recursion above and
generally not integers. Live is not the same as lonely: at `(1, 2, 3, 4, 5, 6, 7, 9)`, at scale 2, the runner at 2 has no
lonely spine instant `r/16`, its odd differences `1, 1, 3, 5, 7` taking all four residue pairs mod 16. A clear instant
`a/(8D)` forces `D ≤ a·d_min` (`step_ceiling`). `[PROVED]`

**A single slot-sharer and the next spine.** For integer readings, with a slot-sharer at reading `S_b` (a multiple of 8), at
`u = p/8 + 1/(8·S_b)` the slot-sharer sits exactly at one eighth (`blocked_lands_on_threshold`), and every integer reading
`s ≤ S_b` with `s·p mod 8 ∈ [1, 6]` stays clear there (`unblocked_stays_clear`). `[PROVED]` When the slot-sharer is the only
runner in the way at `u = p/8`, this is a §6.1 move; readings with `s·p mod 8 = 7` are not covered by the statement.

### 6.3 Every lonely instant is matched by an opening

> **Proposition 6.1.** If the subject is lonely at `t`, it is lonely at an opening `(⌊e·t⌋ + 1/8)/e` of one of its own
> differences `e`, no later than `t`.  `[PROVED — reading_complete, opening_le; over the reals, every lap]`

So the earliest lonely instant is the bound or one eighth past some lap line of one of the subject's differences
(Theorem 6.2(d) gives the same for the cascade's fixed point). This is a statement about the earliest instant, not about every
lonely instant: those fill intervals. `[PROVED — Proposition 6.1 at the earliest instant: the opening it supplies is positive
and no later, so it is that instant; the bound is the opening k = 0 of d_min]` The development record checked it on 91,456 of
91,456 runners; the generating script is not identified there. v7's check of its own procedure: 4,800 of 4,800 instants it
gave were openings, and across `n = 5…11` none was the closing end of a clear stretch. The finite form — the left end of a
closed interval or some zone's right end is clear whenever any point is — is `exists_clear_candidate` (general `n`; the name
predates this terminology).

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
> cascade reaches a fixed point; a run of lap-completion zones from the bound ends at a lonely instant; some flank has a
> lonely opening. `[PROVED — lonely_iff_run_ends; Flanks.lonely_iff_exists_flank]`

### 6.6 The subject's own AP instants

With `d_l = (a_l + e_l)·m` — AP index `a_l ∈ ℤ`, deviation `e_l` — the instants `ν/(8m)`, `ν = 1, 2, …`, are the subject's own
AP instants.

> **Proposition 6.5 (drift lines).** At the own AP instant `ν = 8K + r`, runner `l` sits at `(r·a_l + ν·e_l)/8` plus `K·a_l`
> whole laps: its AP slot plus its deviation accumulated over `ν` eighths (`drift_position`). It is in the way there iff
> `r·a_l + ν·e_l` is within 1 of a multiple of 8 (`inWay_at_ap_instant_iff_drift`), i.e. iff
> `ν ∈ ((8M − 1)/(a_l + e_l), (8M + 1)/(a_l + e_l))` for some `M` (`drift_blocked_iff_interval`) — its lap zones read at own
> AP instants (`zone_at_ap_instant_iff`). Valid for every real reading.  `[PROVED]`

> **Proposition 6.6 (slot-sharers).** A runner at difference `8b·m` is in the way at every own AP instant
> (`sharer_inWay_at_ap_instant`), so with such a runner present the subject is lonely at no own AP instant
> (`not_lonely_at_ap_instant_of_sharer`).  `[PROVED]` The converse fails: runners with no exact slot-sharer and no lonely own
> AP instant exist (44, 10 and 396 in three families on `[1, 16]`; 51 random to 300).  `[VERIFIED — item 33]` The
> hypothesis "every such runner has a slot-sharer at a finer scale" (some runner with `L·s ∈ 8ℤ`, `L` dividing the reading denominator) is refuted: it held
> for 633 of the 1,079 such runners examined.

**The spine pattern depends only on slot and deviation.** `[PROVED — arithmetic; checked on 95,776 spine instants from
speeds, 0 disagreements]` At spine instants `r = 1, 3, 5, 7` a runner of slot `a` and deviation `ε` is in the way exactly when
`c + r·ε < 1` or `7 < c + r·ε < 9`, with `c = r·a mod 8`. So the pattern is the same at every scale (`A4_SPINE_BLOCKING_v1`):
- only a **near-sharer** (a reading within 1 of a multiple of 8: slot `≡ 0`, or slot `≡ 7` with `ε > 0`) is ever in the way at
  spine 1, and one at distance `δ` from its multiple of 8 is in the way at exactly the spines `r < 1/δ`;
- every other runner is in the way at two of the four spines at most, and only as `{3, 7}` or `{5, 7}`.

> **Proposition 6.7 (the own-AP residue rule — the rational form of 6.5).** Let the readings be `s_l = c_l/κ`. Put
> `h_l = gcd(c_l, 8κ)`, `m′_l = 8κ/h_l`, `u_l = c_l/h_l`. Runner `l` is in the way at the own AP instant `ν` iff `ν·u_l mod m′_l`
> is strictly within `m′_l/8` of 0. Hence `m′_l = 1` is a slot-sharer (in the way at every `ν`); `m′_l` even and at most 8 is
> never in the way at odd `ν`; otherwise `l` is in the way on explicit residue classes of `ν`. The lonely own AP spine
> instants are the odd `ν` outside every runner's classes.
> `[PROVED for the first three clauses — MomentIterationN.own_ap_residue_rule (the residue rule itself),
> slot_sharer_of_m'_eq_one, not_inWay_odd_of_m'_even_le; the last clause, the characterisation of the lonely spine
> instants, follows from them but is not separately stated in Lean. VERIFIED — 40,000 of 40,000 runners, reading
> denominators 1 to 30+, and the formalised rule re-checked against the cascade's own predicate on 40,000 triples,
> 1,004 of them on the open-zone boundary (`experiments/n8/own_ap_residue_check_v1`)]`

At denominator `κ = 2` this is the pair rule: the odd doubled readings are in the way at `ν ≡ ±c⁻¹ (mod 16)`, and the
four pairs `{±1}, {±3}, {±5}, {±7}` all taken leave no lonely own AP instant. **Lattice `L`** is the family of instants
`u = p/(8L)`; it is dead for the subject when some reading is a whole multiple of `8L` (that runner is then on the subject at
every instant of the lattice). A reading `s ≥ 8L` is needed for that, so every lattice with `8L > s_max` is live, and the first
live lattice is at most `⌊s_max/8⌋ + 1` (`s_max = S`). `[PROVED — arithmetic, every real reading; stated for integer readings in `WHY_IT_PREDICTS_v1` §2]`

**Own AP instants are not the cascade's instant.** Near the wrap, `(1, …, 7, 9 ± δ)`, the first own AP instant at which
runner 1 is lonely recedes like `1/(8δ)`, while its first lonely instant stays at `u = 9/64` (two scales) for `δ` down to
`10⁻⁶`. `[VERIFIED — revision-list item 35]` Existence needs some lonely instant, not the cascade's, so lonely lattice
instants settle a runner as well (Corollary 6.4).

### 6.7 Existence

> **Existence.** For every arrangement and every runner, the cascade reaches a fixed point — it arrives at a scale at
> which no reading lies within 1 of a multiple of 8. Equivalently (Corollary 6.4), the run of lap-completion zones from the
> bound ends; equivalently, some flank has a lonely opening.  `[OPEN; not stated in either artefact]`

**The obligation in the form §3 asks for.** `FRAMEWORK_CONJECTURE_v1` §3: *"A proof is an **exhibition**: the rules,
written down, with their conditions shown exhaustive."* **Rules, plural; conditions, plural.** Read that way the obligation
is not that one mechanism works everywhere — it is that the rules already written down leave nothing out. The framework has
been building rules all along, each a condition paired with an instant:

| rule | condition on the difference set | the instant it names |
|---|---|---|
| **Theorem 4.8** | `d_max ≤ 7·d_min` | `1/(8·d_min)` |
| **Theorem 6.12** | every ratio to some flank `e` in the band at opening `k` | `(k + 1/8)/e` |
| **Theorem 6.9** | exactly one non-integer ratio at a live flank | an opening of that flank |
| **Proposition 6.10** | two non-integer ratios, one off the other's lattice | an opening of that flank |
| **Theorem 6.13** | whole-number differences | decided by a finite search, `k < e` at each flank |
| **the U/K calculus** (§6.9) | all but one difference on a `P`-lattice, clear openings known | an opening of the free flank |
| **§4.5, §6.9 census** | the 4,413 fully-pinned families | the recorded `(e, k)` |

**What is proved of it.** Every family of §4.5 and of §6.9; and at other thresholds and fewer differences, the rows of §8.

**What is not yet shown is exhaustiveness.** Measured as predicates on difference sets, the rules above that can be written
as predicates decide about **39%** of random seven-sets, essentially all of it Theorem 4.8
(`experiments/n8/formalised_coverage_v1`). That figure is a **lower bound** — the U/K calculus needs a period and a
clear-opening set supplied per family, and the census is a list of arrangements, so neither is expressible as a predicate and
both count as uncovered there. The gap is the obligation: **a class of difference sets no rule yet reaches.**

Stating it this way changes what counts as progress. Under "the cascade reaches a fixed point" there is none until the whole
thing falls; under §3's form, each new rule is measurable ground. It is the same obligation — the equivalences below are
proved both ways — in the shape §3 asks for.

**The joint, and why it is not the statement here.** `SKETCH_v7` §10 put the same obligation as a claim: *"for every
arrangement and every runner there is a `u` in the window `[1/8, 7/8]` at which all six of the other runners read mid-lap."*
It was `[CLAIMED]`, never proved, and it is the open statement above **with the first window attached** — the nearest runner
reads mid-lap exactly when `u ∈ [1/8, 7/8]`, so the claim says the subject is lonely within its first lap. As written it is
**false**, refuted by the arrangement §6.9 already names: `(1, 31, 75, 97, 128, 160, 176, 225)`, runner 1, which has no
lonely instant anywhere in `[1/8, 7/8]` and is first lonely at `u = 165/128`, in its second lap. Stripped of the window its
content is exactly Existence, which is what is stated here and is open. The same refutation retires v7's §7.4 Claim
(Appendix B.1), whose wording stopped the cascade at lap 0.

**The obligation, as one statement.** `[PROVED — the reduction; Cascade and the specification]` Every link from the bound
to Existence is formalised except one, and composing them leaves a single obligation. The relocation of an instant is a
change of scale (`move_eq_self_or_opening`, `nextOpening_at_scale`); `N` relocations move the nearest reading by at most a
product of lap factors, `m · t_N ≤ (1/8)·∏_{j<N} (Q_j + 1/8)/(Q_j − 1/8)` (`nearest_reading_recurrence`); a cascade whose
instants are capped arrives (`exists_fixed_of_capped`); what it arrives at is the isolation itself, and the least one
(`first_isolation_as_zone_run`); and arriving is equivalent to being lonely somewhere (`lonely_iff_run_ends`). Hence

> **Existence at eight runners is exactly: the cascade's instants are uniformly capped.**
> `LRC.Spec.existence_of_capped` and `capped_of_existence`, both directions, both within the three axioms
> (`experiments/n8/v9_2_spec_axioms_v1.out`; the specification file sits outside both gates — §10).

The converse is stated deliberately. This is the obligation **restated, not weakened** — a cap is no easier than Existence,
and the reduction's worth is that what remains is one statement in the framework's own objects, with every other link proved.
**Read this with the amendment below**: both theorems are stated on `ExistenceAt8`, the difference-set form, which since
2026-09-18 is no longer the target. The equivalence stands as proved; what it is an equivalence *to* is a statement that is
sufficient for the conjecture rather than identical to it.
The word *capped* is this manuscript's own (§8.2).

**The target, and the obligation on arrangements.** `[PROVED — the specification]` Until 2026-09-18 the Lean target was
`ExistenceAt8`, which quantifies over a difference set `ds : Finset ℝ` with `card ds ≤ 7`. That form is **sufficient** for the
conjecture and was proved so (`lonelyRunnerAt8_of_existence`), and the `card ds ≤ 3` sets it admits that no arrangement
produces are themselves settled (`exists_lonely_of_card_le_three`, `[PROVED]`). That it exceeds the conjecture on **no other**
card needs the converse — that every `ds` with `4 ≤ card ≤ 7` arises from some arrangement. An explicit construction is
written down in `Spec/Target.lean` (subject at `0`, a runner at `+d` for each `d ∈ ds`, one at `−d` for `7 − card` of them),
but it is **not formalised**: `[EMPIRICAL — 20,000 sets, no failure]`. It is not the same statement. `Finset ℝ` forces decidable equality; it **collapses
duplicate differences**, destroying the indexing; `card ≤ 7` admits sets no arrangement produces; and it **discards the
arrangement** — where the gaps, the AP structure and "the subject and its two neighbours" live. The target is therefore

> **`LonelyRunnerAt8`** — for every injective `v : Fin 8 → ℝ` and every `k`, some `t > 0` at which every other runner is at
> circle distance at least `1/8` from `k`.

and the obligation is `ExistenceOnArrangements`, the same statement written per subject. The two are `Iff.rfl`
(`lonelyRunnerAt8_iff_existenceOnArrangements`): **the obligation is the conjecture**, not a reduction of it.

`LRC/Cascade/Arrangement.lean` carries the machinery there, with no appeal to `ExistenceAt8`. Loneliness of a subject is
exactly "nobody in the way" (`lonelyAt_iff_no_inWay`), splits into one condition per side (`lonelyAt_iff_two_sided`), and
binds only the **two neighbours** (`lonelyAt_iff_neighbours`). Three facts are arrangement-level and have no difference-set
counterpart: `inWay_comm` — `i` is in `k`'s way exactly when `k` is in `i`'s, a statement relating two *subjects*;
`lonelyAt_add_const` — adding a constant to every speed changes nothing, so `v k = 0` is a convenience and never a
hypothesis, and no runner is held at rest; and `lonelyAt_const_mul` — rescaling the speeds rescales the reading, so the
scale is carried by the speeds and is never chosen.

The bridge is `lonelyAt_iff_lonely_diffSet`: for a **fixed** subject, loneliness factors through that subject's own seven
disparities, so §6's flank, opening and residue results apply verbatim. Through it, `exists_lonelyAt_iff_flank` (a subject is
lonely somewhere exactly when it is lonely at an opening of one of *its own* disparities — the openings are the speeds' own
data, and nothing is picked) and `exists_lonelyAt_iff_bounded` (whole-number disparities: only the openings
`j < e` need be read). Theorem 6.14's criterion is restated there as `lonelyAt_named_instant`, and its `c = 1`, `j = 0` case
as `lonelyAt_inv_of_not_dvd`. All of it is axiom-clean and `sorry`-free.

**What is not claimed.** The amendment does not prove Existence and does not make it closer or further. It relocates the
obligation to the objects the framework is stated in, and makes the existing library available there.

**What failure would require.** A cascade that never stops lands every step on an opening that lies strictly inside
another runner's zone, for ever; by Theorem 6.3(d) the subject is then lonely at no positive instant, and the steps increase
without bound through infinitely many distinct openings. Each such step is arithmetic: if a runner at difference `e` is in
the way at an opening `t = a/(8d)` at or after the bound, then `|e·a − 8w·d| < d` for some integer `w`, and since
`a ≥ d/d_min` (that is, `t ≥ 1/(8·d_min)`),

    | e − (8w/a)·d | < d_min.

A runner in the way at an opening lies within less than one `d_min` of a specific rational multiple of the difference whose
opening it is. `[PROVED — arithmetic; v7 §7.4, there for the openings of its first window]` Failure needs such a relation at
every step, for ever.

**The obligation is per runner**, not per arrangement: a runner outside the families of §4.5 and §6.9 needs its instant
whether or not another runner of the same arrangement is inside them.

**Computations.** `[VERIFIED — exact rational arithmetic]`

- **The cascade equals the BSM first isolation instant** for 207,464 of 207,464 runners (one mover; two movers; every runner
  moved; push-out and spread families; all eight-subsets of `[1, 16]`; random integers to 1,000). Most moves in that
  replication: 24; an adversarial climb over speeds up to 400 found 28 moves, at `(27, 70, 107, 137, 159, 188, 344, 393)`,
  runner 393 (`t = 49/1872`). Each move lands on an opening before the instant, so the number of moves is at most
  `(7/8)·S·R + 7`. `[PROVED — arithmetic]`
- **Exhaustive sweep.** Every integer arrangement with `0 = v_1 < … < v_8 ≤ 40` and gcd 1 — 18,564,316 arrangements,
  148,514,528 runner-instances — has a lonely instant for every runner; by Corollary 6.4 the cascade reaches a fixed point
  for each. **The enumeration is in the pinned frame `v_1 = 0`**, which is not this framework's: §6A's first row does
  not describe it, and v7 recorded its use as a firewall violation. What carries the counts into the framework's objects is
  that a common shift of every speed leaves every difference `v_j − v_i`, and so every reading, unchanged, and that every
  runner of every arrangement was evaluated.
- **Other orders, unpinned.** For `n = 5, …, 10`, every arrangement of `n` distinct positive integer speeds with gcd 1 in
  `[1, 34]`, `[1, 26]`, `[1, 21]`, `[1, 18]`, `[1, 16]`, `[1, 15]` respectively, at threshold `1/n`: every runner has a lonely instant,
  4,025,986 runner-instances, decided by the boundary set, not sampled (v7's procedure gave an instant for each;
  `docs/nN/EXHAUSTIVE_OTHER_ORDERS_v1.md`).
- **v7's procedure.** Over 4,800 runner-instances (random integer arrangements, speeds to 1,500), v7's two families together —
  the openings of its first window and its lattice instants `p/(8D)`, `D ≤ 7·d_min` — gave an instant for every runner, the
  lattice family alone for 0.981–0.999; 21,600 runner-instances across seven populations, including adversarial ones, all
  gave one. In the `v_8 ≤ 40` record the instants v7's procedure gave (not necessarily the earliest) sit at median `u = 1/8`,
  90th percentile `0.173`, 99th percentile `0.25`, maximum `245/304 ≈ 0.806`.
- **The time ratio** `R`: the largest found at order 8 is **≈ 11.96**, at `S ≈ 7.44`, converged on by independent searches on
  unrelated grids. `[EMPIRICAL]`
- **Rational and irrational speeds, and the hard cases** (§6.8); flanks (§6.9).

Existence is open; these are computations over the stated families.

### 6.8 Hard cases and incommensurate instances

| arrangement | runner | cascade | instant | check |
|---|---|---|---|---|
| `(1, 31, 75, 97, 128, 160, 176, 225)` | 1 | 23 moves, `d_min = 30` | `11/256` (`u = 165/128`, `R = 165/16`) | = BSM; harness |
| `(1, 1975, 5265, 6910, 8737, 9589, 11845, 15135)` | 1 | 22 moves, `d_min = 1974` | `73/121072` (`u = 219/184`) | = BSM |
| `(11, 21, 22, 23, 26, 34, 35, 40)` | 35 | 1 move, `d_min = 1` | `25/192` | = BSM |
| `(27, 70, 107, 137, 159, 188, 344, 393)` | 393 | 28 moves, `d_min = 49` | `49/1872` (`u = 2401/1872`, `R = 2401/234`) | = BSM; harness |
| `(4, 12, 29, 37, 101, 121, 176, 196)` | 37 | 1 move, `d_min = 8` | `9/512` | = BSM |
| `(1, 2, π, 4, …, 8)` | π, 4 | `d_min = 4 − π`, Thm 4.8 | `1/(8(4 − π))`, irrational | Lean: `IrrationalDemo.all_lonely`, `time_irrational` |
| `(1, 1 + √2/100, 3, …, 8)` | 2 | 2 moves from `1/(8δ)`, `δ = √2/100` | cascade: `(497/8)/(7 − √2/100) ≈ 8.8930`, irrational | exact in `ℚ(√2)` (`experiments/n8/v9_checks_v1.out`); Lean proves the later lonely instant `75√2/4` at the spine `r = 3` of scale `δ` (`IrrationalCascade.r2_lonely`, `r2_time_irrational`) |
| same | 1, 3–8 | | `71/8`; `1/8` | Lean: `r1_lonely`, `others_lonely` |

**What v7 said of these arrangements.** `(1, 1975, …, 15135)`, runner 1, was v7's witness that its openings alone do not
suffice: all 23 openings admissible in its first window fail, and its lattice family clears the runner at `D = 8`, `p = 3`,
`t = 3/64` (lap 92). `(11, 21, 22, 23, 26, 34, 35, 40)`, runner 35, was its witness that the lattice family alone does not
suffice: with a difference equal to `d_min = 1` the ceiling allows only `D ≤ 7` and no such step clears, while the opening
`(d, a) = (9, 25)` does. `[VERIFIED — exact]` v7 read the second as a regime: a runner whose `d_min` is small against its
other differences has almost no lattice to run. v7's two families covered opposite regimes: the lattice reached instants
outside the first window, and the openings reached numerators its four residues cannot express. `(1, 31, 75, …, 225)`,
runner 1, refutes v7's Claim **as written**: nothing clears in its first window, and it is lonely at `t = 9/40` (`D = 5`,
lap 6) `[PROVED — exact, exhibited; revision-list items 1–2]`. The Claim's wording stopped the cascade at lap 0; the `d_min`
lattice read past lap 0 isolates the runner at `43/240` (`u = 5 + 3/8`), and the `1975…` runner at `17/15792`
(`u = 2 + 1/8`). All of these are lonely instants later than the cascade's first.
(`experiments/n8/hard_cases_first_isolation_v1.py`.)

### 6.9 Flanks

By Proposition 6.1 every lonely instant is matched by a lonely opening of one of the subject's differences. Call that
difference `e` a **flank**; its openings are `(k + 1/8)/e`, `k = 0, 1, …`.

> **Theorem 6.8 (loneliness is a flank statement).** The subject is lonely at some positive instant iff some flank has a
> lonely opening. At the flank's `k`-th opening only the ratio `ρ_j = d_j/e` enters: runner `j` sits at `ρ_j·(k + 1/8)` laps.
> - If `ρ_j = A` is an integer, `j` is clear at every opening iff `8 ∤ A`, and in the way at every opening if `8 | A`.
> - Otherwise only the fractional part `f_j` moves: `j` is in the way at opening `k` exactly when `k·f_j + ρ_j/8` is within
>   `1/8` of an integer.
>
> `[PROVED — Flanks.lonely_iff_exists_flank, position_at_flank, integer_ratio_clear_iff, fractional_ratio_circDist; checked
> 143,520 times against direct evaluation, 0 disagreements]`

A flank is **live** when no ratio to it is a multiple of 8, and **shadowed** when every one of its openings has a runner in the
way.

> **Theorem 6.9 (one fractional ratio).** A flank at which exactly one ratio is non-integer, and every integer ratio is
> not a multiple of 8, has a lonely opening, so the cascade stops.  `[PROVED — Flanks.exists_clear_step,
> lonely_opening_of_one_fractional, stops_of_one_fractional (n ≥ 4 in Lean); elementary for n ≥ 3]`

The proof follows the nearest integer to `k·f + c` step by step: it stays fixed if `f < 2/n`, advances by one if
`f > 1 − 2/n`, and cannot follow a middle step at all; so some opening is clear. No count is used.

> **Proposition 6.10 (a pair of fractional ratios).** Let a live flank have exactly two non-integer ratios.
> (a) If one lies on the `c`-lattice (`Int.fract(c·(y/e)) = 0`, so its fractional part has denominator `c`) and the other does
> not, the flank has a lonely opening. (b) If both lie on lattices and shadow the flank between them, each lies on the other's
> lattice — so their reduced denominators divide each other, and `c₁ = c₂`.
> `[PROVED — Flanks.lonely_opening_of_lattice_and_free, stops_of_lattice_and_free, shadowing_pair_cross_lattice; no count used]`

Both parts run on `class_killer_int`: the lattice runner's verdict repeats with its denominator, so it is clear on a whole
residue class, and shadowing that class would put the other ratio on the same lattice. **(a) is stronger than the "rational and
an irrational" statement it replaces** — it needs only that the second ratio is off the lattice, not that it is irrational
(`off_lattice_of_irrational_ratio` is the bridge if an irrational is what one has).

**Withdrawn in v9.3: the former Propositions 6.10 (rational pair) and 6.11 (the flank sum criterion).**
`[WITHDRAWN — CORRECTIONS_2026_09_17_v2 §5]` Their arithmetic is not in question; they are **inapplicable as a discharge**.
Both conclude that a lonely opening exists without bounding where it is — 6.11's `q = q′L` with `q′ ≤ Q^m` and `Q → ∞`, and
the manuscript's own note that "the criterion names an opening without bounding when" (`k = 1, 5, 45, 442, 4420` as `ε → 0`).
That is register items 4 and 27 at flanks, and it is the ban table of §6A below: *the construction runs a cascade to a named
instant*. The test is the **index bound**, not the tool: `exists_clear_step` is native and argues by contradiction, and
`exists_fixed_of_lonely` is native and uses pigeonhole. Their credited reach is also refuted — over every 8-subset of `[1, 20]`,
958,256 live flanks, the sum criterion fires only at `|J| ≤ 1`, which Theorem 6.9 already decides
(`experiments/n8/flank_sum_reach_v1`); and at order 8 it cannot reach `|J| ≥ 4` at all, since each term is at least `2/n = 1/4`
before any denominator is read. What survives of the half-integer enumeration is recorded as a computation, not a proposition:
the only shadowing pairs to denominator 14 have both fractional parts `1/2`, in 4 unordered whole-part classes mod 8
(`experiments/n8/shadowing_pair_denominators_v1`).

> **Theorem 6.12 (the band at every opening).** At flank `e`'s `k`-th opening a difference `d` is clear iff its ratio lies in
> `⋃_M [(nM + 1)/(nk + 1), (nM + n − 1)/(nk + 1)]`; and if every difference does, the subject is lonely there.
> `[PROVED — Flanks.clear_at_opening_of_band and its converse band_of_clear_at_opening, so the `iff` is proved in both
> directions; lonely_at_opening_of_bands, exists_lonely_of_bands]`

**What mirrors what.** Both of the framework's ratio conditions are this one band at `M = 0`, at two different
`(flank, opening)` pairs. They are one criterion, not two theorems:

| | flank | opening | the band at `M = 0` | at `n = 8` |
|---|---|---|---|---|
| **Theorem 4.8** | `e = d_min` | `k = 0` | `e ≤ d ≤ (n−1)·e` | `d_min ≤ d ≤ 7·d_min` |
| **its mirror** | `e = d_max` | `k = 1` | `e/(n+1) ≤ d ≤ (n−1)·e/(n+1)` | `d_max/9 ≤ d ≤ 7·d_max/9` |

Both recoveries are in Lean so the relationship is checkable rather than asserted: `clear_at_bound_of_ratio`, which carries
the **`e = d_min`** condition as `e ≤ d` — that condition is what makes it Theorem 4.8 rather than a band at an arbitrary
flank — and `clear_at_first_opening_of_ratio` for the mirror. The band condition is *equivalent* to the clearing condition, not a weakening
(`experiments/n8/band_rule_coverage_v1`, 60,000 triples, no disagreement), so the theorem decides every case the criterion
decides. Measured on difference sets: `k = 0` alone settles 50.4% of random seven-sets, `k ≤ 2` at any flank 91.2%
(`experiments/n8/small_k_theorem_v1`). It does **not** prove Existence — the required `k` is unbounded, and a hill-climb
reaches `k = 369` at spread ≈14,125 (`experiments/n8/bounded_k_attack_v1`).

> **Theorem 6.13 (the search over openings is finite).** At a whole-number flank `e` the verdict repeats with period `e`, so
> the subject is lonely somewhere **iff** it is lonely at one of the `Σ_{e ∈ ds} e` openings with `k < e`.
> `[PROVED — Flanks.circDist_periodic_of_int_flank, lonely_periodic_of_int_flank, lonely_iff_bounded_search]`

This is `circDist_periodic_of_lattice` at `P = e`, since `fract(e·(d/e)) = fract(d) = 0` for whole `d`; it was one step away
in the artefact and nothing had taken it. It turns `lonely_iff_exists_flank`'s unbounded `∃ k` into a finite check — median
696 openings for seven differences drawn from `[1, 200]` — and the bounded search never misses (`experiments/n8/
bounded_search_check_v1`, 4,000 sets, zero false negatives). **It does not prove Existence**, which quantifies over
infinitely many difference sets: a decision procedure decides each case, it does not discharge a universal.

> **Theorem 6.14 (the criterion is a congruence).** At a whole-number flank `b` a whole-number difference `a` is clear at
> the `k`-th opening exactly when the residue of `a·(8k + 1)` modulo `8b` lies in the closed band `[b, 7b]`. Composing with
> 6.13, loneliness over whole-number differences is decided by `Σ_{b ∈ ds} b` residue tests in `ℤ`, and no real number
> occurs in the criterion.
> `[PROVED — Flanks.clear_at_int_flank_iff_emod, lonely_iff_emod_search]`

The threshold `1/8` has become a band of integers and the opening index enters only through `8k + 1`. This matters because
of what the two objects support: `circDist` is a minimum of fractional parts and admits only inequalities, while `Int.emod`
admits congruences, the Chinese Remainder Theorem and counting over `ZMod (8b)`. The criterion was checked against the
real-valued definition before it was formalised — 60,000 cases, zero disagreements, and the finite search against a wide
real search on 4,000 sets, zero disagreements (`RESIDUE_ROUTE_v1`, `experiments/n8/residue_route_v1`).

It also bounds the **difference set**, which 6.13 does not: the verdict for `a` depends on `a` only through `a mod 8b`, so
at a fixed flank the question is a finite check over residues. Measured with a firing control — shifting every runner by a
multiple of `8b` left 40,000 of 40,000 verdicts unchanged, shifting by non-multiples changed 38,832 of 40,000.

**What is not claimed.** 6.14 does not prove Existence. The finite problem it gives is indexed by an unbounded flank `b`, so
it is a family of finite problems rather than one. The union bound reappears unchanged: each runner blocks `2b − 1` of the
`8b` residues, a fraction tending to `1/4`. The restriction to `u = 8k + 1` is not cosmetic — it neutralises the flank
runner, which sits exactly on the boundary (`circDist_flank_self`) and so never blocks, measured as a free fraction of
0.1976 against 0.1709 over all residues — but that leaves six effective blockers, and `6 × 1/4 > 1` still. The wall moves;
it does not fall. Stated in the new object, the question is whether seven Bohr sets in `ℤ/8bℤ` can cover the progression
`u ≡ 1 (mod 8)`; the known obstruction to the obvious next move is that `[b, 7b]` is an interval, and intervals do not
factor under CRT.

**Computations at flanks** `[VERIFIED — exact; exhaustive in the stated ranges]`:
- **No runner has every flank shadowed.** Free flanks per runner — order 5, every 5-subset of `[1, 30]`: `{1: 4,086, 2: 56,908,
  3: 199,004, 4: 452,532}`; order 8, every 8-subset of `[1, 20]`: `{1: 16, 2: 4,538, 3: 41,118, 4: 175,806, 5: 354,736,
  6: 314,912, 7: 116,634}`.
- **Where free flanks run out** (order 8, at most two free): shadowed flanks are dead (one exact slot-sharer, 4,064), small (2–3
  runners, 8,638) or wide (4–6 runners sharing one small denominator, 8,564). All 16 one-free-flank runners have the
  difference set `{2, …, 7, 16}`; the free flank is 16, decided at its first opening by the mirror of 4.8.
- **A sharer's own flank** (`d_s = 8b·d_e`): over every 8-subset of `[1, 20]`, 374,556 such pairs (so `b ≤ 2` in that range), the
  sharer's flank is shadowed only if some runner sits at a symmetric point of the sharer's progression (ratio denominator 2, the
  antipode, or 4, the quarter points), or five or more runners sit at its fine slots (denominators 8, 16). Necessary, not
  sufficient. The earlier guess that a sharer's own flank is always free is refuted: 24,656 failures at order 8 against 317,686
  holds (`SHARER_FLANK_RULE_v2`).
- **Shadowing triples** at order 8 with denominators up to 8 and no shadowing pair inside: `(2, 4, 4)`, `(3, 3, 3)`, `(3, 6, 6)`,
  `(5, 5, 5)`; the residue count does not reduce triples to finitely many signatures (`(2, 5, c)` passes it for every `c`), so
  the full list is open.

**The census families decided at a later opening.** `[PROVED — Cascade, 3,072 theorems]` The other 3,072 of §4.5's 4,413
arrangements are lonely not at the flank's bound but at its `k`-th opening for some `k ≥ 1` (median 1, largest 18). The
verdict at each opening is the integer comparison of Proposition 2.1, so each is discharged by `decide`.

**The calculus for a family with a free difference.** `[PROVED — Cascade]` When a shadowing set pins all but one difference,
the remaining one ranges over the reals and the flank must be shown free for every value of it. Three facts do that, and all
three are about openings and denominators, not about measure:

- a difference whose ratio to the flank has **denominator dividing `P`** has the same verdict at openings `k` and `k + jP`,
  so the flank's **clear openings** — those at which every pinned difference is clear — repeat with period `P`
  (`circDist_periodic_of_lattice`);
- a difference that shadows **every** opening of one such class must itself have denominator dividing `P`
  (`class_killer_int`), proved from `exists_clear_step` by following the runner's successive positions, with no density,
  equidistribution or rationality input, and covering rational and irrational ratios in one case;
- therefore the **shadowing values** of the free difference form a finite set, and if none of them shadows every clear
  opening then the flank is free **for every real value** of that difference (`lonely_of_flank_unkillable`). When no single
  flank is free for all values, it is enough that no value shadows every flank (`lonely_of_some_flank_unkillable`).

The eighth-family theorem is the worked case: flank `7`, period `7`, clear openings `{1, 3}`, no shadowing values — and it
is re-derived from the general statement, supplying only that data (`eighth_family_via_calculus`).

**Open at flanks.** That **not every flank of a runner can be shadowed at once**, which is Existence read at flanks.

v9.2 also listed "flanks with four or more non-integer ratios, where Proposition 6.11 does not apply". That is withdrawn:
it is register item 26, **rule coverage read as reach** — `j ≥ 4` was where a proposition stopped applying, not where the
difficulty is. Live flanks fail at every `j` from 2 up (`{2: 13, 3: 44, 4: 147, 5: 285, 6: 561}`, `flank_what_blocks_v1`), so
`j` does not predict failure, and the claim that the withdrawn propositions covered `j ≤ 3` was false. The obligation stays **per runner** (§6.7): a runner needs its instant, and it has
several flanks, so no single flank has to be free. That is why a per-flank criterion cannot discharge it — individual flanks
are shadowed routinely (2.6% of live ones), while no runner was found with every flank shadowed, and **0 of 6,000
arrangements** contained such a runner.


### 6.10 The obligation with no time and no iteration

`[PROVED — Cascade/ScaleCandidates.lean]` A flank opening **is** the first spine instant of a scale
read off the arrangement:

    flankOpening n e k  =  (k + 1/n)/e  =  1 / (n · (e/(n·k+1)))

so the opening of disparity `e` at index `k` is the instant `1/(n·D)` for the **candidate scale**
`D = e/(n·k+1)` (`candidateScale`, `flankOpening_eq_spine`). Nothing is chosen: `e` is one of the
subject's own disparities and `k` an index. This meets §6A's no-search ban and the register's items
22–24, which refuse a loop over the gap because `D = p/(8t)` re-asks the construction's output as its
input.

> **Theorem 6.15.** The subject is lonely at some positive instant **iff** some candidate scale is
> clear for every disparity. `[PROVED — lonely_iff_exists_candidate_scale]`

No quantifier over time, no iteration. Two further facts make it usable.

> **Theorem 6.16.** At `D = e/(n·k+1)` the disparity `e` reads **exactly** `n·k+1`, at distance
> exactly 1 from the multiple `n·k`. `[PROVED — own_reading, candidate_clear_own]`

So every candidate is **clear by construction for the disparity that names it**: one of the seven
constraints is free at every candidate, and the content is the other six.

> **Theorem 6.17.** A disparity `d` is in the way at scale `D` exactly when `D > d`, or
> `D ∈ (d/(n·M+1), d/(n·M−1))` for some `M ≥ 1`. `[PROVED — inWay_at_scale_interval]`

The bad scales are therefore an **explicit union of open intervals on the half-line `(0, d_min]`** —
one dimension, not the six of reading space — and the candidate scales are precisely their **left
endpoints**. A good scale is a *gap*, and a gap is **named** by its endpoint rather than inferred
from a measure. That is what keeps this on the native side of §6A: verifying that a union of cells
covers a region would be a complement-emptiness computation, which the firewall refuses.

**The cascade is a sort and a scan.** `[VERIFIED — 32,000 of 32,000, exact]` The cascade's final
scale is the **largest clear endpoint `d/(8M+1)` at or below `d_min`**, in every case tested
(`scale_interval_v1`). The winning candidate has median rank 1, mean 2.41, maximum 25. The 23–28
moves of §6.8's hard cases are that sort, performed one comparison at a time.

**The index is bounded given the ratio, and that is the useful statement.**
`[VERIFIED — adversarial per band]` `bounded_k_attack_v1` reached `k = 369` and was read as showing
`k` unbounded; its witness has `S ≈ 14,125`, and all eight of that arrangement's subjects resolve in
at most **three** cascade moves with `R ≤ 1.17`. The question it never asked has a clean answer
(`k_vs_S_v1`):

| `S` cap | 8 | 10 | 15 | 20 | 30 | 50 | 100 | 300 | 1000 |
|---|---|---|---|---|---|---|---|---|---|
| max min-`k` | 6 | 6 | 6 | 6 | 7 | 10 | 14 | 37 | 146 |

Roughly linear in `S`; at the order-5 certificate's own working range `S ≤ 26` it is `k ≤ 7`. Random
sampling agrees: `k ≤ 6` settles 24,000 of 24,000 sampled subjects out to `S ≤ 40`. **This is a
measured ceiling, not a proved one**, and the obvious route to proving it — that the bad intervals'
total length decays while candidates densify — is a measure argument and is refused (see B.10).

**Finding the first instant is not the obligation.** `[VERIFIED — exact]` §6A already states that
first-ness is a proved property of the cascade's output and not a requirement. Measured, the
difference is large: on `(27, 70, 107, 137, 159, 188, 344, 393)` the cascade takes **28 moves** to
the earliest instant, while the smallest opening index at *any* flank is **6**; on
`(1, 31, 75, 97, 128, 160, 176, 225)` it is 23 against 4; across 20,000 subjects in the band
`S ∈ [7,8]`, mean 2.16 moves against mean `k` 1.04. The instants agree exactly — Proposition 6.1
guarantees it — so the `(e,k)` form finds the identical instant at a fifth of the depth.

### 6.11 Two walkers

At a flank, writing `ρ_j = d_j/e` and `f_j = Int.fract ρ_j`, runner `j` sits at `k·f_j + ρ_j/8`
(Theorem 6.8). The flank itself has `f = 0` and is free (Theorem 6.16); integer ratios are stationary
and decided by `8 ∤ A_j`. So the moving parts are the non-integer ratios, and Theorem 6.9
(`exists_clear_step`) settles **one**.

**Two walkers do not always clear.** `[VERIFIED — exhaustive, denominators 2…7]` Exactly eight
configurations shadow every opening, and **all eight have both fractional parts `1/2`**, in four
unordered whole-part classes mod 8 — the family §6.9 already records. `ρ = 1/2` and `ρ = 3.5` block
each other at every opening. So no theorem of the form "two walkers always clear" can hold.

**But the obstruction needs a fast walker.** Write `ĝ = min(f, 1−f)`, the walker's effective step.

> **Theorem 6.18 (the run-length criterion).** A walker is bad for at most `(2/n)/ĝ` consecutive
> openings, and from the opening at which it enters the clear arc it stays clear while
> `j·ĝ ≤ 1 − 2/n − ĝ`. Hence if some `L` satisfies `L·f₁ ≤ 1 − 2/n − f₁` and `2/n ≤ L·f₂`, some
> opening is clear for **both** walkers.
> `[PROVED — TwoWalker.bad_run_le, exists_crossing, clear_run, two_walkers]`

The proof uses no count, no density and no equidistribution: the nearest integer cannot advance,
because advancing needs `f > 1 − 2/n` and `f ≤ 1/2 ≤ 1 − 2/n` for `n ≥ 4`. Its witness is the
crossing index plus an offset below `L`, so the argument carries its own index bound — the test §6A
states.

Measured, the criterion fires on **80.6%** of 20,000 sampled pairs with **zero** violations; the
simplified form `max ĝ < 1/4` fires on 24.8% of 40,000 with zero violations. And every shadowing
configuration found exhaustively has `max ĝ ≥ 1/3`.

**The case split, and what is left.**

| two walkers | settled by | status |
|---|---|---|
| one on a lattice, one off it | Prop 6.10(a); `not_shadow_of_off_lattice` | `[PROVED]` |
| both on lattices, different reduced denominators | `shadowing_pair_cross_lattice` forces `c₁ = c₂` | `[PROVED]` |
| the run-length condition holds | Theorem 6.18 | `[PROVED]` |
| **both on a common lattice, run-length failing** | the verdict is periodic in `k`, so a finite check decides it | **where the shadowing family lives** |

**The count of walkers is not the index.** §6.9 records that `j` does not predict shadowing. At
`j = 3`, 496,128 configurations tested exhaustively give 1,432 shadowing, and their `ĝ` multisets
include `(1/3,1/3,1/3)` and `(1/3,1/6,1/6)` — **no walker at `1/2`**. So the `j = 2` family's
half-integers are a `j = 2` fact. What survives across both is the threshold: every shadowing
configuration found has `max ĝ ≥ 1/3`, and configurations with all `ĝ ∈ {1/5, 1/6, 1/7}` were tested
exhaustively and none shadow. `[VERIFIED — exhaustive to denominator 7]`

**Shadowing one flank is common; shadowing all seven has never been seen.** Appendix D.

---

### 6.12 The clearance criterion

Everything the cascade does at a scale is decided by one residue condition. Write the disparities in
reduced units, `d = a·g`, and a scale as `D = e·g/(8N+1)`, so the reading of `a·g` there is
`a(8N+1)/e`. The runner is in the way when that reading is within `1` of a multiple of `8`.

**Theorem 6.19 (the criterion).** *At the scale `e/(8N+1)` a subject is clear exactly when every
disparity satisfies*
```
        e  ≤  a(8N+1)  mod  8e  ≤  7e .
```
`[PROVED]` `DminClearance.clear_at_scale_iff`, with `clear_iff` the case `N = 0`, `e = d_min/g`, and
`bad_iff` the underlying residue statement. Verified against the cascade at **every scale it visits**
— 46,353 of 46,353 — and at `d_min` alone 32,000 of 32,000.

**Theorem 6.20 (order-free form).** *The criterion does not use the value `8`. At order `n` it reads
`e ≤ a(nN+1) mod ne ≤ (n−1)e`, with constant `n−1`.* `[PROVED]` `bad_iff_gen`.

**Corollary 6.21 (`S ≤ n−1` forces clearance).** *A reading in `[1, n−1]` is already inside the band,
so a subject with `S ≤ n−1` is clear at its own `d_min`, with no cascade at all.* `[PROVED]`
`clear_of_reading_le_gen`; the `n = 8` case is `clear_of_reading_le_seven`.

This is Theorem 4.8's constant arriving as a consequence rather than an input: `7` is one below the
first multiple of `8`, at every order. Measured across orders 3–8, the implication holds with zero
violations and the fraction clearing at `d_min` is stable near 0.55–0.63.

**Corollary 6.22 (`d_min` never fails).** *Taking `a = e = c` gives residue `c`, on the lower
boundary, and the threshold counts as clear. So `d_min` never blocks at its own scale, and at most
`n − 2` of the `n − 1` disparities can.* `[PROVED]` `dmin_always_clear`. The ceiling is attained:
`{1, 8, 16, 24, 32, 40, 48}` has six of seven failing.

**The balance.** A failure needs a reading above `7` — either `7c < a < 8c` (a pure spread effect,
unreachable by any multiple) or `a ≥ 8c` landing near a multiple. Over 32,000 subjects the failures
number `1 → 9615, 2 → 4218, 3 → 951, 4 → 106, 5 → 4`: **mostly one**. `[EMPIRICAL]`

---

### 6.13 The move in closed form

**Theorem 6.23 (the lap is exact).** *If `a` blocks at the scale `e/(8N+1)` — its reading within `1`
of `8M` — then `M` is the least `k` with `(8k+1)e ≥ a(8N+1)`. The move's lap index needs no rounding
decision.* `[PROVED]` `MoveRule.move_lap`.

Hence the blocker offers the candidate scale `a·g/(8M+1)`, and the move takes the smallest:

```
      λ  =  D/D'  =  max over blockers of  (8M_a + 1)/s_a ,        D'  =  a·g/(8M_a + 1) .
```

Verified against the cascade on **18,286 of 18,286** moves, and the dilation formula likewise. (Three
moves name a different blocker — ties producing the identical scale — so the rule is exact on the
scale, which is what the recursion consumes.)

**Corollary 6.24.** *Every scale the cascade visits is a candidate scale: `a·g/(8M_a+1)` is
`Cascade.candidateScale 8 (a·g) M_a`. The cascade never leaves that family.* `[PROVED — in the
text]`, immediately from Theorem 6.23 and the definition of `candidateScale`
(`LRC/Cascade/ScaleCandidates.lean`); no separate declaration is claimed.

With Theorem 6.19 this closes the recursion: readings, blockers, dilation and next scale all have
closed forms, and no step is left implicit.

*Not a theorem:* "the smallest lap wins" is a good heuristic and **not** a rule. The ratio is
`(8M+δ)/(8M+1)` with `δ = s − 8M`, increasing in both, so a later-lap blocker sitting far enough
*below* its multiple beats an earlier one above it. It holds 97.3%; the failures have the winner at
median `δ = −0.50`. `[EMPIRICAL]`

---

### 6.14 The dilation is bounded

**Theorem 6.25.** *`λ < 9/7`.* `[PROVED]` `DilationBound.dilation_lt_nine_sevenths`. A blocker at lap
`M ≥ 1` has reading `s > 8M − 1`, so `λ < (8M+1)/(8M−1)`, which decreases in `M` and is largest at
`M = 1`. `M ≥ 1` holds because `d_min` never blocks (Corollary 6.22).

**Theorem 6.26.** *`λ < 17/15` once `M ≥ 2`.* `[PROVED]` `dilation_lt_of_two_le`.

Measured: **45,199 cascade steps, none with `λ ≥ 9/7`**, maximum `1.284105` against `9/7 =
1.285714`, attained at `M = 1`.

**Consequence, and the shape of the difficulty.** `R = ∏λⱼ < (9/7)^K`, so `K > log R / log(9/7)` — a
*lower* bound on the number of moves. There is **no matching upper bound**, because `λ → 1` as
`M → ∞`. Steps can be arbitrarily unproductive, and no ceiling on the move count follows from the
step law.

**The cascade self-slows.** As the scale contracts every reading inflates, so blockers are caught at
higher lap index. Measured on the deep cases, first half against second:

```
     23 moves:  mean M  1.73 → 3.58      λ  1.1483 → 1.0752
     28 moves:  mean M  2.07 → 4.57      λ  1.1204 → 1.0577
```
`[EMPIRICAL]` The driver is `M`, not `δ`: `δ` sits near `−0.5` throughout and is *more* negative in
deep cascades, which would raise `λ` — the lap index is what lowers it.

---

### 6.15 Exact blocks

A disparity is **colliding** when `8 ∣ a` in reduced units, i.e. it shares the subject's residue.

**Theorem 6.27.** *If a blocker's reading is exactly `8M`, the blocker is colliding.* `[PROVED]`
`ExactBlock.exact_block_is_colliding`: `a(8N+1) = 8Mc` with `8N+1` odd forces `8 ∣ a`.

**Corollary 6.28.** *A non-colliding disparity never reads an exact multiple of `8` at any cascade
scale.* `[PROVED]` `noncolliding_never_exact`. Measured: **0 of 12,152** non-colliding blocks are
exact — that zero is the theorem, not the sample.

**Theorem 6.29.** *A near (non-exact) colliding block forces the host `c > 8`; equivalently a host of
`8` or less admits only exact blocks.* `[PROVED]` `near_block_host_large`, `small_host_forces_exact`.
Measured: zero violations, and the smallest host among near blocks is exactly `9`.

An exact block means the blocker is *coincident* with the subject, and it forces the next move in
closed form. **81.3%** of colliding blocks are exact, and the partition is complete: with
`r = b(8N+1) mod c`, `r = 0` is exact (4,314 events), `7c/8 < r < c` is a near block below the
multiple (731), `0 < r < c/8` above it (260). The `r = 0 ⟺ exact` criterion holds 5,305 of 5,305.
The 731:260 asymmetry is the monotonicity of the readings: a blocker enters its bad zone across the
lower edge and is generically caught there. `[EMPIRICAL]`

Colliding disparities are **19.2%** of a colliding subject's pack but **31.3%** of setter events and
**27.3%** of final setters, and the effect survives controlling for size (1.38×–2.64× at equal size
rank, pooled 1.93×). `[EMPIRICAL]`

---

## 6A. The firewall

The framework's bans are part of it.

| | |
|---|---|
| **No stationary frame** | No runner is pinned to zero. The per-runner reading `v_j − v_i` is what loneliness of `i` means (§1.1). Enumerations in a pinned frame carry the caveat of §6.7 |
| **No window, no bound on when** | The evaluation is not confined to a first lap or window, and no result requires a bound on when an instant falls. Bounds such as `R < n − 1` are sufficient conditions at most |
| **No search** | The cascade is fixed by the speeds: there are no candidates, and nothing is picked or predicted |
| **No first-instant demand** | The construction's correctness does not depend on finding the first instant. That the cascade's fixed point is the first lonely instant is a proved property of its output (Theorem 6.2(b)), not a requirement placed on anything |
| **No global clock** | No single shared isolation event is needed; each runner receives its own instant, read in its own `u = d_min·t`. Two qualifications: the reference ideal, the arithmetic progression, **is** globally isolated (φ(n) law, §5, Theorems 4.5–4.7), and deviations from it are read runner by runner; and, in the author's words, *"Global clock no but the slowest speed defines a cycle"* |
| **No measure or density** | Exact arithmetic and the geometry of lap zones only. No measure, density, zero-measure argument, or stability radius |
| **No covering or emptiness language** | The construction forms no complement and no set to be shown empty; it runs a cascade to a named instant |
| **Boundary discipline is mandatory** | Open cells and boundary points evaluated separately; touching zones never merged; a cell decided by an interior point (§1.2) |

**Three** of these were violated in earlier drafts. The first-instant demand entered v7's §7.1 and §7.2, and the pinned frame entered
v7's §7.4 evidence. The third was found only on 2026-09-17: **no covering or emptiness language** was violated by Propositions
6.10–6.11, whose proofs conclude that a lonely opening exists without naming or bounding one — carried through v8 and v9.2
unrecorded, and withdrawn in v9.3 (`CORRECTIONS_2026_09_17_v2` §5).

`CORRECTIONS_2026_09_17_v2` §1 names a fourth site under the same ban, `n > 2k`. That one is **not** a violation of this table
and is not counted here: what §1 refutes is the *framing* of `n > 2k` as the obstruction to beat, not its proof, which runs on
a potential and produces an explicit cap (`stops_when_twice_card_lt` via `exists_fixed_of_capped`). It arrives at the covering
threshold by a route that uses no covering, which is why §8.2 keeps the row with the coincidence stated.

**What the test is, stated once.** The bound lives in the **argument**, not in the shape of the statement. Every result kept
here concludes with an unbounded `∃` in Lean — Theorem 6.9 and Proposition 6.10 both end `∃ k, Lonely n ds (flankOpening n e k)`
— and that is not the defect. Their witnesses come from `exists_clear_step`, whose index is bounded by `~1/min(f, 1−f)` in the
step's fractional part, and `clear_in_class_of_not_int` passes that same bound through. The withdrawn propositions have no such
bound anywhere in their arguments. A reader checking this table should read the proof, not the `∃`.

Of the first two violations, v7 recorded both rather than repairing them quietly. The first is resolved — first-ness is a proved
property of the cascade's output, not a demand — and the second stands as a recorded caveat on pinned enumerations (§4.6, §6.7,
Appendix A).

---

## 7. Formal verification

Two artefacts, Lean 4 with mathlib (§10 for toolchain and digests). Each is built by explicit target by its gate; a plain
`lake build` does not enter `LRC/`.

| | `Construction8` (v7's artefact, frozen) | `Cascade` |
|---|---|---|
| directory | `LonelyRunner/LRC/Construction8/`, 11 modules | `LonelyRunner/LRC/Cascade/`, 21 modules |
| theorems | 85 | 4,759 — **283 structural**, 4,476 generated |
| `sorry`; `native_decide`, `unsafe`, `admit` | 0; 0 | 0; 0 |
| axioms | **every theorem** within `[propext, Classical.choice, Quot.sound]` (82 exactly those three, 3 a subset): `experiments/n8/v9_construction8_all_axioms_v1.lean` and `.out`; the gate checks 23 headline declarations | **every theorem** `[propext, Classical.choice, Quot.sound]`, in the gate |
| gate | `scripts/n8/gate.sh` | `scripts/cascade/gate.sh` |

**The gates.** Both purge build files evicted by file-system sync, build every module by explicit target, inventory
`sorry`, scan for `native_decide`, `unsafe` and `admit`, and run `#print axioms`. Check [4] of each searches declaration
names for a statement of the open part and fails if one is found. The cascade gate reads every module in its directory both for the build
and for the axiom check (a fixed file list once left a new module unchecked, and in 2026-09 was found still to be governing
the build step while the axiom check read the directory; both now derive the list from disk). It also asserts its own
coverage: the number of declarations it extracts must equal an independent count on disk taken with a deliberately broader
pattern, so a declaration written in a form the extractor cannot name fails the gate rather than being skipped silently. At
4,759 theorems it takes about 13 minutes, almost all of it the per-theorem axiom check — measured
2026-09-17 on a warm build, almost all of it step [3]. The exact split varies run to run, so it is **not pinned here**:
the run is deposited at `experiments/n8/cascade_gate_v9_4_v1.out` and that file is the witness, not this paragraph. Check [6]
of the gate fails if the theorem count, module count, digest or artefact commit above ever disagree with the tree. It scales with the theorem
count, so the figure drifts upward; a cold build makes the module build step much longer and no cold figure is quoted. It was tested to fail on a planted
`sorry` in a new module and on a planted declaration naming the open claim; the failure modes of the `Construction8` gate were tested before
it was trusted. The 7 `ConstructionN` declarations cited in §5 and §6.3 are checked in `experiments/n8/v8_axiom_check_v1.lean` (output `v8_axiom_check_v1.out`: 26 of 26 within the three axioms, three gate
declarations re-checked there).

**The 28 declarations added in v12** (§13) live in `experiments/n8/`, **not** in the gated `LRC/` tree. They are individually axiom-checked and carry zero `sorry`, but they are **not** covered by either gate, and the theorem, module, digest and commit figures in the table above are unchanged by them. Whether they migrate into `LRC/` is a later decision.

**Which numbered results are machine-checked.**

| result | declaration | artefact |
|---|---|---|
| Prop 2.1 | `coord_iff` | Construction8 |
| §2.2 lap and phase | `window_iff`, `reading_clear_iff`, `lap_and_phase` | Construction8 |
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
| Thm 4.7 | `survives_of`; `int_of_pairwise_sep`, `not_dvd_of_sep`; `commensurable` | Construction8 |
| Thm 4.8 | `ratio_condition` | Construction8 |
| Thm 4.9 | `wide_gap_core`, `wide_gap_end`, `wide_gap_speeds` | Construction8 |
| Thm 4.10; integral readings recur each lap | `spine_all_or_nothing`; `localisation_free` | Construction8 |
| §5, the φ(n) instants | `isolation_iff_coprime`, `card_coprime_eq_totient`, `instants_on_grid`, `coprime_of_isolation`, `isolation_forces_coprime_grid` | general-`n` line |
| §6.1 the move | `inWay`, `nextOpening`, `move`, `inWay_until_opening`, `lt_nextOpening`, `move_eq_self_or_opening` | Cascade |
| §6.2 integer dead steps, ceiling, slot-sharer step | `dead_iff`, `dead_downward`, `exists_live`, `step_ceiling`, `blocked_lands_on_threshold`, `unblocked_stays_clear` | Construction8 |
| Prop 6.1 | `reading_complete`, `opening_le`, `clear_on_left`; `exists_clear_candidate` | Construction8; general-`n` line |
| Thm 6.2 | `lonely_of_fixed`, `first_isolation_of_fixed`, `first_isolation_as_zone_run`, `flank_at_first_isolation`, `Run.covers` (a run's zones follow on from its start to its end), `run_of_iterate` | Cascade |
| Thm 6.3, Cor 6.4 | `bound_le_of_lonely`, `iterate_le_of_lonely`, `move_le_of_lonely`, `iterate_mem_openings`, `exists_fixed_of_lonely`, `lonely_iff_run_ends`, `lonely_iff_exists_flank` | Cascade |
| Props 6.5–6.6 | `drift_position`, `inWay_at_ap_instant_iff_drift`, `drift_blocked_iff_interval`, `zone_at_ap_instant_iff`, `sharer_inWay_at_ap_instant`, `not_lonely_at_ap_instant_of_sharer` | Cascade |
| Prop 6.7 (first three clauses); §6.6 spine pattern; §6.2 dilation | `MomentIterationN.own_ap_residue_rule`, `slot_sharer_of_m'_eq_one`, `not_inWay_odd_of_m'_even_le`, `spine_reduce`, `circDist_div_lt_iff`, `spine_inWay_iff`, `nextScale`, `reading_at_nextScale`, `dilation_factor`, `one_lt_dilation_factor`, `setter_reading_at_nextScale`, `other_reading_shift`, `shift_coeff_mem` | Cascade |
| §6.8 incommensurate instances | `IrrationalDemo.*`, `IrrationalCascade.*` | Cascade |
| Thms 6.8–6.9 | `Flanks.flankOpening`, `lonely_iff_exists_flank`, `position_at_flank`, `integer_ratio_clear_iff`, `fractional_ratio_circDist`, `exists_clear_step`, `lonely_opening_of_one_fractional`, `stops_of_one_fractional` | Cascade |
| Thm 6.14 (new, v9.5) | `Flanks.clear_at_int_flank_iff_emod`, `lonely_iff_emod_search` | Cascade |
| Thms 6.12–6.13 (new, v9.4) | `Flanks.clear_at_opening_of_band`, `band_of_clear_at_opening`, `lonely_at_opening_of_bands`, `exists_lonely_of_bands`, `clear_at_bound_of_ratio`, `clear_at_first_opening_of_ratio`, `circDist_periodic_of_int_flank`, `lonely_periodic_of_int_flank`, `lonely_iff_bounded_search` | Cascade |
| the framework's symmetries (new, v9.4) | `Flanks.circDist_neg` (`circDist` is even, so speed order is a convention), `lonely_smul` (loneliness is scale-free, which licenses reading against `d_min`), `lonely_neg`, `inWay_at_opening_iff_not_band`, `circDist_flank_self` (a flank sits **exactly** on `1/n` at its own openings — why the zones must be open) | Cascade |
| Prop 6.10 (6.11 withdrawn, v9.3) | `Flanks.lonely_opening_of_lattice_and_free`, `stops_of_lattice_and_free`, `shadowing_pair_cross_lattice`, `off_lattice_of_irrational_ratio`, `on_lattice_of_ratio_den` | Cascade |
| §8.2 small orders | `VersionB.two_diffs`, `three_diffs`, `four_diffs`, `slowest_recursion`, `order_three`, `order_four`; `two_diffs_stop_within_one_move`, `three_diffs_stop_within_three_moves`, `four_diffs_stop_ge_six`, `stops_slowest_recursion` | Cascade |
| §8.2 the tools | `move_growth`, `return_growth`, `return_lemma`, `no_return_after_faster`, `no_four_alternation`, `no_return_after_few_faster`, `nearest_reading_recurrence`, `exists_fixed_of_capped` | Cascade |
| §8.2 `n > 2k` | `ManyDifferences.stops_when_twice_card_lt`, `many_diffs`, `potential_step`, `time_le_potential`, `lapFactor_pow_le`, `lapProd_pow_le`, `potential_pow_le` | Cascade |
| §6.7 the clearing test as arithmetic | `Flanks.clear_of_residue_band` (Prop 2.1 in integers), `lonely_of_band_list`, `circDist_ge_of_band` | Cascade |
| §6.7 clear openings and shadowing values | `class_killer_int`, `clear_in_class_of_not_int`, `circDist_periodic_of_lattice`, `lonely_opening_of_free_off_lattice`, `lonely_of_flank_unkillable`, `stops_of_flank_unkillable`, `lonely_of_some_flank_unkillable`, `stops_of_some_flank_unkillable` | Cascade |
| §4.5, §6.9 the census families | `CensusBatch.*` (62), `PinnedBatch1–4.*` (4,413), `CensusFamilies.family10_lonely`, `EighthFamily.eighth_family_via_calculus` | Cascade |
| §6.7 the target and the obligation | `LRC.Spec.LonelyRunnerAt8` (the target), `ExistenceOnArrangements`, `lonelyRunnerAt8_iff_existenceOnArrangements` (`Iff.rfl`), `lonelyRunnerAt8_iff_arrangement`, `lonelyRunnerAt8_of_arrangement` | specification, outside both artefacts |
| §6.7 the machinery on arrangements | `Arrangement.sep`, `disp`, `InWay`, `LonelyAt`, `lonelyAt_iff_no_inWay`, `lonelyAt_iff_two_sided`, `lonelyAt_iff_neighbours`, `inWay_comm`, `lonelyAt_add_const`, `lonelyAt_const_mul`, `diffSet`, `lonelyAt_iff_lonely_diffSet`, `exists_lonelyAt_iff_flank`, `exists_lonelyAt_iff_bounded`, `lonelyAt_inv_of_not_dvd`, `lonelyAt_named_instant` | Cascade |
| §6.7 the difference-set form (amended, retained) | `LRC.Spec.ExistenceAt8`, `_cascade`, `_flank`, `target_forms_agree`, `target_flank_agrees`, `CascadeCapped`, `existence_of_capped`, `capped_of_existence`, `lonelyRunnerAt8_of_existence` | specification, outside both artefacts |
| §6.10 the candidate scales | `Flanks.candidateScale`, `candidateScale_pos`, `flankOpening_eq_spine`, `own_reading`, `candidate_clear_own`, `lonely_iff_exists_candidate_scale`, `inWay_at_scale_interval` | Cascade |
| §6.11 two walkers | `TwoWalker.bad_run_le`, `exists_crossing`, `clear_run`, `two_walkers`, `not_shadow_of_off_lattice` | development file, outside both artefacts (§10) |
| Appendix A | `first_stretch_overlap`, `consecutive_break` (Construction8); `two_sigma_zone_inside` (general-`n` line) | as stated |

The other negative results of Appendix A are proved in the text with explicit counterexamples. Several cited names predate the
present terminology (`window_iff`, `blocked_width`, `exists_clear_candidate`, `Run.covers`); the frozen declarations keep them.

---

## 8. Generalisation

### 8.1 The infrastructure at every `n`

The cascade, every statement of §6.1–6.6 including Proposition 6.7 (whose declarations carry `n` as a parameter; v9.2 excepted it because it was not then formalised), and Theorems 6.8–6.9 hold at threshold `1/n` over any finite
set of positive differences (Theorem 6.9 in Lean for `n ≥ 4`): the Lean statements carry `n` as a parameter, and the order-8
statements are their instances (`Cascade/Iteration.lean` carries `n` as a parameter). The spine-pattern paragraph of §6.6 is the
exception: it is stated at order 8.

Of `Construction8`'s 85 theorems, 59 are stated at general `n` and a further 20 involve no runner count (statements about
reals: the contiguous-reach bound, the circle-distance identities, the index-free wide-gap core). Six carry `n = 8`, all of
them the zone geometry of §3 and Appendix A.2: the two zone widths, the two ratio bounds, and the two halves of the
single-reading exclusion. Their general forms are formalised in the general-`n` line, with theorems instantiating them at
`n = 8` and recovering the `Construction8` constants:

| | general `n` | range | `n = 8` |
|---|---|---|---|
| zone width | `2/(ns)` | `n ≥ 1` (`blocked_width`) | `1/(4s)` |
| clear interval | `(n−2)/(ns)` | `n ≥ 1` (`clear_width`) | `3/(4s)` |
| first-zone overlap (Appendix A.2) | `s/s′ < (n+1)/(n−1)`, i.e. `(n−1)·s < (n+1)·s′` | `n ≥ 1` (`first_stretch_overlap`) | `9/7` |
| descent through consecutive integers — a chain of first zones of readings `s, s−1, …` persists only while `2s > n + 1` | `2s > n + 1` | every `n` (`consecutive_break`) | `2s > 9`, breaking at `s = 4` |
| single-reading exclusion (Prop 3.3) | `s′ ≤ 2σ/(n−2)` | `n > 4` (`no_solo_closure`; at `n = 4` the two sides coincide) | `s′ ≤ σ/3` |
| `2σ` containment (Appendix A.3) | lap-`(2k+1)` zone of `2σ` inside a clear interval of `σ` | `n > 3` (`two_sigma_zone_inside`) | holds |

**The local restrictions tighten as `n` grows.** The overlap bound `(n+1)/(n−1)` decreases towards 1 — `9/7` at `n = 8`, `13/11` at `n = 12`, `17/15` at `n = 16` — so two
readings must be closer in ratio for their zones to meet; the exclusion `2σ/(n−2)` tightens likewise.

### 8.2 Existence with few differences

With `k` differences at threshold `1/n` (the order-`n` case is `k = n − 1`). Each with its Version B form: the stated step of
the cascade is lonely and first.

| differences | orders | cascade stops within | theorem | status |
|---|---|---|---|---|
| 2 | every `n ≥ 3` | 1 move | `two_diffs_stop_within_one_move` | `[PROVED — Cascade]` |
| 3 | every `n ≥ 4` | 3 moves | `three_diffs_stop_within_three_moves` | `[PROVED — Cascade]` |
| 4 | every `n ≥ 6` | 7 moves | `four_diffs_stop_ge_six` | `[PROVED — Cascade]` |
| `k` | every `n ≥ max(9, 2^(k−1))` | `2^(k−1) − 1` moves | `stops_slowest_recursion` | `[PROVED — Cascade]` |
| `k` | every `n > 2k` | (some step) | `ManyDifferences.stops_when_twice_card_lt` | `[PROVED — Cascade]`; kept with its coincidence stated (below) |

The orders `n = 3` and `n = 4` (two and three differences) are the first two rows read on the diagonal (`TerminationThree`,
`TerminationFour`; at `n = 4` the instant also satisfies `d_min·t < 3/4`). The `n > 2k` row improves the previous row for every
`k ≥ 5` (for example `k = 5` at `n ≥ 11`, against 16) and reaches no order on the diagonal. Five differences at `n = 6 … 10`
remain open. `[OPEN]`

**The `n > 2k` proof** uses a potential `Ψ(t)`, the product over runners of the lap factors `(r + 1/n)/(r − 1/n)` of the laps each
has passed by `t`. A move set at lap `Q` raises `Ψ` by at least that lap's factor (`potential_step`) and multiplies `t` by less
(`move_growth`), so `t_N·Ψ(t_0) ≤ t_0·Ψ(t_N)` (`time_le_potential`). A Bernoulli bound in integer powers gives
`Ψ(t)^n ≤ C^k·(∏_x (x + 1/t_0))²·t^{2k}`, so the instants are capped when `2k < n` (`exists_fixed_of_capped`). No zone width or
interval length enters. It reaches the same threshold as the zone-width count excised earlier (`AdvanceBudget`, revision
list item 51), and the coincidence is exact and worth stating: `n > 2k` is `2k/n < 1`, that is `k·(2/n) < 1`, which says the
`k` in-the-way arcs, each of width `2/n`, cannot cover the circle. At `n = 8` with `k = 7` their total width is `7/4`, so
they cover it 1.75 times over, which is why this row reaches no order on the diagonal. **The proof arrives at the covering
threshold by a route that uses no covering** — no zone width or interval length enters it. The row is kept on that footing,
with the coincidence recorded rather than left implicit (author's ruling, 2026-09-17); nothing else is built on it.

**The tools**, every `n`: a move set at lap `Q` multiplies the instant by less than `(nQ + 1)/(nQ − 1)`
(`move_growth`); a runner that left at lap `P` is back in the way only after growth `(nP + n − 1)/(nP + 1)`
(`return_growth`), which after a single move reads `Q(n − 2) < 2P + 1` (`return_lemma`); no runner returns straight after
a move by a runner at least as fast (`no_return_after_faster`, `n ≥ 4`); no two runners set four consecutive moves
alternately (`no_four_alternation`); no return across `g` faster moves when `n ≥ 2g + 2` (`no_return_after_few_faster`);
the nearest runner's reading is at most `(1/n)·∏` of those factors (`nearest_reading_recurrence`); a cascade whose instants
are capped stops (`exists_fixed_of_capped`).

**Order 5: Existence with four differences at `n = 5` is open.** `[OPEN]` A stronger, sufficient statement is `R < 4`, lonely
within the nearest runner's first relative lap. What is established toward it: `R` is at most a product of step factors
`(5N + 1)/(5N − 1 + δ)`; a cascade of lap-1 steps only has `R < (3/2)³ = 27/8`; exact progression readings with no slot-sharer give
`R = 1`; the runners that can be in the way at the own AP instants `R = 2, 3` fall in explicit slot-and-deviation classes.
`[DERIVED / VERIFIED; revision-list item 52]`

> **`sup R = 31/9` for every arrangement of ratio `d_max/d_min ≤ 26`.** `[PROVED — exhaustive certificate over words
> `(setter, lap)`, each bounded by an exact rational linear program]` The supremum is attained at the word
> `(1,2), (2,1), (1,3), (3,1), (2,2), (1,6)` with margin `τ = 132/4165`, and `31/9 = 3.444… < 4`, so Existence holds for every
> such arrangement (`experiments/n8/order5_certificate_v3.py`, outputs to `order5_certificate_S26_v3.out`).

Four things about that certificate, stated because each has been misread once. **The value is computed, not recognised:** the
earlier `≈ 31/9` came from the optimum of floating-point programs over bounded searches (item 49); this is exact rational
arithmetic and the rational is the answer, not a reading of one. **The bound is on the ratio, not the spread:** `S = d_max/d_min`
throughout. The script and its first output both printed the word *spread*, which this manuscript reserves for
`W = v_8 − v_1`, a difference and not a ratio; both were corrected and the certificate re-run, and the deposited output now
reproduces from its script. Everything but that wording is unchanged by the re-run — 280,785 words tested, 5,721 realisable,
the same supremum, the same word, the same margin. **What makes the enumeration finite is stated in the output and belongs here:** at ratio bound
`S` no setter sets beyond lap `L = ⌊(4S − 1)/5⌋`, because `R < 4` at the step before the exceedance forces `Q < (4S + 1)/5`,
and a runner's setting laps strictly increase; so the words run to at most `3L` moves — `L = 20` and 60 moves at `S = 26`. **The enumeration is a relaxation, in the sound direction:** the word
programs impose only that each setter is in the way just before it sets and that the instant advances, dropping that the setter has
the latest opening and that the others are clear, so the optimum bounds the true supremum from **above** and `sup R < 4` over the
relaxation proves it for the cascade. **The sweep is flat, not closed:** `31/9` holds at every ratio bound from 10 through 26 with
the same word and the same margin, but flatness over a range is not a proof beyond it, and unbounded ratio stays open — as does
this row's `[OPEN]`, since `R < 4` is a stronger statement than Existence needs (audit R1; §1.3 has no window). From order 6 the nearest runner itself can set a
move: at `n = 6`, speeds `1, 59733/25000, 299191/100000, 392283/100000, 516561/100000`, it is in the way at the ninth step and
the cascade ends at nearest reading 8.3559 (BSM agrees). Annealing on the nearest reading found maxima 8.60, 9.04, 11.66,
10.66 at `n = 6, 7, 8, 9`; the separate search on `R` at order 8 found 11.96 (§6.7). `[VERIFIED instance; EMPIRICAL maxima]`

**Order-8 computations are order-8 computations.** The settled-at-once shares of §4.5 and the counts of §6.7 and §6.9 do not
transfer to other orders.

---

## 9. What is and is not established

**Construction** (Theorem 6.2) — proved, in Lean: a fixed point of the cascade is lonely, first, the end of the run of
lap-completion zones from the bound, and has a flank at exactly one eighth.

**Localisation** (Theorem 6.3, Corollary 6.4, Theorem 6.8) — proved, in Lean: every lonely instant is at or after every step of
the cascade and is matched by a lonely opening no later than it; a lonely instant forces the cascade to a fixed point; a
runner is lonely at some instant exactly when some flank has a lonely opening.

**Existence** (§6.7) — open at order 8. Proved in the families of §4.5 and §6.9 (Theorems 6.8–6.9 and Proposition 6.10, all in
Lean), and at the orders and difference counts of §8.2. v9.2 also cited Propositions 6.10–6.11 "in the text"; the counting parts
of those are **withdrawn in v9.3** and nothing here rests on them. Computed over the families of §6.7 and §6.9, with no case found in
which the cascade fails to stop.

If Existence held for every runner, the conjecture at eight runners would follow.

**Added in v11, and none of it proves Existence.** The clearance criterion (Theorem 6.19) and its
order-free form (6.20), from which Theorem 4.8's constant follows as Corollary 6.21 — `7` is one
below the first multiple of `8`, at every order. The move in closed form (6.23–6.24), which leaves no
step of the recursion implicit. The dilation bound `λ < 9/7` (6.25–6.26) — a bound **above** only, so
`K > log R / log(9/7)` follows and **no upper bound on the move count does**. Exact blocks
(6.27–6.29). The cage (4.11–4.15): whole laps are invisible at a grid instant, and offsets sharing a
factor with `8` can never bind. And `R`'s closed form and band structure (11.1–11.3), with the AP
shown extremal for covering and trivial for `R`.

**What v11 changes about the shape of the obligation.** Existence is now statable without the
cascade (§11.1), and `R < 16` — a bounded question in six real parameters — would suffice for it.
`experiments/n8/RCapObligation_v1.lean` proves `RCapped B → DoorCapped → LonelyRunnerAt8` with the
cap as an explicit hypothesis, so what is owed is visible in Lean rather than assumed. **No bound is
supplied.** `R < 12` rests on 12.2 million profile evaluations and no route found exceeds 28 moves;
both are statements about searches, and `doorCapped_iff` being an `↔` means either would have been
the conjecture itself.

Also established in v10, and none of it moves Existence: §6.10's restatement of the obligation with
no time and no iteration (Theorems 6.15–6.17, in Lean); §6.11's run-length criterion for two walkers
(Theorem 6.18, in Lean) together with the exhaustive refutation of the two-walker case in general;
and §4.5(c)'s grid-as-progression-plus-whole-laps criterion.

Also established: every numbered result of §§2–4 (§7 gives the declaration); §5's derivation of the φ(n) instants; the
negative results of Appendix A, proved in the text or in Lean as stated.

**Author's rulings.** **Promotion: v9.3 is the manuscript of record** (author, 2026-09-17). That closes the decision left open
by `V7_REVISION_LIST_v1` §12 and `V8_REVISION_LIST_v1` — those two lists still describe it as pending and are kept as the record
of their own moment, not repaired in place.

Whether the residue counts and pigeonhole of Propositions 6.10–6.11 sit inside the framework was
**pending** in v9.2 and **lapses in v9.3**: both propositions are withdrawn, so the ruling has nothing left to decide
(`CORRECTIONS_2026_09_17_v2` §5). The author's separate ruling of **2026-09-15**, that such counts are admissible **as tools**,
is untouched and still stands (§5). The `n > 2k` proof (§8.2) was **ruled on 2026-09-17**: the row is kept with its covering-threshold coincidence
stated (§8.2; Appendix B.5).

---

**Added in v12, and none of it proves Existence.** §13 replaces the covering *search* with two rules:
the gap rule (13.1–13.3), which makes every junction an integer inequality, and the reach rule
(13.4–13.6), which turns the sweep into an `↔` that returns the leftmost uncovered point. From those,
the witness's arithmetic form (13.7–13.9) and the removal of the continuum and of division
(13.8, 13.10). 28 theorems, axiom-clean. **Eighteen of them mention no order** and hold at every `n`; the ten
of §13E are order-8 specific and are not claimed otherwise.

**What v12 changes about the shape of the obligation.** For integer readings the covering question is
now posed over `ℤ`: a finite conjunction of integer inequalities on an enumerable candidate set,
proved equivalent to the real statement. The integer-reading branch with collisions is consequently
a statement about **two integers** — for every profile `S`, is there `s ∈ S` and `A ≡ 1 (mod 8)` with
`s ≤ A ≤ 7s` such that `s'A mod 8s ∈ [s,7s]` for every `s' ∈ S`. **No bound is supplied, and the
branch is not closed.** Appendix A.5 records four routes that were tried on it and closed, with the
measurements that closed them, so they are not re-attempted.

**One figure is retracted in v12.** The `53/462` (half `53/924`) minimum uncovered length for the
integer-reading branch is exact and exhaustive for readings `≤ 40` and **is not a floor beyond that
range** — Theorem 13.2 shows the minimum decays like `H⁻²`, and a gap of `1/3080` exists at readings
`55, 56`. Any earlier statement of it as a bound is withdrawn.

## 10. Data and code availability

**The formal development.** Lean 4, toolchain `leanprover/lean4:v4.29.1`, mathlib revision
`5e932f97dd25535344f80f9dd8da3aab83df0fe6` (tag `v4.29.1`), batteries `756e3321fd3b02a85ffda19fef789916223e578c`.

- `LonelyRunner/LRC/Construction8/` — eleven modules `Parts`, `LemmaPass`, `Coords`, `Reference`, `Gaps`, `Sorted`, `Grid`,
  `Integrality`, `Flank`, `Window`, `Bounds`; digest
  `578022e0296ce565ec601655747d1e5cdc614a9efa2cced6540162e698f43b9d`; gate `scripts/n8/gate.sh`.
  **Corrected in v9.5**: v9.2–v9.4 recorded the `Cascade` digest here. `Construction8` is frozen, so the figure had been
  wrong since it was written. See Appendix B.8.
- `LonelyRunner/LRC/Cascade/` — twenty-one modules `Iteration`, `SmallOrders`, `FourDifferences`, `ManyDifferences`, `Flanks`, `ScaleCandidates`,
  `Together`, `VersionB`, `Reading`, `Irrational`, `Certificate`, `EighthFamily`, `NearAP`, `CensusFamilies`, `CensusBatch`,
  `PinnedBatch1`–`PinnedBatch4`, `Arrangement`, `All`; digest `c54d9843191fb009f41fe895cd66efb01a953cccf108c6ac08fd1ead03585154`
  (LonelyRunner commit `c023d10`); gate `scripts/cascade/gate.sh`. `Together` is new in v9.3 and carries H1 (Appendix A
  item 4). The eighteen-module state quoted by v9.2 (4,669 theorems, digest `17e68102…`) is commit `561d73f`. The nine-module state quoted by v9.1 (161 theorems, digest
  `a1916b1e…`) is commit `561d73f`. The seven-module state quoted by v8.2 (135 theorems, digest
  `9657ea89…`) is tag `manuscript-v8.2-cascade`.
- `LonelyRunner/LRC/Spec/Target.lean` — **the target** (amended 2026-09-18, §6.7) and the reduction. **Deliberately outside
  both artefacts**, so the cascade gate's check [4] — that nothing in the artefact names the open statement — keeps its
  meaning. It is therefore **outside the coverage of both gates**: neither builds it nor runs `#print axioms` on it. Its
  axiom check is a separate artefact. `experiments/n8/v9_2_spec_axioms_v1.lean` and `.out` covered **four** declarations; the
  module now carries **fifteen theorems**, and the seven the amendment rests on were not among the four, so that artefact had
  become a stale witness for a file it no longer described — the same shape as the defect Appendix B.8 records. **Replaced in
  v9.6** by `experiments/n8/v9_6_spec_axioms_v1.lean` and `.out`, which names **every theorem in the module**: all fifteen
  within `[propext, Classical.choice, Quot.sound]`. The v9.2 artefact is kept as the record of what was checked then.
- Both digests: `shasum -a 256 *.lean | sort -k2 | shasum -a 256` in the directory.
- `LonelyRunner/LRC/ConstructionN/` — the general-`n` line (§5, §8.1), not part of either artefact, gate `scripts/nN/gate.sh`.

**Computations** (exact rational arithmetic unless stated), in `experiments/n8/` and `experiments/small_n/`:
`complete_predictor_replication_v1.py` (207,464), `scale_cascade_recursion_v1.py` (124,488), `chain_from_laps_v1.py`
(29,320), `move_setters_v1.py`, `residue_rule_q_v1.py` (40,000), `r16_search_v2.py` and `ratio_vs_spread_v1.py` (`R`),
`hard_cases_first_isolation_v1.py` (§6.8), `v9_checks_v1.py` (§6.7 move count, §6.8 irrational cascade), `n8_exact_ap_v1.py`
(§4.5), `a4_spine_blocking_v1.py` (§6.6), `flank_shadow_v1.py`, `flank_irrational_v1.py`, `flank_all_shadowed_v1.py`,
`flank_near_extreme_v1.py`, `flank_one_free_v1.py`, `sharer_even_slot_v1.py`, `sharer_exceptions_v1.py` (§6.9), and for §8.2
the scripts cited in revision-list items 37–52; the other-orders sweep of §6.7 is `docs/nN/EXHAUSTIVE_OTHER_ORDERS_v1.md`.
Several script and document names predate the present terminology (`predictor`, `WHY_IT_PREDICTS`); the construction does
not predict, it determines.

**The census, its emitters and its checks** (§4.5, §6.9). The shadowing-set census is recomputed from its covers and
cross-checked in `census_export_v1.py`, whose output `census_families_v1.json` is deposited with this work so that the
4,475 family theorems regenerate from this repository alone; the underlying per-modulus dump is produced in a separate
working tree. The Lean is emitted by `gen_pinned_batch_v1.py` (the 4,413 with no free difference) and
`gen_census_batch_v1.py` (the 62 with one), and checked against the definition — not against the arithmetic that chose the
witnesses — by `pinned_batch_verify_v1.py` (30,891 clearance checks, 0 failures, 0 disagreements between the residue test
and `circDist`) and `census_batch_verify_v1.py` (15,354 values of the free difference, 0 failures). `framework_cases_v1.py`
holds this manuscript's named cases as a runnable harness and reproduces their published values exactly; a claim that no
arrangement does something is run against it first. `manuscript_map_v1.py` records this document's own
section-to-declaration structure, so a successor version can be diffed against it rather than inspected.

**The exhaustive record of §6.7.** The `v_8 ≤ 40` sweep is a single JSON record, SHA-256
`18f8f88a0f92e08cd2110c61e75b92189baba80506cc73aa098cc86385525a7c`, produced by `exhaustive_exact.py`, SHA-256
`1589b78f939564718204a338b380283b5e0181162e4d2903205e57232be84bc3`; its `u_max_runner: 7` is a 0-based index. It sits in a
separate working tree; both will be deposited together, and the digests identify the deposited copies.
**Both figures are restored in v9.5 from v9.2**, the last version that recorded them correctly — v9.3 and v9.4 overwrote
them with the `Cascade` directory digest. Neither artefact is on disk beside this manuscript, so neither value is
recomputed here: they are `[CARRIED — from v9.2, not recomputed]`. See Appendix B.8.

---

### 10.1 The v11 development files

Not in the gated tree (§7's figures are unchanged by them). Lean 4, same toolchain and mathlib pin as
§10. Each is checked with `lake env lean` from `LonelyRunner/`, and the axiom check for all
twenty-seven is deposited at `experiments/n8/v11_new_axioms_v1.out`.

```bash
cd LonelyRunner
lake env lean ../experiments/n8/DminClearance_v1.lean    # 7  the clearance criterion, general n
lake env lean ../experiments/n8/GridNeighbour_v1.lean    # 8  the cage; laps invisible
lake env lean ../experiments/n8/ExactBlock_v1.lean       # 5  only colliding disparities block exactly
lake env lean ../experiments/n8/MoveRule_v1.lean         # 2  the move's lap is exact
lake env lean ../experiments/n8/DilationBound_v1.lean    # 2  lambda < 9/7
lake env lean ../experiments/n8/RBand_v1.lean            # 1  R mod 8 in [1,7]
lake env lean ../experiments/n8/RCapObligation_v1.lean   # 2  RCapped B -> LonelyRunnerAt8
```

### 10.2 The v12 development files

Also outside the gated tree; §7's figures are unchanged by them. The axiom check for all **28** is
regenerated by `experiments/n8/v12_new_axioms_v1.sh` and deposited at
`experiments/n8/v12_new_axioms_v1.out` — 24 exactly `[propext, Classical.choice, Quot.sound]`, 2 a
strict subset, 2 no axioms at all.

```bash
cd LonelyRunner
lake env lean ../experiments/n8/GapRule_v1.lean          #  3  gap = N/(s s'), N an integer
lake env lean ../experiments/n8/ReachRule_v1.lean        # 13  the fold decides; witness normal form
lake env lean ../experiments/n8/ArithForm_v1.lean        #  2  covering without division
lake env lean ../experiments/n8/Guard_v1.lean            #  8  guards; 8-periodic blocking
lake env lean ../experiments/n8/NoFinitePoints_v1.lean   #  2  one reading blocks all
```

The measurements cited in §13 and Appendix A are reproduced by, in order:

```bash
python3 experiments/n8/gap_rule_v1.py          # the gap identity and the 1/H^2 decay
python3 experiments/n8/reach_rule_v1.py        # fold vs sweep, 4,000 profiles, n = 7,8,9,11,13
python3 experiments/n8/finite_check_v1.py      # candidate sets; the congruence form
python3 experiments/n8/witness_normal_v1.py    # normalisation at orders 4..9
python3 experiments/n8/overlap_tree_v1.py      # Hunter-Kounias spanning-tree measurement
python3 experiments/n8/branchB_witness_v1.py   # s = s* refuted, with the matched control
python3 experiments/n8/branchB_witness_v2.py   # which reading supplies the witness
python3 experiments/n8/branchB_rule_v1.py      # largest-reading rule refuted
python3 experiments/n8/branchB_threshold_v1.py # the threshold hunt, and why it was dropped
```

The measurements cited in §§4.7, 6.12–6.15, 11 and 12, each exact-rational and reproducible:

```bash
python3 experiments/n8/dmin_criterion_v1.py      # criterion at d_min, 32,000/32,000
python3 experiments/n8/scale_criterion_v1.py     # criterion at every scale, 46,353/46,353
python3 experiments/n8/move_rule_v2.py           # the move, 18,286/18,286
python3 experiments/n8/self_slowing_v1.py        # lambda < 9/7 in 45,199 steps; M rises
python3 experiments/n8/colliding_mechanism_v2.py # r = 0 <-> exact, 5,305/5,305
python3 experiments/n8/R_direct_v1.py            # R closed form, 10,677/10,677
python3 experiments/n8/R_bands_v1.py             # R mod 8 in [1,7], 148,892 cascades
python3 experiments/n8/R_frontier_v1.py          # max R against S; the crossing at 7.45
python3 experiments/n8/ap_crossing_v2.py         # the AP's clear set; Theorem 11.3's check
python3 experiments/n8/cell_census_v2.py         # the cell-width law, 96 cells
python3 experiments/n8/transplant_v1.py          # the deep-case recipe
```

**Note on running the cascade gate.** `scripts/cascade/gate.sh` takes **no manuscript argument** — it
finds the highest-numbered `MANUSCRIPT_v*.md` beside the tree itself. Its optional `$1` is the
**build-log output path**, and passing a manuscript path there overwrites that file. Invoke it as
`bash scripts/cascade/gate.sh` with no arguments.

---

## 11. The ratio `R`, and what Existence reduces to

`R = d_min/D_final` is the contraction the cascade performs. Two facts make it the natural object.

**Theorem 11.1 (`R` in closed form).** *At the final scale every reading is `s_i·R` with
`s_i = d_i/d_min`, so clearance is `s_i·R mod 8 ∈ [1,7]` for all `i`; and since the cascade walks
forward from `R = 1`,*
```
        R  =  min { R ≥ 1  :  ∀i,  s_i·R  mod 8  ∈  [1,7] } .
```
Two parts, graded separately. That the clear set *is* `{R : ∀i, s_i·R mod 8 ∈ [1,7]}` is
`[PROVED — in the text]`: the reading of `d_i` at a scale `D` is `d_i/D = (d_i/d_min)(d_min/D) =
s_i·R`, and clearance is that every reading is at least `1` from a multiple of `8`. That the
cascade's value is the **minimum** such `R ≥ 1` is `[PROVED]` from Localisation (Theorem 6.3,
Corollary 6.4): every lonely instant is at or after every step of the cascade. `[VERIFIED — 10,677
of 10,677 against the cascade]`, and exact on every deep case on file, as a check on both. It follows that `R` is
computable from the reading profile alone, with no iteration.

Also exact: `R = c(8M+1)/a` for the last setter `a` at lap `M` (10,290 of 10,290), whence
`R ≤ 8M_final + 1`.

**Theorem 11.2 (the bands).** *`R/8 = d_min·t*` is `d_min`'s own lap coordinate at the isolation
instant, and `d_min` is a disparity, so `R mod 8 ∈ [1,7]`. `R` can never lie in `(7,9)`, `(15,17)`,
…* `[PROVED]` `RBand.R_avoids_bad_bands`, stated for arbitrary `n`. Measured: **148,892 cascades,
zero violations.**

So `⌊R/8⌋` counts the **complete laps `d_min` makes** before isolation, and the bands are occupied as
follows:

```
     band 0   R ∈ [1, 7]     every one of 148,892 random cascades
     band 1   R ∈ [9, 15]    no random cascade; every deep case on file (10.26 … 11.97)
     band 2   R ∈ [17, 23]   never observed
```

**A deep cascade is one that pushes `d_min` past its first lap.** Depth and band are the same
phenomenon seen twice, and the apparent gap in the arrival coordinate — nothing between `0.63` and
`1.28` — is the forbidden band `(7,9)`, not a sampling artefact.

### 11.1 What Existence reduces to

Existence at order 8 is equivalent to `CascadeCapped` (§6.7, both directions in Lean), which is that
the cascade terminates, which is that `R` is finite. With Theorem 11.1 this becomes a statement with
no cascade in it:

> **Existence at order 8 ⟺ for every profile `1 = s₁ < s₂ < … < s₇`, some `R ≥ 1` has all
> `s_i·R mod 8 ∈ [1,7]`.**

And with Theorem 11.2 there is a sufficient condition over a **bounded** region:

> **`R < 16` for every profile ⟹ Existence at order 8**,

since `R < 16` says exactly that `[1,7] ∪ [9,15]` contains a clear point. That is six real parameters
over a region of total length 12, where before it was an unbounded search over `t`. It is *stronger*
than Existence — Existence needs only some band — and it is what every measurement supports.

*This is a reformulation, not progress toward a proof.* No bound is established: `R < 12` rests on
12.2 million profile evaluations and `R < 16` on those plus Theorem 11.2. The counting is no help —
six combs at density `1/4` over 12 units give 18 units of bad measure, a factor of 1.5.

**Method note, and a change of scope stated plainly.** §11.1 argues by covering: it forms
complements and asks whether a set is empty. **§6A's row bans exactly that, and its wording is
formal, not a provenance test** — "the construction forms no complement and no set to be shown
empty". So this section is *not* admitted by reading the row; it is admitted by the **author's
ruling of 2026-09-18** that the ban exists to prevent a covering argument being *imported* from
outside the framework, and that an argument built from the framework's own objects — the readings,
the bad bands, `R` — is not that. The row is otherwise untouched, and the withdrawal it produced
(Propositions 6.10–6.11, Appendix B) stands. Readers who reject the ruling should read §11.1 as
conditional on it; Theorems 11.1–11.2 do not depend on it.

### 11.2 The frontier, and where the maximum sits

Searching profiles directly (12.2 million evaluations) gives `max R = 11.965675`, in band 1, never
reaching 12. At the maximiser exactly one constraint binds:

```
        s₇ · R  =  89  =  8·11 + 1        the largest reading on a band's lower edge
```

so `R = 89/S`, with ceiling `89/7 = 12.714` as `S → 7` — unreachable, because `S ≤ 7` clears at once
(Corollary 6.21). Mapping the tension, maximum `R` at fixed `S`:

```
        S      max R      89/S     ceiling attained?
    7.200    10.56952   12.3611    no — the other six cannot dodge that long
    7.400    10.53050   12.0270    no
    7.450    11.94631   11.9463    yes
    7.700    11.55844   11.5584    yes
    7.950    11.19497   11.1950    yes
```

Two regimes crossing at `S ≈ 7.45`, which is where `R` is maximised. **Every deep case on file sits
there** — 7.467, 7.469, 7.618, 7.857, and the two `R`-maximisers at 7.462 and 7.478 — and `S`
re-pinned to 7.46–7.48 under every rescaling and every seeded climb. It is the optimum, not a
coincidence. `[EMPIRICAL]`

### 11.3 The arithmetic progression is extremal, and the cage says why

**Theorem 11.3.** *For the AP — readings `1,2,…,7` — the clear points in `[1,15]` are exactly the odd
integers `{1,3,5,7,9,11,13,15}`.*

`[PROVED — in the text]`, in two directions. *Odd `R` is clear:* `R` odd is a unit mod `8`, so
`i ↦ i·R mod 8` is injective on `{1,…,7}` and never lands on `0`, hence every reading is in `[1,7]`.
`R = 7` gives `7,6,5,4,3,2,1`; `R = 9` gives `1,2,3,4,5,6,7`. *Nothing else is clear:* the reading
`i = 1` forces `R mod 8 ∈ [1,7]` and `i = 7` forces `7R mod 8 ∈ [1,7]`, and those two alone leave
only the odd integers in `[1,15]`.

`[VERIFIED — exhaustive over all band endpoints]`, `experiments/n8/ap_crossing_v2.py`. **No Lean
declaration is claimed for this result**; it is a text proof with a computational check.

The AP is therefore the configuration closest to covering `[1,7] ∪ [9,15]` — maximised at
**99.9982%**, uncovered `0.000211` of 12 — and its residual is exactly those eight protected points.
The same `slot_gcd` fact that cages offsets 2, 4, 6 protects them.

**The duality.** The AP is at once the extremal *coverer* and the *trivial* case for `R`, whose first
clear point is the minimum `R = 1`. Maximising coverage and maximising `R` are different objectives
with different optima: the `R`-maximisers are irregular profiles at `S ≈ 7.45`, not the AP. Crossing
the boundary along `1, 1+u, …, 1+6u`, the instant `S` exceeds 7 the protected point dies and `R`
jumps to ≈ 4.98 — but that family stays in band 0 throughout. **Regular spacing is not how a large
`R` is reached.**

So a counterexample would have to beat the AP at covering *while* being irregular enough to push `R`
past 15 — two objectives that pull apart. That is a description of the obstruction, not a proof of
it, and nothing here closes Existence.

---

## 12. Depth as a function on the profile space

The number of moves is scale-invariant, so it is a function on the projectivised disparity space.
Everything in this section is `[EMPIRICAL]` unless marked, and every individual figure is exact
arithmetic on a fixed configuration.

**Cells and walls.** Depth is constant on cells, and the walls are exact rationals of the form
`e(8M±1)/(8N+1)` — the intersection of a candidate scale with an in-the-way boundary. Bisected on the
23-move case: `1225/41 = 175·7/41`, `518/17 = 74·7/17`, `2016/65 = 224·9/65`, `225 = 175·9/7`,
`224/7`. Six of seven walls found in one census are recovered by enumerating that form; the seventh
comes from a scale the cascade derives rather than an original disparity.

Because depth is scale-invariant its level sets are **cones**, so the walls are homogeneous
hyperplanes `q·a_i = p·a_j` with `p, q ≡ ±1 (mod 8)`. A 2-D slice confirms it: the depth-0 boundary
is `d_max = 7·d_min` exactly, bisected to `10⁻¹²` at eight values.

**The cells are solid.** Zooming 10× into the depth-28 cell only sharpens its boundaries —
`[48.829268, 49.021277]`, width `0.192` — and no deeper cell appears inside. Refining one coordinate
never reaches a deeper case; several must move.

**Width decays with depth.** Over 96 cells across all seven axes of two cases,
`log(width) = 3.710 − 0.1754·K` (correlation `−0.718`): each extra move multiplies cell width by
`0.839`. That is the quantitative reason deep cases evade sampling and need directed search. The
decay base `1.192` is the same order as the measured geometric mean dilation `1.113` — the mechanism
is that a cell needing one more move is a pre-image under one more contraction — but the two differ
by 6.6% and the identification is not exact.

**Two deep families.** Reading profiles, normalised so the largest reading is 8:

```
    23 moves:  1.071  2.643  3.429  4.536  5.679  6.250  8.000     family A
    27 moves:  1.018  2.509  3.455  4.473  5.600  6.255  8.000     family A
    28 moves:  1.071  4.481  5.115  5.596  6.251  7.060  8.000     family B
```

Family A spreads across `[1,8]`; family B has one isolated small reading and six clustered from 4.5.
The deepest case is family B, and interpolating between the families is a **valley** — depth falls to
5–12 between them. They are isolated peaks.

**Deep cases are constructible.** Since depth is constant on cones, transplanting a profile to a fresh
minimum `c` by `d_i = round(c·r_i)` lands in the same cone up to rounding:

```
    profile A   r = [1, 74/30, 96/30, 127/30, 159/30, 175/30, 224/30]   P(≥20) = 0.992
    profile B   r = [1, 205/49, 234/49, 256/49, 286/49, 323/49, 366/49] P(= 28) = 0.549
```

`c = 3000` on profile B gives `[3000, 12551, 14327, 15673, 17510, 19776, 22408]`, 28 moves. Deep cases
are available on demand at any lattice size, which they were not before. The ~32% failures are
roundings that fall across a wall.

**What is not established.** No route found exceeds 28 moves: transplanting reproduces but never
exceeds; hill-climbing seeded at the record at scales ×1, ×4, ×12 and ×40 never exceeds it; and the
interpolation is a valley. **This is a statement about searches.** No ceiling on the move count is
established, and none follows from §6.14 — adding constraints contracts the cone of admissible
profiles without emptying it, and the depth-28 cell has ordinary positive width, not the vanishing
width a geometric limit would show.

---

## 13. The covering scan as a rule

Everything in this section is machine-checked and **none of it proves Existence**. It concerns the
*form* of the covering question, not its answer. The artefacts are in `experiments/n8/`, not in the
gated `LRC/` tree, so the figures of §7 are unchanged by it.

The covering test used throughout this work is a search: build the bad intervals of each reading,
sort them, sweep left to right. This section replaces that search with two closed-form rules and
then shows what they force. **Eighteen of the twenty-eight mention no order at all** — every declaration of
`GapRule_v1`, `ReachRule_v1` and `ArithForm_v1` (§13A–§13D) is stated at general `n` and holds at
every order. The remaining ten (§13E, `Guard_v1` and `NoFinitePoints_v1`) are **order-8 specific**:
the literal `8` occurs in their statements — `ZMod 8`, `¬ (8 ∣ s)`, `s·R ≡ 1 (mod 8)` — and no
general-`n` claim is made for them.

### 13A The gap rule

For a reading `s` at level `m`, the bad interval ends at `(nm+1)/s`; the next, of reading `s'` at
level `m'`, begins at `(nm'−1)/s'`. The width between them is

    (nm'−1)/s' − (nm+1)/s  =  N/(s·s'),      N = s(nm'−1) − s'(nm+1).

**Theorem 13.1** (`GapRule.gap_eq`). The identity above holds for all integers with `s, s' > 0`.

**Theorem 13.2** (`GapRule.gap_ge`). For **integer** readings `N` is an integer, so a gap has `N ≥ 1`
and width at least `1/(s·s')`.

**Theorem 13.3** (`GapRule.no_gap_iff`). Two consecutive intervals meet or overlap exactly when
`s(nm'−1) ≤ s'(nm+1)` — a linear inequality over `ℤ`, not over `ℝ`.

*Checked* (`experiments/n8/gap_rule_v1.py`): 126,258 gaps across 4,000 profiles, width
`= N/(s·s')` and `N ≥ 1` in every case, 0 violations.

**A retraction follows immediately, and it is against this work.** Theorem 13.2 gives a smallest
possible gap of `1/H²` for readings bounded by `H`. The minimum uncovered length therefore **decays**;
a gap of `1/3080` exists at readings `55, 56` (`experiments/n8/gap_rule_v1.py`). The figure `53/462` (half `53/924`) recorded for the
integer-reading branch is exact and exhaustive **for readings ≤ 40** and is not a floor beyond that
range. It was never a bound, and is not one now.

### 13B The reach rule

Strip the bookkeeping from the sweep and one number remains:

    reach r []            = r
    reach r ((a,b) :: t)  = if a < r then reach (max r b) t else r

**Theorem 13.4** (`ReachRule.covered_below_reach`). Everything from the start up to the reach lies in
one of the intervals. **No sortedness hypothesis is required**: the fold is sound on any list, and
ordering only makes it sharp.

**Theorem 13.5** (`ReachRule.reach_uncovered`). On a list sorted by left endpoint, no interval
contains the reach. Sortedness enters in exactly one branch — the one where the scan *stops*: if it
halts at `r` because the next interval starts at `a ≥ r`, every later interval also starts at
`a' ≥ a ≥ r`.

**Theorem 13.6** (`ReachRule.reach_decides`). Hence an `↔`: `[r,N]` is covered **if and only if** the
reach passes `N`. When it does not, the fold *returns the leftmost uncovered point*
(`ReachRule.uncovered_witness`).

*Checked* (`experiments/n8/reach_rule_v1.py`): against the interval sweep on 4,000 random integer
profiles at `n = 8` — 0 verdict mismatches, and the reach is the first uncovered point in every
uncovered case. Identical code at `n = 7, 9, 11, 13`.

### 13C What the witness can be

**Theorem 13.7** (`ReachRule.reach_mem`, `reach_denom`). The recursion assigns `r` only its starting
value or the right endpoint of an interval it crossed. So the witness is the start, or `(nm+1)/s` —
a rational whose **denominator divides a reading**.

**Theorem 13.8** (`ReachRule.finite_check`). Covering `[r,N]` is therefore equivalent to covering a
**finite list of explicitly named points**. No quantifier over the continuum remains on either side.
*(Candidate-set size at `n = 8`, readings `< 60`: min 27, median 123, max 242 —
`experiments/n8/finite_check_v1.py`.)*

**Theorem 13.9** (`ReachRule.witness_normalised`). Combining these: if covering fails, a witness
exists in normal form — the start, or `(n·m+1)/s` with `s` from the reading set.

Read on the bad sets, this says a lonely point exists of the form `t = A/(n·s)` with `s` a speed and
`A ≡ 1 (mod n)`. **No novelty is claimed for this.** Witness-denominator normal forms are an
actively worked area and at least one other is established (the maximum is attained where two sine
curves cross, forcing denominator = sum or difference of two velocities); the relationship between
that form and `A/(n·s)` has **not been checked**. What is claimed is that the statement is proved and
that the derivation here is independent of the classical route. Grade: `[PROVED]` for the abstract
interval theorem; `[VERIFIED-INSTANCE]` for the reading on the bad sets — orders `n = 4..9`,
exhaustive over `(n−1)`-subsets of `[1,16]` plus 3,000 random profiles from `[1,400]` per order,
**0 mismatches in twelve arms** (`experiments/n8/witness_normal_v1.py`). The `n ≤ 7` arms test the
reduction, not the conjecture.

### 13D The arithmetic form

**Theorem 13.10** (`ArithForm.near_iff_int`, `covers_iff_int`). At a point `A/s` with `s > 0`, being
within `1` of a multiple of `n` is the integer inequality `|A − nks| < s`; equivalently
`s'·A mod n·s ∈ (−s, s)`. No rational arithmetic survives.

Together with 13.8: **for integer readings, at any order, deciding whether `[1, n−1]` is covered is a
finite conjunction of integer inequalities over an explicitly enumerable candidate set** — proved
equivalent to the real statement, not approximating it. The sweep's only operations are `a < r` and
`max r b`, and by 13.3 each is an integer comparison after clearing denominators.

*Checked* (`experiments/n8/finite_check_v1.py`): 374,522 candidate points across 3,000 profiles,
integer form against real form, 0 mismatches; the resulting finite congruence check against the full
interval sweep, 0 mismatches on 3,000 profiles.

### 13E Guards and blocking

**Theorems 13.11** (`Guard_v1.lean`, 8 declarations: `guard_blocks_below`, `raising_unguards`,
`klein_self_inverse`, `ap_clear_at_odd`, `unguarded_width`, `odd_clear_of_not_dvd`, `block_periodic`,
`block_shift`) and **13.12** (`NoFinitePoints_v1.lean`: `near_eight_blocks`,
`one_reading_blocks_all`). The guard relation is `s·R ≡ 1 (mod 8)`; the Klein structure makes it
self-inverse, so guards are exactly the units. `block_periodic` is what halves the integer-reading
problem.

### 13F Grades and declaration index

Grades, since §13's results are otherwise carried by prose. Theorems 13.1–13.8 and 13.10–13.12:
**`[PROVED]`**, Lean, axiom-clean, general `n` for 13.1–13.10 and order-8 for 13.11–13.12. Theorem
13.9: **`[PROVED]`** as the abstract interval statement; its reading on the Lonely Runner bad sets is
**`[VERIFIED-INSTANCE]`**, not formalised. Every measurement quoted in §13 is **`[EMPIRICAL]`**,
bound to the script, sample and range named beside it. **No result in §13 is `[CLAIMED]` or
`[ASSERTED]`, and none bears on Existence.**

| result | declarations | file | theorems |
|---|---|---|---|
| 13.1–13.3 | `gap_eq`, `gap_ge`, `no_gap_iff` | `experiments/n8/GapRule_v1.lean` | 3 |
| 13.4–13.9 | `reach_*`, `finite_check`, `witness_normalised`, +2 `simp` | `experiments/n8/ReachRule_v1.lean` | 13 |
| 13.10 | `near_iff_int`, `covers_iff_int` | `experiments/n8/ArithForm_v1.lean` | 2 |
| 13.11 | eight guard declarations | `experiments/n8/Guard_v1.lean` | 8 |
| 13.12 | `near_eight_blocks`, `one_reading_blocks_all` | `experiments/n8/NoFinitePoints_v1.lean` | 2 |
| | | **total new in v12** | **28** |

All 28 are within `[propext, Classical.choice, Quot.sound]` — **24 exactly those three, 2 a strict
subset (`[propext, Quot.sound]`), and 2 depending on no axioms at all** — with zero `sorry`, zero
`native_decide`, zero `unsafe`, zero `admit`. The axiom check is deposited: it is regenerated by
`experiments/n8/v12_new_axioms_v1.sh` and its output is `experiments/n8/v12_new_axioms_v1.out`. That
file is the witness, not this paragraph. The count of 28 is taken with comments stripped, because a
doc-comment line beginning with the word `theorem` has previously been miscounted as a declaration in
this project; the raw line count gives `ReachRule_v1` 11 rather than 13.


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

Each is a route that looks natural and does not work, with the reason. Stated as contributions. Where a figure was measured
inside v7's first-lap window `[1/8, 7/8]`, it is labelled so.

**1. Comparing the in-the-way zones' total length with the lap cannot name an instant.** In the progression the first
runner's lonely instants are isolated points, `≡ 1/8, 3/8, 5/8, 7/8 (mod 1)`: the set on which such a comparison would have to
find room has length zero in the case that matters. Any argument must name an instant.

**2. A chain of overlapping zones does not have a ratio to accumulate.** A route that follows a chain of overlapping
in-the-way zones (a run, in §6.4's terms) and bounds the spread of readings it can pass through fails on four exact facts.
(i) `u = 7/8` can be in the way of a reading well above `9/7`: `s = 11/5` on its second lap, `‖(11/5)(7/8)‖ = 3/40`.
(ii) The overlap bound `s/s′ < 9/7` holds for first zones only (`first_stretch_overlap`); lap `k` of `s` meets lap `k′` of `s′`
when `s/s′ < (8k + 1)/(8k′ − 1)`, giving `17/7` and `25/7` later. (iii) A run is built from zones, not runners: a reading `s` has
`s` zones per lap of the nearest runner (`3s/4` inside v7's window, where seven readings supplied about 24), and an observed run
went 11 steps with readings recurring; `N` runners do not give `N − 1` steps. (iv) A single reading can be in the way at both
`u = 1/8` and `u = 7/8`: `s = 8`. The descent through consecutive integers breaks at `s = 4` (`consecutive_break`).

*Data on runs* (development record; enumeration in the pinned frame `v_1 = 0`, which leaves every difference unchanged). Over
every arrangement `0 = v_1 < … < v_8 ≤ 20` whose short gap has moved off the wrap (§4.6): 231,294 runner-instances with a reading
in the way at the bound; runs of mean 2.38 zones, 99th percentile 8, maximum 19; ends at 99th percentile `u = 0.304`, maximum
`0.589` (at `(0, 2, 8, 10, 11, 13, 16, 17)`, runner 0, reading 7). These are small integer arrangements; runs elsewhere end
much later (§6.7: `R ≈ 11.96`, `u ≈ 1.5`).

**3. Counting readings against clear intervals fails.** Over one lap of `u` a reading `s = 8` has 8 zones and 8 closed clear
intervals `[(8k+1)/64, (8k+7)/64]` (6 of them inside v7's window). The v7 inference that five other readings cannot be in the way
on six intervals assumed one reading per interval; readings share an interval, and one reading has zones in several. Over
300,000 draws of five readings, the most closed was three of v7's six, which is neither none nor all (v7's conclusion held in
that search; its counting argument does not). And no count on how many intervals one reading reaches can repair it: with `σ`
the smallest reading other than the baseline, the lap-`(2k+1)` zone of `s = 2σ` lies inside the closed clear interval
`[(8k+1)/(8σ), (8k+7)/(8σ)]` of `σ` **for every** `k` (`two_sigma_zone_inside`, needs `n > 3`). `[PROVED]` So Proposition 3.3's
"at least two readings acting together" cannot be combined with a count of how many intervals each reading reaches.

**4. Runners in the way together (H1).** The development record states H1 as: same-side runners are in the way together
only where their connecting difference is within `1/4` of a lap line. The sharper form holds. If the two runners sit at
`x`, `y` relative to the subject with `‖x‖, ‖y‖ < 1/8`, then `‖x − y‖ ≤ ‖x‖ + ‖y‖ < 1/4`; and if both lie on the same side,
in `(0, 1/8)` or in `(−1/8, 0)`, then `|x − y| < 1/8`. Since `x − y` is the connecting difference times `t`, that difference is
within `1/4` of a lap line, and within `1/8` on the same side. `[PROVED — Together.connecting_difference_near_lap, connecting_difference_same_side; the circle-metric triangle inequality they need, circDist_sub_le, is proved there too]` The development
record combines H1 with the overlap bound of item 2 to argue that a long run forces near-divisibility conditions
`k·b ≡ 0 (mod 8a)` on the arrangement's gaps (`PROOF_DEV_v1` Part V, which sits in a separate working tree at
`lrc-n8/notes/` and is not deposited with this manuscript; the passage is quoted verbatim in `LOST_FUNCTIONS_v1` §E, which is,
so the step is checkable here). That step is stated there, not derived; it is recorded
here as a direction in the framework's objects, not as a result. The next test it names: trace the steps of the longest run
(19 zones) and locate the arithmetic that ends it.

**5. A depth floor cannot cap the cascade by controlling growth.** A candidate lemma from outside this project proposed a
universal floor `δ ≥ c_* > 0` on how shallowly a returning setter can sit, and used it through
`λ_j ≤ 1 + (2 − 8c_*)/s_j`. The floor is real over whole-number speeds and is now proved — but it is `1/(8b)`, set by the
previous setter, not universal (`Flanks.depth_floor`). The route fails for a reason independent of the constant's size: for
any **true** floor `c_*` and any **true** lap bound `C_lap` on `Σ(1/s_j)/log G`, the chain
`log G ≤ Σ(2 − 8δ_j)/s_j ≤ (2 − 8c_*)Σ(1/s_j) ≤ (2 − 8c_*)C_lap log G` forces `(2 − 8c_*)·C_lap ≥ 1`, which is the exact
negation of what the route needs. Step two is termwise, so no sharpening of the depth bound helps.

The reason is that `s' = s + (2 − 8δ)` exactly, so `s` grows linearly in move count and `Σ(2 − 8δ_j)/s_j` is a left-endpoint
Riemann sum for its own integral `log(s_end/s_start)`; the measured overestimate is 0.8% to 12% over 1,560 cascades. Both
sides of the circle count the number of moves, so no contradiction can come out of it. This also places the route on the
familiar line: the threshold `c_* > 1/4 − 3/(4k)` is non-positive exactly when `k ≤ 3`, which at `n = 8` is exactly `2k < n`.
Full adjudication in `LONG_RETURN_LEMMA_v1`; the forcing argument and its measurements in `LONG_RETURN_CIRCLE_v1`
(`experiments/n8/long_return_circle_v1`).

---

### Routes 6–9, closed in v12, with the measurement that closed each

**Generic counting on the integer-reading branch.** Each reading eliminates about `1/4` of the
candidate numerators `A`; seven readings give `7/4 > 1`. This is the classical measure obstruction in
another coordinate — total bad measure `7 × 3/2 = 10.5` against an interval of length `6`. **Any
argument that ignores overlap between readings fails here, at any order, by construction.**

**Hunter–Kounias on the overlaps.** The bound `|⋃Aᵢ| ≤ Σ|Aᵢ| − max_{spanning tree} Σ|Aᵢ ∩ Aⱼ|` is
valid and was the obvious non-counting route. Forcing a gap needs the tree sum above `4.5` over six
edges. Measured exactly (`experiments/n8/overlap_tree_v1.py`) over 400 random 7-reading profiles from
`[2,200]`: mean single-reading measure `1.4984`, mean pairwise overlap `0.3702`, **best spanning tree `3.1023`**. The bound lands at
`10.5 − 3.1023 = 7.3977` where `6` is needed — short by `1.40`, and not close. Scope: that sample and
range; not a proof that no tree reaches `4.5`, a measurement that none came near it. **Not a live
lead.**

**Two witness-selection rules, both refuted exhaustively.** On the 244,790 Branch-B profiles with readings in `[2,30]`
(`experiments/n8/branchB_witness_v1.py`, `branchB_rule_v1.py`, `branchB_threshold_v1.py`): "take `s = s*`, the reading divisible by `8`" fails on **18,809** of them
(smallest `S = (1,2,3,4,5,7,8)`); "take the largest reading" fails on **794**, with failures
persisting at `s_max = 41, 48, 56, 80` under 300k-per-value sampling and no clean threshold.

The first refutation has a reusable cause. Its motivation was that `s*`'s own constraint
self-neutralises, since `s*·A/(8s*) = A/8` and `‖A/8‖ = 1/8` exactly. That is true — and
`(s·A) mod 8s = s` for **every** reading when `A ≡ 1 (mod 8)`, so the argument never singled out `s*`
at all. A matched control confirms it: readings not divisible by `8` fail at `10.90%`, the same order.

**What survives** (`experiments/n8/branchB_witness_v2.py`). Allowing **any** reading to supply the
witness: 0 failures in all 244,790 profiles. Two regularities, measured and unexplained — at least **two** readings always supply a
witness, never one and never zero (distribution over the six eligible readings
`{2: 61, 3: 1879, 4: 21557, 5: 97893, 6: 123400}`); and the supplying reading is never the smallest.
Scope: readings `[2,30]`, `n = 8`, integer readings.


## Appendix B. Version maps

### B.1 From v7 to v8

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
| References: Rosenfeld "the two formulations agree by the standard reduction" | removed | nothing uses a reduction to a stationary runner; Existence is stated per runner on differences |
| — | §4.6 | wrap gap at the global start, gap migration and its obligation; perturbations (`LOST_FUNCTIONS_v1` §§F, H) |
| — | §2.3 | fitting between AP locations, open (item 24) |
| — | Appendix C | the objection ledger's tested objections (ruling Q4) |
| v7 §3 "the baseline has no zone inside the evaluation window" | §3 | the window is gone, so Proposition 3.3's conclusion keeps the baseline alternative |

### B.2 From v8 to v8.1 to v8.2

Both dated 2026-09-15. Added in v9.2, the transitions having been recorded in `V8_REVISION_LIST_v1.md` rather than here.

**v8 → v8.1** (+195 lines, −40; every removed line replaced in place).

| | v8.1 | why |
|---|---|---|
| **Appendix C. Objections tested** | new | the objections and their tests collected in the manuscript rather than in the development record |
| §2.3 **fitting between the AP locations** | new, `[OPEN]` | the author's statement of 2026-09-14 stated exactly: against a progression of gap `D`, runner `k` sits strictly between its neighbours' locations and adjacent bands overlap by one gap. With the worked fits `(1, 31, 75, 97, 128, 160, 176, 225)` at gap 32 and `(1, 2, 3, 4, 5, 6, 7, 100)` failing, the 45,568/34,462 and 80,357/58,800 counts, and the open part — how the fit decides which runners need the cascade (revision-list item 24) |

That `[OPEN]` is the first of the five this manuscript still carries. The section then wrote the anchored gap as `S/7`; the
symbol was separated from the difference ratio in v9 and is now `W/7` (B.3, audit finding C1).

**v8.1 → v8.2** (+23 lines, −13).

| | v8.2 | why |
|---|---|---|
| §2.2 **lap and phase** | new, `[PROVED]` | a reading's product `s·u` splits as whole laps plus a phase; clear exactly when the phase is in `[1/8, 7/8]`, and for `u ∈ [0, 1)` exactly when `u` is (`lap_and_phase`, `reading_clear_iff`, `window_iff`) |
| §7 axioms row | the further `Construction8` and `ConstructionN` declarations checked | `experiments/n8/v8_axiom_check_v1.lean`, output 26 of 26 within the three axioms; three gate declarations re-checked there |
| §7 table | row for §2.2 added | |
| Proposition 6.1 | grade sharpened | from the bare `[PROVED]` to the earliest-instant form: the opening it supplies is lonely and no later one is, so it is that instant, the bound being the opening `k = 0` of `d_min` |
| Appendix C | rows extended | incommensurable speeds, the real-to-integer reduction, covering and candidate counting, and what the test means |

v8.2 was frozen by the author on 2026-09-15 and audited twice — `V8_2_ISOLATED_AUDIT_v1` (54 findings, isolated) and
`V8_2_OWN_AUDIT_v1` (17) — which is what v9 was redrafted against (B.3).

### B.3 From v8.2 to v9

Sources: `V8_REVISION_LIST_v1.md` items 1–7; `V8_2_ISOLATED_AUDIT_v1.md` (54 findings, tables R1–R7 and C1–C5);
`V8_2_OWN_AUDIT_v1.md` (17 findings, K1–K17); the author's audit request of 2026-09-15; `FRAMEWORK_BOUNDARY_AUDIT_v3`, `WHAT_STOPS_PROOF_v2`, `A4_SPINE_BLOCKING_v1`, `T4_FLANKS_v3`,
`FLANK_NEAR_EXTREMES_v2`, `SHARER_FLANK_RULE_v2`. v8.2 itself is unchanged.

| v8.2 | v9 | reason |
|---|---|---|
| §8.2 "Order 5 is open. In the cascade's quantity it is `R < 4`" | Existence with four differences at `n = 5` is open; `R < 4` a stronger sufficient statement | `R < 4` is the first window (audit R1; boundary audit B2) |
| §4.5(a) "at each of the four instants `u = r/8`, `r ∈ {1, 3, 5, 7}`" | "at every spine instant" | `spine_all_or_nothing` holds for every unit `p`, not only the first lap |
| §8.2 maxima "each below `2n − 1`"; §6.7 "no `R ≥ 16`", "no ceiling on the number of moves", "nothing bounds the number of moves or `R`" | maxima reported without window comparison; "Existence is open" | bounds on when are not requirements (R1, R7) |
| §6.8 runner 2 of `(1, 1+√2/100, 3, …, 8)` given as instant `75√2/4` | cascade instant `(497/8)/(7 − √2/100) ≈ 8.8930` after 2 moves; `75√2/4` a later lonely instant proved in Lean | contradicted Theorem 6.2(b) (audit C5; exact check `v9_checks_v1.out`) |
| §6.7 adversarial climb "reached 29" moves | 28 moves, `t = 49/1872` | recount in the table's convention (C2) |
| Appendix C "the gap is a scale `k·d_min`", "`4k` candidates", "the rules missed", standing objections "evidence is finite", "exactness only for commensurate speeds" | labelled as the ledger's 2026-09-14 construction; each step is one move; the standing objections withdrawn | scales are `d/(8N+1)`, nothing is a candidate (R2, C1); R3, R7 |
| Appendix C "what the conjecture asks of that runner" | "Existence for that runner" | conjecture named once, in §9 (R5; list item 1) |
| §6.2 dead lattice under "the moves are the scale jumps" | slot-sharers at a real scale; integer dead steps as the integer form; not the cascade's path | B4, R3 |
| §6.6 Prop 6.7 and the first live lattice for rational/integer readings | Prop 6.7 as the rational form of 6.5; live-lattice bound proved for real readings | B3, B5, C3 |
| symbols `S`, `R`, `D`, `m`, `n` used two ways | `S = d_max/d_min`, `W` spread, `R` time ratio, `z` residue (Prop 2.1), `Δ_i` set, `q` time denominator, `κ` reading denominator, `μ` smallest speed gap, `ν` own-AP index, `ρ_j` flank ratio, `b` sharer multiple, `w` (§6.7) | C1; separated again in v9.1 |
| §2.1 "six readings to evaluate" | all seven evaluated | C5 |
| §4.6 `d_max = 7 + ε`; "window re-anchors"; "between the readings `9/8` and `15/8`" | `7 + 2ε`; "bound moves"; positions of readings 3 and 5 | C5, R1, C1 |
| §4.5(d) "Integral readings localise … `u ∈ [1/8, 7/8]`" | "Integral readings recur each lap", a periodicity fact, outside the families | C1, C5 |
| §4.6, Appendix A.2 pinned-frame counts without caveat | caveat added | R4 |
| §6A no-global-clock "the slowest runner's lap is the cycle in which instants are counted" | the author's words quoted; instants read in each runner's own `u` | R4 |
| §6A | rows "No window, no bound on when" and "No search" added | the author's rules (2026-09-14/15) |
| §8.1 "remaining five forms hold for every `n ≥ 1`"; "Whatever obstruction … not weaker" | ranges per form; the obstruction sentence removed | C5, R6 |
| Prop 3.3 as a length comparison | as containment of a clear interval | R6 |
| Appendix A.2–A.3 window counts ("`3s/4` zones", "6 clear intervals", "none reaches `u = 7/8`") | counts over a lap, window figures labelled | R1 |
| Appendix A.3 open clear interval `((8k+1)/(8σ), (8k+7)/(8σ))` | closed | R4 |
| abstract "every theorem" in both artefacts on the three axioms | true for both: every `Construction8` theorem checked (`v9_construction8_all_axioms_v1`) | C2 |
| §7 rows missing `commensurable`, `instants_on_grid`, `coprime_of_isolation`, the `SmallOrders`/`FourDifferences` theorems, `first_stretch_overlap`, `consecutive_break` | added | C4 |
| §6.7 "eight distinct positive speeds … thresholds `1/5` to `1/10`" | `n` speeds at threshold `1/n`, ranges stated | C1 |
| §2.3 fit counts over "eight-subsets of `[1, 20]`" | "with gcd 1" | C2 |
| §8.2 maxima 11.66 vs §6.7 11.96 | two searches named | C2 |
| "returns", "predictor" wording | "names", "arrives at", "determinator"; legacy names noted | R2; list item 6 |
| §1.1 "Exactness, and where it holds" | "Real speeds throughout"; the scale-free ideal in the author's words | R3; the author (2026-09-15) |
| — | §4.2 perfect isolation has no slack | `WHAT_STOPS_PROOF_v2` G3 |
| — | §6.2 a step is one dilation; the setter lands on the ideal | `A4_SPINE_BLOCKING_v1` §4 |
| — | §6.6 the spine pattern depends only on slot and deviation | `A4_SPINE_BLOCKING_v1` |
| — | §6.9 Flanks: Theorems 6.8–6.9 (Lean), Propositions 6.10–6.11, mirror of 4.8, computations | `T4_FLANKS_v3`, `FLANK_NEAR_EXTREMES_v2`, `SHARER_FLANK_RULE_v2` |
| — | §8.2 `n > 2k` row | list item 3 (`ManyDifferences`) |
| §7 `Cascade` 7 modules, 135 theorems, digest `9657ea89…` | 9 modules, 161 theorems, digest `a1916b1e…` | list items 3, 7 |

Applied in a different form: the isolated audit's proposal to delete "Nothing above `v_8 = 40`" — the sentence is gone and the
scope is stated in the sweep's description instead (`0 = v_1 < … < v_8 ≤ 40` and gcd 1), so the earlier loss audit's requirement
that the scope be kept is met without presenting it as a limitation.

Not applied, with reason: the isolated audit's proposal to delete the slowest-runner cycle from §6A — it is the author's own
qualification, now quoted there.

Not carried into the manuscript: revision-list item 2's **T3**, "state `R ≤ 2n − 1` as an empirical conjecture". A bound on when
an instant falls is not a requirement of any result (§6A), so v9 reports the maxima found (§8.2) without the conjecture. The
list keeps T3 as a working item.

**v9.1 corrections** (compile-diff of v9 against v8.2 and the two audits): restored `v8_axiom_check_v1.out` and its 26 of 26;
the earlier slot-multiple bound `W/(8g)` beside the `d_max` form; the citations of revision-list item 21 and
`WHY_IT_PREDICTS_v1` §2; "not sampled"; "the local restrictions tighten as `n` grows"; `Cascade/Iteration.lean` as the file
carrying the parameter; Appendix C's "the first three rows above withdrew those objections as they were framed". Added: the
refuted sharer guess with its counts, the range of the sharer census, the open triple list, five differences at `n = 6 … 10`
open. Symbols separated again after the redraft moved three collisions: `z` for the residue of Prop 2.1, `κ` for the reading
denominator of Prop 6.7, `w` for the integer of §6.7, `b` for the sharer multiple in §6.9. Scope corrected: §8.1's
generalisation excludes §6.6's order-8 spine paragraph.

---

### B.4 From v9 to v9.1

2026-09-15. The compile-diff of v9, run before promotion; its record is the addendum to item 8 of
`V8_REVISION_LIST_v1.md`. Added in v9.2 for the same reason as B.2.

**What the loss audit found.** 0 audit findings unaddressed (of the 54 isolated: 52 applied, 2 recorded; of the 17 own: all
applied); 22 numbered results present at the same grade — v8.2's whole set, carried; v9 added four of
its own (Theorems 6.8–6.9, Propositions 6.10–6.11) for the 26 v9.2 carried, so the audit's 22 is a carry count and
not a total. v9.3 withdrew Proposition 6.11, leaving 25; v9.4 added Theorems 6.12–6.13 for 27; **v9.5 adds Theorem 6.14, so this manuscript carries 28**, and Proposition 6.10 is restated (§6.9); 4 retraction records carried, none re-claimed; 114 Lean names all
resolving; 26 figures new to v9 all sourced; and the Cascade digest, theorem count, tag and commit recomputed on disk.

**Fixed in v9.1.** Seven small losses: the `v8_axiom_check_v1.out` result, the `W/(8g)` slot-multiple bound, the citations of
revision-list item 21 and of `WHY_IT_PREDICTS_v1` §2, "not sampled", "the local restrictions tighten as `n` grows", the
`Cascade/Iteration.lean` reference, and Appendix C's "the first three rows above withdrew those objections". Also restored:
the sharer refutation record and the census range; the open triple list; five differences at `n = 6 … 10` stated open; the own
audit credited in B.3; the "not applied" record corrected, the `v_8 ≤ 40` scope belonging to the sweep description and not
being a limitation; and a B.3 row for §4.5(a)'s widening to every spine instant. **T3 was recorded as not carried into the
manuscript, with the reason**, rather than left absent.

**Six contradictions the redraft had introduced were removed.** The symbol collisions on `ρ`, `q` and `m` — now `z`, `κ`,
`w`, `b` and `ρ_j` — and §8.1's generalisation, which had swept in §6.6's order-8 spine paragraph and now excludes it.

v9.1 was frozen by the author on the same day.

### B.5 From v9.1 to v9.2

v9.1 is frozen; nothing in it is edited. This version adds what was formalised after that freeze and moves one grade.
Author's rulings of 2026-09-17 are marked.

| v9.1 | v9.2 | why |
|---|---|---|
| §7: Cascade 9 modules, 161 theorems | 18 modules, 4,669 at v9.2; **19 modules, 4,705 at v9.3** | the tree; digest and commit refreshed in §10 |
| §7 gates paragraph | extended | the fixed module list was still governing the build step while the axiom check read the directory; both now derive from disk. A coverage assertion added against an independent broader count, so a declaration the extractor cannot name fails the gate rather than being skipped. Runtime recorded |
| §7 table | four rows added | the clearing test as arithmetic; clear openings and shadowing values; the census families; the reduction |
| §4.5 | the 1,341 census families clearing at the bound | **ruling: it matters, so the split decides** — `k = 0` is this section's criterion. The near-agreement with the 31% figure is called a coincidence of two populations |
| §6.9 | the 3,072 decided at a later opening, and the calculus | **ruling: framework names** — clear openings, shadowing values, denominators; not residue classes, covers or orbits |
| §6.7 | the reduction | `CascadeCapped ↔ ExistenceAt8`, both directions. The converse is stated so the reduction is read as the obligation restated, not weakened. The `[OPEN]` is unchanged |
| §6.8 | two rows annotated, one added | the `R` readings, and the named-case harness |
| §8.2 order 5 `[EMPIRICAL] ≈ 31/9` | `[PROVED — ratio ≤ 26]`, `sup R = 31/9` | **ruling: the post-correct grade, with ambiguity named.** Four are named: the value is computed not recognised; the bound is on the *ratio*, and the script's own verdict line wrongly prints *spread*; the enumeration is a relaxation in the sound direction; the sweep is flat but not closed. The row's `[OPEN]` stays |
| §8.2 `n > 2k` "nativeness pending" | kept, coincidence stated | **ruling: keep it as a row with the coincidence stated.** `n > 2k` is `k·(2/n) < 1` — the `k` arcs cannot cover the circle; at `n = 8, k = 7` they cover 1.75 times over. The proof reaches that threshold using no covering |
| §9 "Author's rulings pending … whether the `n > 2k` proof is native" | the `n > 2k` ruling recorded as made; the Props 6.10–6.11 one was still pending at v9.2 and is **withdrawn in v9.3** with the propositions | the two sites disagreed after the §8.2 edit; found by the compile-diff before promotion |
| — | the specification file's gate position stated, with its own axiom-check artefact | it is outside both gates by design, so its "within the three axioms" needed a witness of its own (`v9_2_spec_axioms_v1`); found by the compile-diff |
| §5 | the nativeness check recorded | the additions were checked against §5's claim declaration by declaration: only `Int.fract`, `Nat` casts and division, `List`/`Finset` membership and `Function.iterate_add_apply`; nothing from measure theory, topology, filters or number theory; `exists_clear_step` uses no non-local identifier at all |
| §6.2, §6.7 | three sketch sections accounted for | `SKETCH_v7`'s **enlarged tier**, **mixed reading** (its §7b) and **the joint** (its §10) had never appeared in any manuscript version, a gap the v1 audit named on 2026-09-13. The first two are retired by Theorem 6.2(b) — the cascade lands on the first lonely instant, so no tier or candidate list can better it, and the mixed reading is beaten on its own worked example. The joint is the open statement with the first window attached, and **false as written**, by the arrangement §6.9 already names |
| Appendix B | **B.2** and **B.4** added; the appendix renumbered B.1–B.5 | the map ran v7→v8, v8.2→v9, v9.1→v9.2, leaving v8→v8.1→v8.2 and v9→v9.1 unmapped here; both were recorded in `V8_REVISION_LIST_v1.md` instead. Now in the appendix, so the chain is unbroken: v7 → v8 → v8.1 → v8.2 → v9 → v9.1 → v9.2. Six cross-references were repointed with the renumbering; the two to B.1 were unaffected, B.1 being the only number that did not move |
| §8.2 | the certificate re-run at ratio 26 and its output re-deposited | the script and its first output printed *spread* where the manuscript reserves that word for the speed spread. Both corrected; the re-run changed the two wording lines and nothing else — 280,785 words, 5,721 realisable, `31/9`, the same word and margin `132/4165` — so the deposit reproduces from its script |
| §10 | census artefacts, the specification file, refreshed digest | the emitters, the verifiers, the harness, the map; and that the census data is deposited so the theorems regenerate from this repository alone |

**A trace recovered, not a change.** B.1 maps v7's sections to v8's but not its numbered results, so a reader holding v7
cannot follow a result by its number. The three that were renumbered out of §7 are:

| v1 | v7 | v8 onward |
|---|---|---|
| Theorem 7.1 — the procedure returns `u` ⟹ the runner is lonely at `u/d_min` | Theorem 7.2 — returns `(d, a)` ⟹ lonely at `a/(8d)` | **Theorem 6.2 (Construction)** |
| — | Proposition 7.1 — lonely at any instant of its **window** ⟹ lonely at one of the candidates | **Theorem 6.3 (Localisation)** and **Corollary 6.4**, with the window dropped and the statement strengthened to an equivalence over every positive instant |

Nothing was lost in that renumbering; the second was strengthened. Recorded here because the trace was
missing, not because anything moved.

Unchanged: the 26 numbered results and their declarations; §1.3's statement that there is no window; §6A; and all five open
items — §2.3, §4.6, §6.7, and the two in §8.2.

### B.6 From v9.2 to v9.3

v9.2 was the manuscript of record, frozen 2026-09-17. v9.3 unfreezes it for one reason: **Propositions 6.10–6.11 were an
imported argument and are withdrawn.** The full case is `CORRECTIONS_2026_09_17_v2` §5; in short, both conclude that a lonely
opening exists without bounding where it is, which is register items 4 and 27 and a violation of §6A's own ban table.

| what | v9.2 | v9.3 |
|---|---|---|
| Prop 6.11, the flank sum criterion | `[PROVED — pigeonhole and a residue count; ruling pending]` | **withdrawn** |
| Prop 6.10, the rational pair's counting step | `[PROVED — residue count; ruling pending]` | **withdrawn**; the surviving parts restated and formalised |
| Prop 6.10, the mixed pair | prose, "a rational and an irrational one never do" | `lonely_opening_of_lattice_and_free` — **stronger**: needs only "off the lattice", not "irrational" |
| Prop 6.10, the rational pair's reduction | inside the residue count | `shadowing_pair_cross_lattice` — `c₁ = c₂` with **no count** |
| §6.9 "Open at flanks" | led with `j ≥ 4`, "where Proposition 6.11 does not apply" | that clause withdrawn — register item 26, rule coverage read as reach |
| §9 author's rulings | the counting ruling **pending** | **withdrawn**; nothing left for it to decide |
| §6A ban table | "Two of these were violated in earlier drafts" | **three** — the covering ban, unrecorded through v8 and v9.2 |
| §7 crosswalk: Prop 6.7, §6.6, §6.2 | "derived and verified, not formalised" | 13 Lean declarations (12 theorems and `nextScale`) |
| §7 crosswalk: H1 (Appendix A item 4) | "not formalised" | `Together.connecting_difference_near_lap`, `_same_side`, `circDist_sub_le` |
| numbered results | 26 | **25** (6.11 withdrawn; 6.10 restated) |

**Nothing else moved.** §1.3's no-window statement, §6A, every open item and every other numbered result and declaration
stand as in v9.2. To be exact, since v9.2's roll-up counted five and this is a different tally of the same body: §2.3, §4.6,
§6.7 and the **two** in §8.2 are unchanged verbatim, §6.9's shadowing-triples item is unchanged, and §6.9's flank item is
unchanged in substance —
"not every flank of a runner can be shadowed at once" was already there, and only the withdrawn `j ≥ 4` clause preceding it is
gone.

**What is *not* claimed.** The withdrawal does not make Existence closer or further. It removes two propositions that were
never load-bearing for it, and corrects a statement of where the difficulty lies.

### B.7 From v9.3 to v9.4

v9.3 was the manuscript of record earlier the same day. v9.4 supersedes it because the Lean work that followed is new
mathematics, not the figure corrections v9.3 absorbed in place.

| what | v9.3 | v9.4 |
|---|---|---|
| the mirror of Theorem 4.8 | `[DERIVED — Theorem 6.8]`, prose | **Theorem 6.12**, `[PROVED]`, three declarations, and `clear_at_bound_of_ratio` states the `k = 0` recovery of 4.8 in Lean |
| the search over openings | unbounded `∃ k` (`lonely_iff_exists_flank`) | **Theorem 6.13**: at a whole-number flank the verdict has period `e`, so the search is finite |
| the census | 4,413 declarations, split 1,341 "at the bound" / 3,072 "later" | one criterion at 169 `(e, k)` pairs, greedy cover 78; the split named as a **false division** |
| numbered results | 25 | **27** |
| §7 crosswalk | no row for the new work | row added, seven declarations |

**What is not claimed.** Neither new theorem proves Existence. 6.12 widens what is decided and leaves `k` unbounded; 6.13
makes the whole-number case decidable, which decides each difference set and discharges no universal. Existence at order 8
is unchanged and remains `[OPEN]`.

**Nothing else moved.** Every other numbered result, every `[OPEN]` item, every retraction record and §6A's ban table stand
as in v9.3.

### B.8 From v9.4 to v9.5

v9.4 was the manuscript of record on 2026-09-17. v9.5 supersedes it for one new theorem and one correction.

| what | v9.4 | v9.5 |
|---|---|---|
| the clearance criterion | real-valued, `1/8 ≤ circDist` | **Theorem 6.14**: an integer congruence, `b ≤ a(8k+1) mod 8b ≤ 7b` |
| finiteness | in the opening index only (6.13) | also in the difference set, at a fixed flank |
| `Construction8` digest | `a2089a3a…` — the `Cascade` digest | `578022e0…`, computed |
| §6.7 JSON and `exhaustive_exact.py` digests | `a2089a3a…` for both | **restored from v9.2**: `18f8f88a…` and `1589b78f…`, marked `[CARRIED]` |
| `Cascade` figures | 4,705 theorems, 229 structural | 4,709 theorems, 233 structural |
| numbered results | 27 | **28** |

**The digest correction.** **v9.2 was correct**: its §10 carried four *distinct* digests — `Construction8` `578022e0…`,
`Cascade` `17e68102…`, the §6.7 JSON `18f8f88a…` and `exhaustive_exact.py` `1589b78f…`. **v9.3 introduced the defect** and
v9.4 repeated it: each recorded a single SHA-256 four times (`1af2c9f2…` in v9.3, `a2089a3a…` in v9.4), in both cases the
then-current `Cascade` digest — the `Cascade` tree digests to `1af2c9f2…` at commit `b8ee8b7`, to `a2089a3a…` at `561d73f`,
and to `17e68102…` at `7df1ec4`, which is the value v9.2 records. The mechanism is visible in that pattern: the `Cascade`
digest was refreshed by replacing every 64-character hex string, rather than the one that had changed.

Gate check [6] did not catch it because it greps for the **presence** of the `Cascade` digest, which one correct slot
satisfies; the other three were never examined. Check [6] now also requires the `Construction8` digest and requires the two
to differ.

That `Construction8`'s v9.2 digest `578022e0…` is exactly what this tree computes today is the evidence that it is in fact
frozen, as §7 says. Nothing rested on the wrong values — no argument cites them, and `Construction8` has its own gate
(`scripts/n8/gate.sh`) which verifies that tree directly. The defect was in what a reader was told to reproduce, which is
the reason the figures are recorded at all.

**What is not claimed.** 6.14 does not prove Existence — see its own paragraph. Existence at order 8 is unchanged and
remains `[OPEN]`.

**Nothing else moved.** Every other numbered result, every `[OPEN]` item, every retraction record and §6A's ban table stand
as in v9.4.

### B.10 From v9.6 to v10

v9.6 is carried forward; **no numbered result is removed, weakened or regraded**, and every `[OPEN]`
item stands. Numbered results 28 → **32** (Theorems 6.15–6.18).

| what | v9.6 | v10 |
|---|---|---|
| the obligation | the cascade reaches a fixed point; equivalently some flank has a lonely opening | **§6.10**: some **candidate scale** `e/(8k+1)` is clear for every disparity — no time, no iteration `[PROVED]` |
| the bad scales | not stated as a set | **Theorem 6.17**: an explicit union of open intervals on `(0, d_min]`, the candidates their left endpoints |
| the cascade | an iteration | **a sort and a scan** — the final scale is the largest clear endpoint below `d_min` `[VERIFIED — 32,000 of 32,000]` |
| "the required `k` is unbounded" | read as closing the flank route | true and uninformative: the witness has `S ≈ 14,125` and is trivial for the cascade. `k` is bounded **given `S`** — 6 at `S ≤ 20`, 7 at `S ≤ 30` |
| two walkers | Prop 6.10 (a) and (b) | **refuted in general** (the `f = 1/2` family) and **Theorem 6.18** closes the rest by run length |
| §4.5(c) grids | a definition | grid = progression + whole laps; the `φ(n)` criterion; the integer-scale layer reaches 40–48% |
| §10 figures | 4,748 / 272 / twenty modules / `d8ceb5ad` / `58ba790` | 4,759 / 283 / twenty-one / `c54d9843` / `c023d10` |

**Four withdrawals, recorded rather than repaired silently.**

1. **A scale-selection rule from the AP fit.** Three candidates — the minimal fitting scale, the
   margin-maximising scale over all eight, and the same over the front four — each **fail** on
   `(11, 21, 22, 23, 26, 34, 35, 40)`, serving no scale for some subject at any `r ≤ 400`
   (`ap_fit_rule_v1`). §2.3's open item is not closed.
2. **A slot-occupancy reading of the hard arrangements.** It reconstructed an arrangement from a
   disparity set by putting the subject at **0** — a stationary runner, §6A — and used one of up to
   128 sign patterns. Redone on arrangements (`slot_collision_v2`), the mean-`R`-falls-with-crowding
   trend survives and the tail structure does **not**; the tail claim is withdrawn.
3. **A bound on how much of the scale half-line the bad intervals cover.** Measured at ~56% on
   random samples and read as a cap leaving persistent room. It is not a cap: coverage reaches
   **0.989** on `(1, 31, 75, 97, 128, 160, 176, 225)` and **0.987** adversarially
   (`bad_coverage_v1`). Truncating the interval index undercounts the accumulation near zero by
   about `d_min/8` per disparity. **And even a true bound would be a measure argument**, which §6A
   refuses — a scale outside every bad interval *is* a lonely instant, so such a bound would be
   Existence by the banned route.
4. **`ĝ = 1/2` as the signature of shadowing.** True at `j = 2`, false at `j = 3`
   (`ghat_index_v2`). What survives is the threshold `max ĝ ≥ 1/3`.

**What is not claimed.** Nothing in v10 proves Existence, and no grade moves. Theorem 6.15 is an
equivalence, so the obligation is restated in better coordinates and is **no easier**.

### B.11 From v10 to v11

**Carried.** All 32 numbered results at the same numbers with the same statements; all `[OPEN]`
items still `[OPEN]`; every withdrawal, correction and version map B.1–B.10; Appendices A, C, D. The
v10→v11 compile-diff reports a **deletion set of zero lines** — v11 is v10 plus insertions.

**Added.** §4.7 (Theorems 4.11–4.15), §§6.12–6.15 (6.19–6.29), §10.1, §11 (11.1–11.3), §12, and two
paragraphs in §9. Numbered results 32 → 51.

**Compile-diff findings, and what was done.**

| finding | action |
|---|---|
| Theorem 11.3 graded `[PROVED]` with no named artifact | text proof now given in both directions; **no Lean declaration claimed** |
| Theorem 11.1, Corollaries 4.15 and 6.24 carried no grade | graded; 11.1 split into its proved part (from Theorem 6.3) and its verified part |
| "all axiom-clean" had no deposited artifact | deposited at `experiments/n8/v11_new_axioms_v1.out`, 27 of 27 |
| header said "twenty-five theorems in six files" against its own table | corrected to **27 in 7**; the table was right |
| §6A's ban glossed as a provenance test, which its wording is not | §11.1 now states the change of scope plainly and attributes it to the author's ruling |
| §10 cited for reproduction commands it did not contain | §10.1 added |
| a second section numbered 4.6; new sections at `##` not `###` | renumbered 4.7; levels corrected |
| no version map for the transition | this appendix |

**An incident, recorded rather than repaired silently.** The first build of v11 was **destroyed** by
its author before it was committed: `scripts/cascade/gate.sh` was invoked with the manuscript path as
`$1`, and `$1` is the script's **build-log output path** (line 17), so `lake build > "$LOG"` wrote
15,083 lines of build output over the file. v10 was untouched and nothing in version control was
harmed; v11 was rebuilt from its sources. Two disciplines follow, and §10.1 now carries the first:
check what a script does with a path before passing one, and commit a manuscript before running any
gate against it.

### B.12 v11 → v12

**Nothing removed.** `compile-diff` reported a deletion set of zero lines: 51 numbered results
carried at the same numbers with identical statement text, 27 `[OPEN]` sites carried, 8 retractions
carried and none re-claimed, no grade moved. Numbered results 51 → 63.

**Added.** §13 (Theorems 13.1–13.12, 28 Lean declarations outside the gated tree); Appendix A routes
6–9; the v12 paragraphs of §9; a scope paragraph in §7.

**Retracted in v12.** The `53/462` (half `53/924`) minimum uncovered length, as a floor. Theorem 13.2
shows the minimum decays like `H⁻²` for readings bounded by `H`. It stands as an exhaustive result
for readings `≤ 40` and was never a bound beyond that. The figure does not appear in v11 or earlier
manuscript versions; the retraction is against `INTEGER_CASE_v2`, `PERIODICITY_v1`,
`TWIN_CASE_THEOREM_v1` and `EXISTENCE_MAP` where it does.

**Corrected in v12 before promotion.** `compile-diff` returned nine findings against the added
material and all nine were fixed: a false claim that no §13 statement mentions the order `8` (ten of
them do, and are now marked order-8 specific); an axiom-clean claim with no deposited witness (now
`v12_new_axioms_v1.sh`/`.out`); nine measurements citing no script (now all cited, and one cited
script did not exist and was written); an incomplete list of insertions; a stale result count; no
version map; the new files missing from §10; two label collisions; and untagged results.

**Not adopted.** Two proposals that would have settled the conjecture — a `K ≤ 28` geometric ceiling
and a piecewise `R < 12` bound — were examined and rejected as unproved; see the header and
`CEILING_CLAIM_v1`. The Barajas–Serra line is kept out of the manuscript by the author's direction.

---

## Appendix C. Objections tested

Recorded from the objection ledger (append-only). Each objection was tested rather than argued. The figures are for the
construction as it stood when tested, 2026-09-14, before v8: a rule-based construction over lattice instants `p/(8D)` with
integer scales `D = k·d_min`. The present cascade (§6) has real scales `d/(8N + 1)` and no candidates.

**Objections that do not apply.**

| objection | outcome |
|---|---|
| Incommensurable speeds break it | 0 failures over 3,200 runner-instances with every difference irrational; the `√2/100` case cleared at `p = 3`, margin `+0.0495`, and at `p = 7`, margin `0`; now also proved on instances in Lean (§6.8) |
| Ties among the differences break it | 8,122 instances with repeated differences, 0 failures |
| It is an `n = 8` construction | the 2026-09-14 rules fired for 76.7–87.0% at `n = 5, 6, 7, 8, 9, 11, 12, 13`, and every instant produced was genuine, 23,703 of 23,703; §8 |
| It needs a global clock | `(3, 7, 12, 20, 29, 31, 44, 50)`: eight runners, five distinct instants, no instant at which all eight are lonely together |
| It needs the real-to-integer reduction | the test reads irrational differences directly (§2.2 band identity); `√2` is never approximated |
| Measure or density is required | inapplicable: the quantity such an argument bounds is zero for the progression, where the framework names `t = 1/8` (Appendix A, 1) |
| Covering, or counting the candidates | inapplicable by type: both conclude that some point survives, and the construction names which; a bound reaching 86.8% produced no instant |
| The test might not mean what it says | `D ≤ (a·e mod nD) ≤ (n−1)D` iff distance at least `1/n`: proved (Prop 2.1), and checked on 28,000 cases at `n = 5…13`, 0 disagreements |
| Producing an instant is not what is asked | an instant at which a runner is lonely is Existence for that runner (§6.7, Corollary 6.4) |

Testing the first exposed a restriction imported into the 2026-09-14 test: at first it appeared to fail, 82 of 2,400, because
the gap `D` had ranged over integers; with the gap taken as a scale the failures went to zero. The earlier restrictions of the
same kind were the first window, `p ∈ {1, 3, 5, 7}`, the lap as part of the output, and `a ≡ 1 (mod 8)`.

**Objections raised and found to be false blockers.**

| objection | why it was false |
|---|---|
| "The construction is not proved to always produce", from rule shares of 81.9% and 66.0% | a rule's share is not the construction's reach: the construction produced for 12,000 of 12,000 random runners and for every runner of every hard case on file |
| "The stepping is not proved to terminate", read as an unbounded search | each step is one move (§6.1), fixed by the runners in the way; no search is performed. What remains open is stated as Existence (§6.7) |
| "The gcd rule does not survive incommensurability" | the `d_min`-scaled construction produced for 1,600 of 1,600 all-irrational runners without it |
| "§7.4 has a counterexample", from `(1, 31, …, 225)` | it refutes v7's wording, which stopped at lap 0; read past lap 0 the runner is isolated (§6.8) |
| "Theorem 4.7 is an imported global obligation" | global isolation of the progression is the framework's reference ideal (§5); the per-runner reading of deviations gives the instants where the reference instant does not survive |

The pattern in each: a restriction placed on a search the construction does not perform — how long, how much of the space,
or when — read back as a limit of the construction.

**What remains.** The first three rows above withdrew those objections as they were framed. The obligation is Existence
(§6.7), open. The ledger's data from the 2026-09-14 rules, integer differences
at order 8 only: every runner those rules did not settle had at least one difference that is a multiple of `8g` (`g` the gcd of
the differences), two-thirds of them exactly one, and an instant was found at gap 2 to 11.


### B.9 From v9.5 to v9.6

| v9.5 | v9.6 | why |
|---|---|---|
| Lean target `LRC.Spec.ExistenceAt8`, over `ds : Finset ℝ`, `card ds ≤ 7` | `LRC.Spec.LonelyRunnerAt8`, over an injective `v : Fin 8 → ℝ` | `ExistenceAt8` is sufficient but not the same statement: decidable equality, duplicate collapse, sets no arrangement produces, and the arrangement discarded |
| the obligation stated on a difference set | `ExistenceOnArrangements`, `Iff.rfl` to the target | the obligation is the conjecture, not a reduction |
| `LRC/Cascade/`, nineteen modules, 4,709 theorems, 233 structural, digest `42742a6f…`, commit `83dd583` | twenty modules, 4,748 theorems, 272 structural, digest `d8ceb5ad…`, commit `58ba790` | `Arrangement.lean` is new; figures recomputed on disk for check [6] |
| — | `Arrangement.inWay_comm`, `lonelyAt_add_const`, `lonelyAt_const_mul` | three facts with no difference-set counterpart: symmetry between two subjects, nothing pinned at `0`, no free scale |
| — | `lonelyAt_iff_lonely_diffSet` | the bridge: for a fixed subject the predicate factors through its own disparities, so §6 applies verbatim without `ExistenceAt8` |
| numbered results | 28 | **28** — no numbered statement added, dropped or regraded |
| §10 `Spec/Target.lean` axiom witness: four declarations (`v9_2_spec_axioms_v1`) | fifteen theorems, every one in the module (`v9_6_spec_axioms_v1`) | the four-declaration artefact no longer described the file; the amendment's seven declarations sat outside it |
| §10 "the frozen target" | "the target (amended 2026-09-18)" | the file was amended the same day; the two statements contradicted each other |
| §6.7 boxed equivalence, unqualified | same, with a scope note | both its theorems are stated on `ExistenceAt8`, which is no longer the target |
| gate figure 4,749 theorems | **4,748** | a doc-comment line beginning `theorem` was counted as a declaration; see the header |

**What is not claimed.** Nothing in v9.6 proves Existence. `ExistenceAt8` is retained, still proved sufficient
(`lonelyRunnerAt8_of_existence`), and every `[OPEN]` of v9.5 is unchanged and still `[OPEN]`. The `card ds ≤ 3` case is
`[PROVED]` (`exists_lonely_of_card_le_three`); that it is the **only** excess is `[EMPIRICAL — 20,000 sets]`, its
construction written down but not formalised.

---

## Appendix D. The seven-flank margin

A runner with all seven flanks shadowed has no lonely instant at all (Corollary 6.4), which would
refute the conjecture at eight runners — a theorem (Rosenfeld 2025). So what follows measures the
**margin**, not the outcome. Exactness comes from Theorem 6.13: at a whole-number flank `e` the
verdict has period `e`, so `k = 0 … e−1` decides it; nothing here is sampled.

**Over every 7-subset of `[1,16]` with gcd 1** — 11,432 sets (`seven_flank_v1`):

| shadowed flanks | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|
| sets | 2,332 | 4,022 | 3,291 | 1,432 | 325 | 29 | **1** | 0 |

**The maximum is 6 of 7, attained at exactly one set in 11,432: `{2, 3, 4, 5, 6, 7, 16}`** — and its
dilates `{2, 3, 4, 5, 6, 7, 16m}` behave the same. That is precisely the critical family
`NearAP.lean` proves lonely, so the unique extremum in the range is the one the artefact already has
a theorem for.

**The margin at the extremum is two openings.**

| set | surviving flank | clear openings | first `k` | instant |
|---|---|---|---|---|
| `{2,3,4,5,6,7,16}` | 16 | **2 of 16** | 1 | `9/128` |
| `{2,3,4,5,6,7,32}` | 32 | 4 of 32 | 2 | `17/256` |
| `(1,3,7,14,21,49,56)` | 49, 56 | 11 of 49, 11 of 56 | 8, 10 | — |

**The surviving flank is always `d_max`.** `[DERIVED — arithmetic]` At `k = 0` the largest flank is
blocked for every arrangement: at `t = 1/(8·d_max)` every smaller disparity sits at
`d/(8·d_max) < 1/8`. The mirror of Theorem 4.8 clears it at `k = 1` when every ratio lies in
`[1/9, 7/9]`. So `d_max` cannot supply the `k = 0` instant that settles 48–64% of subjects, and it is
the last flank standing when the others run out.

**Two hardness directions, and they are not aligned.** `{2,…,7,16}` has 6 of 7 flanks shadowed but
only **63%** of its scale half-line covered by bad intervals; `(1, 31, 75, 97, 128, 160, 176, 225)`
has **98.9%** coverage but far fewer shadowed flanks. An argument closing one need not touch the
other. `[VERIFIED — exact]`

**Scope.** These are **disparity sets**, not arrangements: a 7-subset need not arise from eight real
speeds, so the enumeration is over a superset of the realisable configurations (§6.7's
`ExistenceAt8`-versus-`LonelyRunnerAt8` caveat). The counts are counts of disparity sets.
