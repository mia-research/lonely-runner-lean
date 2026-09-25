# Order eight — running log

**Append-only.** Entries are dated and never edited once written; a correction is a new entry that
names the one it corrects. Standalone versioned documents are reserved for a substantial result
(owner, 2026-09-25). Every figure cites the script and output that produced it. Grades:
`PROVED`, `VERIFIED` (exhaustive on a stated range), `EMPIRICAL` (sampled), `ASSERTED`.

Paths below are relative to `LonelyRunner/` unless they start with `docs/`.

---

## 2026-09-25 — E1. Cloud sessions synced

The three branches of `mia-research/lrc-n8-lean` were merged and applied as local commit `4a60afc`
(Spec gate PASS 1,518/1,518, `experiments/nN/spec_gate_n8cloud_sync.out`), plus `9d044f3` (the two
checks in `docs/n8/PROOF_SHAPE_REVIEW_2026_09_25_v1.md`). Not pushed at the time of writing: the
push was blocked by the Lean guardrail hook and is the owner's to run.

## 2026-09-25 — E2. Terminology, and the five-set bound re-checked

- **"Hard set" is the sessions' label for a rule-miss set**: a set in the session-start residual on
  which the `q ≤ 8` first-opening rule at the least multiple of `q` fails. It is a property of that
  rule, not of the arrangement. The cascade lands on the earliest lonely instant on all 1,436 of them
  (`experiments/nN/cascade_first_check_v1.out`). From here on this log says **rule-miss set**.
- The false five-set bound (review v1, Finding 5) was re-checked with the session's own `cells_of`,
  copied verbatim from `fast_pair_v1.py`: `(1, 3, 4, 5, 7)` gives `5/224`, cell × max `= 5/32`
  `[VERIFIED]`. Its random sample (seed 17, 19,689 distinct 5-sets) contains none of the 20 sub-`1/4`
  sets or their multiples. The bound was never formalised; the only Lean match for "longest" is an
  unrelated order-five comment (`OrderFiveObligation.lean:337`).

## 2026-09-25 — E3. Extra laps: settled

The sessions did not disagree on data; they measured different families (`any_lap_v1`: every
opening of the flank; `lap_null_v1`: laps `r ≤ 2`, 28 sets, one seed). On one object, the 1,436
rule-miss sets, with `lap_null_v1`'s family and null (`experiments/nN/lap_null_v2.out`):

| family | certifies | null |
|---|---|---|
| `r ≤ 0` | 0 | 1,334 ± 8 (selection: the sets are defined by this family failing) |
| `r ≤ 1` | 1,416 | 1,414 ± 5 (8 of 20 seeds ≥ family) |
| `r ≤ 2` | 1,432 | 1,426.4 ± 3.0 (17 of 500 seeds ≥ family, p ≈ 0.034 one-sided, three lap bounds tested) |
| any lap at the rule's flanks | 1,417 | 1,435.1 ± 1.1 with as many random flanks of `S` |

`[EMPIRICAL]` Extra laps give no mechanism a rule could stand on. At `r ≤ 2` there is a small excess
(4 misses against about 9.6), which is weak structure, not none. Any-lap at the rule's flanks does
worse than random flanks.

## 2026-09-25 — E4. The `L_0` ladder against the rational-opening fields — the fields look in the wrong place

Rules compared (`experiments/nN/ladder_vs_fields_v1.py`), both of the `(D, a)` form of
`docs/n8/PROOF_REQUIREMENTS_v2.md` §3, band `D ≤ d·a mod 8D ≤ 7D`:

- **ladder** (v2 numerators): the least `D` with some `a = 8j + 1`, `j < D`, clearing every `d`.
  Dead lattices (`8D | d`) never clear, so starting at `L_0` changes nothing.
- **fields** (`RationalOpening8`): `D = e ∈ S`, `N | e`, `a = 8i(e/N) + 1`; `N*` = least such `N`.

Results `[VERIFIED — exact, each instant re-checked with exact circDist]`:

- **The 7 `EightResidual` sets of `[1,40]` are lonely at `D = 3, a = 1` (`t = 1/24`) — six of them —
  and at `D = 5, a = 9` (`t = 9/40`).** The fields need `N* = 12, 15, 16` for the same sets. No
  smaller resolution clears any of them.
- **The ladder's resolution is almost never a disparity**: 96/1,436 rule-miss sets and 351/3,000
  random primitive 7-sets of `[1,60]` have `D*` in `S`. Ladder `D*` ≤ 10 (rule-miss) and ≤ 11
  (random); fields `N*` up to 24.
- SKETCH_v7's `p ∈ {1,3,5,7}` form finds nothing on 13/1,436 and 37/3,000. That is the restriction
  v2 §6 already lifted.

**Reading.** The residual is a product of the field `no_rational_opening` quantifying over `e ∈ S`.
The Lean certificate `lonely_eight_at_rationalOpening` already allows a flank that is not a
disparity (`N = 1`, `M = D`, `i = 0` gives `t = 1/(8D)`); only the field restricts it. A fixed
bound on `D` cannot close the residual: a set containing a multiple of `8·lcm(1..C)` kills every
`D ≤ C`. So the question moves to E5.

**Source note.** The "31,066 of 31,066, largest resolution 13" figure in
`PROOF_REQUIREMENTS_v1/v2` §7 has no script or output on disk (searched `docs/`, `experiments/`).
It is superseded for this purpose by E4/E5, which have artifacts.

## 2026-09-25 — E5. Live steps past `L_0`: small, scale-free, and smallest when the bottom is eaten

`k` = the number of live lattices in `[L_0, D*)` (`k = 0`: the first live lattice clears)
(`experiments/nN/ladder_live_steps_v1.out`) `[EMPIRICAL]`:

| sets | `k = 0` | max `k` |
|---|---|---|
| 1,436 rule-miss, largest 41..60 | 970 | 6 |
| 3,000 random primitive, `[1, 10³]` | 2,401 | 8 |
| 3,000 random primitive, `[1, 10⁶]` | 2,358 | 6 |
| adversarial, `8·lcm(1..c)` divides one or two elements, `c = 4..16` (1,000 each) | 785 → 960 | 3 at `c = 4, 6`; 2 at `c = 8..12, 16`; 1 at `c = 14` |

The worst case has `L_0 = 17`, `D* = 25`, `t = 33/200`, for
`(520, 676, 754, 2204, 9487, 11531520, 265224960)`, re-checked exactly. The live-step count does not
grow from `10³` to `10⁶`, and it **shrinks** when divisibility kills the small lattices.

**Reading, as a statement to test, not a result.** A rule in the contract's own terms is in view:
*take `L_0`; if it fails, take the next live lattice; some `a ≡ 1 (mod 8)` clears within `K` live
steps*. It is the §7 rule of `PROOF_REQUIREMENTS_v2`, now with `K ≤ 8` on 13,436 sets and an
adversarial family. Clearing at `D` depends only on `d mod 8D`, so the question at each lattice is
a counting question over the `D` numerators `a ≡ 1 (mod 8)` in `[0, 8D)`. The rung budget
(`lonely_eight_of_rung_budget`, proved) is the same kind of count, done at flanks that are
disparities. What is owed is the count at live lattices that need not be disparities, and a reason
the number of live steps stays bounded.

## Owed after E5

1. Worst cases for `k`: a targeted search, not random sampling, for sets that push `k` up (the
   `(33, 51, 231, 651, 744, 773, 996)` family at `k = 8` is the lead).
2. The blocked-numerator count at a live lattice `D`: for each `d`, how many of the `D` numerators
   `a = 8j + 1` it blocks, as a function of `gcd(d, 8D)`. This is the rung budget moved off the
   disparities.
3. Owner: whether to add a Lean field for small non-disparity resolutions, or restate the residual
   around the ladder.
4. The set-specific cell-length target (review v1, Finding 5) is still open. The cascade's landing
   cell is the first candidate to measure.

## 2026-09-25 — E6. The blocked-numerator count at a live lattice; the live-step count under search

`experiments/nN/blocked_count_v1.out`, `ladder_worst_search_v1.out`, `ladder_worst_search_v2.out`.

- At a lattice `D` the candidates `(8j+1)/(8D)`, `j ∈ ℤ/D`, read `d·t_j = d/(8D) + d·j/D`: in `j` the
  runner `d` walks the `h/D`-lattice through `d/(8D)`, `h = gcd(d, D)`, each point `h` times. So
  `B(d) = h · #{k < D/h : ‖d/(8D) + kh/D‖ < 1/8}` `[PROVED — two lines; VERIFIED 0 disagreements
  with brute force, d < 2000, D ≤ 40]`. A runner coprime to `D` blocks `⌊(D−1)/4⌋` to `⌈D/4⌉`; a
  runner with `D | d` blocks nothing on a live lattice.
- Seven coprime runners cost about `7D/4 > D`, so the union bound alone cannot clear a lattice of
  coprime runners. At the clearing lattice `Σ B(d) ≥ D` in 971 of 1,436 rule-miss sets: when the
  lattice clears, it is through **overlap** of the blocked sets, not their count `[VERIFIED]`.
- **E5's small live-step count is a sampling artefact.** Hill-climbing (elements up to `10¹²`)
  reaches `k = 13` (`L_0 = 3`, `D* = 18`), against `k ≤ 8` at random. `D*` has stayed at 25 or below
  in every search `[EMPIRICAL]`. Whether `k` is bounded is not settled; a congruence construction,
  not a search, would decide it. Per E4, a fixed cap on `D` cannot close.

## 2026-09-25 — E7. Lean: the resolution field

Commit `4e468cf` (`LonelyRunner/`). `OrderEightCasesN` §2g adds `ResolutionClears8`,
`lonely_eight_at_resolution` (the instant `(8j+1)/(8D)` named) and `lonely_eight_of_resolution`, and
`EightResidual.no_small_resolution` for `D ≤ resolutionCap8 = 64`, with its case in
`lonely_eight_or_residual`. Spec gate PASS 1,522/1,522 (`experiments/nN/spec_gate_small_resolution.out`).
On its own the field empties the session-start residual on `[1,30]` (12,309 sets, least `D ≤ 12`) and
`[1,40]` (91,523 sets, least `D ≤ 13`) `[VERIFIED — eight_residual_count_v6.out]`.

**Standing, read against the framework (E8).** `D` is not read off the arrangement: it is an integer
resolution, and its instant is **not a certificate**. It is a rule in the sense of R6's `1/q`
(`PAPER_v9_1` §2.1: "an instant named by a rule of §10 need not be one"); Localisation converts it to
an opening no later. Stated natively, the instant `(8j+1)/(8D)` is the spine point of the scale
`D/(8j+1)`, which is §6.10's candidate-scale form `e/(8k+1)` with an integer in place of a
disparity. The firewall's "no search" row concerns the cascade, and a Layer-2 case is a condition with
a proof, so the field has the case form. **That reading is the owner's to confirm.**

## 2026-09-25 — E8. Exhibit versus exist, from the framework's own text

Read: `PAPER_v9_1` §§2–9, 15, 18; `MANUSCRIPT_v20` §0, §1.2, §6.10, §6A.

- **The target is the right statement.** `LonelyRunnerAt8` is the conjecture at eight runners,
  closed condition, `t > 0`, every subject of every injective arrangement.
- **The `∃` in the Lean statements is the intended shape.** `MANUSCRIPT_v20` §6A: "The bound lives in
  the argument, not in the shape of the statement. Every result kept here concludes with an unbounded
  `∃` in Lean … read the proof, not the `∃`." §0 and `PAPER_v9_1` §18 admit pigeonhole,
  contradiction, induction or construction for a case. So an `∃` conclusion is not a defect; an
  argument that bounds no witness is.
- **For whole-number disparities the test is met by the form itself.** Every certificate lies in the
  finite family `e ∈ S`, `j < e` (Theorem 10), so any proof that a certificate exists bounds its
  witness by `max S`. And Theorem 13 turns any existence into an exhibited instant: the cascade from
  the bound halts at the first lonely opening. At whole numbers, exhibit and exist are one statement.
  The owed residual statement is of this kind.
- **The one link in the order-8 chain where the test is live is the real-speed step, not the integers.**
  `RealEightN`'s rank ≥ 2 case carries a model instant to a real time with
  `Stepping.exists_step_near`. That uses pigeonhole returns, with no density or measure, but
  `span_returns` argues by contradiction, so the integer time `K` has **no bound in the argument**.
  By §6A's own test that is the shape for which Props 6.10–6.11 were withdrawn. The same template
  serves orders five to seven (`RealFiveN` … `RealSevenN`). For arbitrary irrational speeds no bound
  can be uniform in `β`, so any bound would have to be stated in the arrangement's own
  Diophantine data. `[ASSERTED — flagged for the owner; not re-derived]`
- **Floating point.** Every ladder and band computation in E3–E7 is integer-exact. The one float
  check (`five_cell_floor_v1`'s grid) is replaced by BSM in `five_cell_floor_v2`: 0 disagreements on
  all 20 sub-`1/4` sets. Means and standard deviations of counts in the null tests are the only
  floats left.

## 2026-09-25 — E9. Owner rulings; the owed statement proved equal to the conjecture

**Rulings (owner, 2026-09-25).** (i) The resolution field of E7 is native: a rule in the R6 sense,
no different in kind. E7's "the owner's to confirm" is answered. (ii) Density has no use in the
framework, which works natively for all positive reals. Pigeonhole is a **tool**, not an object, so
`Stepping.exists_step_near` stands, and E8's flag on the real-speed step is withdrawn.

**`lonelyRunnerAt8_iff_residual`** `[PROVED — commit in LonelyRunner/, Spec gate PASS 1,524/1,524,
experiments/nN/spec_gate_residual_iff.out]`. The converse `residual_of_lonelyRunnerAt8` realises a
residual set as the disparities of the arrangement `(0, r₁, …, r₇)` for its subject, the runner of
speed 0. So the owed statement is **exactly** the conjecture at eight runners: it adds no pinned
runner, no first-instant demand and no bound on when.

**Where extra requirements do live**: in the OWED register, off this path. `RCapped` is a cap.
`FourClears` and `CoprimeLargestFlank` require the *largest* flank specifically. `WindowConstantFive`
requires a clear window of fixed length. `DoorFirstLap` (refuted) bounded when. The cloud sessions'
length step and "robust order-six lemma" (E2) were likewise stronger than the conjecture: a cell of a
given length at a lower order. The latter is false.

## 2026-09-25 — E10. What we need against what we have

**Corrections from the owner (2026-09-25).** The cascade is not a search and not an algorithm that
needs to terminate; it identifies an isolation event from the speeds. The framework neither
guarantees a first isolation event nor requires one. Earlier entries' "halts" and "terminates" are
superseded in that sense.

**Target.** `LonelyRunnerAt8 ↔` every `EightResidual` set is lonely at `1/8` (E9, proved).

### What we have — proved, Lean, axiom-clean

- **Layer 1, every order.** Localisation (`doors_agree`), the certificate's arithmetic form
  (Theorem 10), cascade equivalences (Theorem 13), mirror centre (`MirrorCentreN`).
- **Lower orders, framework form.** `n = 3 … 7`, whole numbers and real speeds (`RealFiveN` …
  `RealSevenN`); BHK Prop 11 and §5 at named instants.
- **Order-8 reductions.** Real → whole numbers (`RealEightN`); common factor; `card ≤ 6` by order 7.
- **Order-8 rules (the case list).** R1, R4, R6, R8, descent (shift budget), free flank, first lap,
  `−7` opening, rational openings at flanks (`N ∣ 8`, 3, 5, 6, 7, 9), resolutions `D ≤ 64` (§2g).
  Rung budget and link lemma.
- **General tools on disk, not yet used at order 8.** `MergeN` (merge rule), `WindowN` (sharp window),
  `WindowTwoN` (two-flank window at `1/6`), `TwoGroupsN` (two groups lined up by stepping, order 5),
  `DescentN` / `DescentMultiN`, `SelfSimilarN`, `Stepping`.

### What the residual contains — it is NOT empty

Every finite window tested is empty (E7), but members exist. Three families were constructed and all
verified exactly (integer band test plus exact `circDist`):

| family | how built | members | what clears them | artifact |
|---|---|---|---|---|
| core + fast block with a large common factor | 5 runners in `[1,100]` plus `L·u, L·u'`, `L = 8·lcm(1..64)`, `u' ≤ 7u` | 162 of 3,000 | **block split**: core lonely at `1/6` (order 6) gives a window `1/(12·max C)`; the pair repeats with period `1/gcd`, lonely at `1/3` (order 3) in each period; `gcd ≥ 12·max C` puts one in the window. 162/162 | `residual_members_v1`, `block_split_v1` |
| core + fast pair, no common factor | as above, second large runner in `(d/7, d)`, `gcd ≤ 10⁶` | 163 of 3,000 (138 with no certificate at any core flank) | **fast pair**: every window of length `3/(4a)` holds a point where both `a ≤ b` are clear; with the core's window this needs `min F ≥ 9·max C`. 163/163 | `residual_members_v2`, `fast_pair_window_v1` |
| **no separation of scale** (`max/min < 9`) | `d₁ = 8·lcm(1..64)·u` kills every `D ≤ 64`; the other six hill-climbed to satisfy every field | 22 in 150 restarts (0 of 5,900 at random: the free flank and the cost field remove them) | **the first live lattice past the cap, `L₀ = 67`, clears all 22** (no blocked live lattice) | `residual_members_v3`, `v4` |

The two-runner window constant: the longest run with no common clear point, times `a`, is at most
`305/616 ≈ 0.495` over `1 ≤ a ≤ b ≤ 80`, against the `3/4` used `[VERIFIED]`. The lemma's proof is
three lines: a window meets at most one open zone of `a`, and `b` crosses a quarter lap in either
remaining piece. `[ASSERTED, not in Lean]`

### What we need

1. **Fast-block rules, in Lean.** Block split and fast pair are native (two lower orders, a window,
   a named instant) and generalise R8 (a block of one). Owed: the two-runner window lemma at `1/8`
   (analogous to `WindowTwoN` at `1/6`); the period argument for a block with a common factor
   (commensurable analogue of `TwoGroupsN`); the two cases and their fields. **This is the cloud
   sessions' length step done correctly**: the core's window comes from its order margin, which is
   proved, and the block is fast, so no uniform cell bound (E2, review Finding 5) is needed.
2. **The lattice rule past any cap.** Scale-free residual members clear at the first live lattice.
   A cap is a case boundary, and the rule that would close it is PROOF_REQUIREMENTS_v2 §7's: some
   live lattice at or just past `L₀` clears. Against it, the live-step count reaches 13 under search
   (E6). What is owed is the mechanism. The union bound fails at a lattice of coprime runners (E6), so
   the count has to see **overlaps** of blocked sets; the link lemma is the one overlap tool in hand.
3. **The organising principle.** The evidence splits the problem on **separation of scale**:
   - separated sets are carried by lower orders with margin (R8, block split, fast pair, descent);
   - scale-free sets are carried by lattices.

   A proof needs this dichotomy stated as cases whose conditions are jointly exhaustive. That means
   a quantitative separation threshold on one side, and on the other a lattice argument valid at
   every set whose consecutive ratios stay below it.

### On whether the named-witness standard is what is blocking a proof

Logically a named witness is not required, and for whole numbers it costs nothing (E8). **On the
evidence so far it is not the obstacle.** Every rule found today names its instant as a matter of
course: block split, fast pair, and the lattice at `L₀`. The proved rules already argue "the blocked
candidates cannot cover" as counts (rung budget, descent shift budget), which the framework admits as
tools. The obstacle is mathematical and specific: at a lattice of mostly coprime runners, first-order
counts over-spend (`7D/4 > D`), and a proof needs control of the overlaps.

## 2026-09-25 — E11. Rulings; AP deformations at scale; the log-time form; the list revised

**Rulings (owner, 2026-09-25).**
- (i) The owner holds that the cascade **guarantees** the isolation event exists: it carries the AP's
  global isolation (φ(n) law) to local isolation as the speeds deform. Recorded as the owner's
  position. Two facts stand beside it:
  - the Lean tree proves the equivalence "event ⇔ lonely", and the unconditional statement at order
    8 is still the hypothesis of `lonelyRunnerAt8_of_residual`;
  - `PAPER_v9_1`'s abstract calls isolation surviving deformation what "the Lonely Runner Conjecture
    asserts".

  Along linear deformation paths (`deformation_v1.out`), the cells descended from the AP's events die
  early (λ ≈ 0.13–0.36), and loneliness at the target is carried by cells **born** along the path:
  every cell is born in 27/28 rule-miss and 30/30 random residual sets `[EMPIRICAL, one path per set]`.
  A deformation argument has to carry births, not only the original events.
- (ii) **Covering is admissible now.** The ban was needed early to clear out what did not apply; with
  the framework developed, the owner will entertain covering arguments.
- (iii) Scale invariance: tests must not be scale-blind. The AP is scale invariant.

**AP deformations at scale** (`near_ap_scale_v1`, `v2`; exact):
- Random ±3 deformations of `k·(1..7)`, `k = 10², 10³, 10⁴`, are settled mostly by R6 (171/158/146
  of 200): an arithmetic accident.
- Searched *for* residual membership (240 restarts, `|eᵢ| ≤ k/100` and `k/10`, `k` up to `10⁵`): **no
  member found**. Within 1% the §15 first-lap and −7 openings carry them; within 10% the `N = 6, 7, 9`
  openings and the resolution field do.
- So E10's scale-free residual members, built around `d₁ = 8·lcm(1..64)`, are arithmetic
  constructions. They are not deformations of the AP.

**The log-time form** `[PROVED — two lines]`. With `x = log t`, `aᵢ = log dᵢ`, and the fixed set
`G = ⋃_{M≥0} [log(M + 1/8), log(M + 7/8)]`, the subject is lonely **iff some translate of the
configuration {aᵢ} lies inside G**. The speeds enter only through the configuration; scaling is
translation; there are no lattices and no divisibility.
- The first tooth `[log 1/8, log 7/8]` has length **exactly `log 7`**. R1 is "fits in the first tooth",
  and the AP (span `log 7`) fits with zero slack: its tightness, read in this picture.
- First-lap clearance is "six in the first tooth, the flank on a tooth's left edge".
- Teeth and gaps shrink like `1/M`, with the gaps' share tending to `1/4`: seven translates of the
  blocked set are not excluded from covering by share alone (`7/4 > 1`).
- Separation of scale is a gap between consecutive `aᵢ`. If every gap is `< log T`, the configuration
  spans `< 6 log T`: **up to scaling, the scale-free remainder is a bounded region.**

### The list, revised

1. **State the obligation in log-time form** (Lean, short). Scale invariance becomes exact, and it
   gives covering arguments a translation-invariant setting.
2. **Separation-of-scale rules.** In hand: a fast block of one (R8, proved); a fast pair (verified
   163/163, window lemma to formalise); a block with a large common factor (verified 162/162; uses
   the block's full LRC over its period, formalise). **Newly visible gap:** a fast block of `f ≥ 3`
   runners **without** a common factor needs a *robust window*: every window of length `κ/min F` holds
   a point where the block is clear at `1/8`, whatever phase the window starts at. That is a
   shifted-start statement for `f` runners, and it is not in hand. The shifted Lonely Runner
   Conjecture (Beck, Hoşten and Schymura 2019, *Lonely Runner Polyhedra*) is the literature's name for
   that shape `[CITED — not verified; citation-verifier owed before any use]`. Whether the organising
   split can always put the gap where `f ≤ 2`, or use a common factor, is open.
3. **The bounded remainder.** With covering admitted, arguments on a bounded region of
   configurations become available. **Tight configurations are where they must be done by hand**: at
   the AP the clear set is isolated points, so no neighbourhood carries an instant. Session 2's sign
   rule (`ap_sign_rule_v1`) is the local analysis at the AP. Its four instants cover four cones of
   deformation directions, and whether those cones exhaust the directions is not checked. The
   deformation data above says born cells take over.
4. **The integer ladder is demoted to a rule.** It is a divisibility device, not a scale-invariant
   one. It emptied every finite window and clears the scale-free arithmetic members at `L₀`. It stays
   in the case list, but it is not the organising principle.
