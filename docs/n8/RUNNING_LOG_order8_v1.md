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

## 2026-09-25 — E12. The AP's end runner is locally robust; log-time and the fast pair in Lean

**Owner's points recorded.**
- The straight-line path of `deformation_v1` was session 1's choice and is not the deformation the
  cascade reads. The births and deaths it counts belong to that path, not to the arrangement.
- Global isolation (the AP's simultaneous event) is not runner isolation, and the conjecture asks
  only for the latter.
- The owner holds that per-runner isolation can be carried through deformation given the runner's
  neighbouring speeds (closest faster, closest slower). The precise statement is to come from the
  owner before it is tested.

**Correction to E11 ("they are not deformations of the AP").** That was inferred from how the sets
were built, not measured. Measured scale-invariantly (`ap_distance_v1.out`,
`ρ(S) = min_k maxᵢ |d₍ᵢ₎/(k·i) − 1|`):
- the 22 scale-free residual members sit at `ρ = 0.39 … 1.51` (median 1.01);
- the near-AP sets searched sit at `ρ ≤ 0.07`.

Every arrangement is a deformation of some AP (`MANUSCRIPT_v20` §2.3). The right statement is that
the members are **large** deformations. Between `ρ ≈ 0.07` and `0.39` no search for residual members
has been run.

**The AP's end runner under any small deformation** `[PROVED — below; VERIFIED ap_local_v1.out]`.
Deform the disparities `1..7` to `d_k = k(1 + r_k)`, `|r_k| ≤ ρ`.
- **Class 1**, `t = 1/(8d₁)`: runner 1 reads exactly `1/8`; runner `k` reads `(k/8)(1+r_k)/(1+r₁)`.
  For `k = 2..6` that is at least `2/8` from an integer, less at most `(6/8)·2ρ/(1−ρ) < 1/8` when
  `ρ < 1/13`. Runner 7 reads `(7/8)·d₇/(7d₁) ≤ 7/8` iff `d₇ ≤ 7d₁`.
- **Class 7**, `t = (6 + 1/8)/d₇` (opening `j = 6` of the largest flank): runner `k` reads
  `(7k/8)(1+r_k)/(1+r₇)`. For `k = 2..6` that is at least `2/8` from an integer, less at most
  `(42/8)·2ρ/(1−ρ) < 1/8` when `ρ < 1/85`. Runner 1 reads `(7/8)·7d₁/d₇ ≤ 7/8` iff `d₇ ≥ 7d₁`.

So for `ρ < 1/85` the end runner is lonely at one of two named instants, and exactly one of
`d₇ ≤ 7d₁`, `d₇ ≥ 7d₁` holds (both on the boundary). **Its isolation moves from class 1 to class 7 as
`d₇/d₁` crosses 7 and never vanishes.** The deciding runners are `d₁` (the nearest speed) and `d₇`.
Sampled: 4,000/4,000 at `ρ = 1/100`. The fixed-instant sign rule (session 2, instant held at `a/8`)
certifies 1,973/4,000: holding the instant fixed was what made it scale-blind.

**Lean** (commit `412b3bf`, Spec gate PASS 1,536/1,536, `experiments/nN/spec_gate_logtime_fastpair.out`):
- `LogTimeN`: `lonely_iff_translate_mem` (real disparities, every `n ≥ 2`): lonely iff some translate
  of `{log d}` lies in `G n`; `translate_scale`: scaling is translation.
- `FastPairEightN`: `pair_window` (every window of length `3/(4a)` holds an instant clearing
  `0 < a ≤ b` at `1/8`) and `lonely_eight_of_fast_pair` (core of at most five at `1/6` by order six,
  `9·max C ≤ a ≤ b`). `OrderEightCasesN` §2h: `FastPair8`, its case, and the field `no_fast_pair`.

**Still owed from E11's list.**
- The block split in Lean (a block with a large common factor).
- The robust-window question for fast blocks of three or more.
- Tight configurations other than the AP.
- The owner's neighbour-speed statement.

## 2026-09-25 — E13. Neighbours fix the isolation point; tight sets; windows; the block split; the cascade map

**Owner (2026-09-25).**
- The cascade's sequence of scales is the path the isolation takes: each step re-reads the
  arrangement as an AP plus deviations at a finer scale.
- The neighbours that fix a runner's isolation point are its two **circle** neighbours at the global
  event (for runner 8 at `t = 1/8`: runners 1 and 7). The other five deviate from their global
  isolation points but stay inside their sections of the circle.

**Every runner of the AP, not only the end runners** `[reasoned; VERIFIED ap_neighbours_v1.out]`.
- At `t = a/8` subject `k`'s circle neighbours are `k ± a (mod 8)`. With the other five in their
  sections, Theorem 1 leaves two constraints linear in `t`, one per neighbour.
- The feasible instants form an interval whose ends are the neighbours' openings. It is nonempty iff
  one ratio of the two neighbours' speed differences lies on one side of a fixed value. The mirror
  class `8 − a` reverses the inequality.
- So in each pair `{1,7}` and `{3,5}` one class survives, at an opening of a neighbour.
- Exact check: at relative deformation `≤ 1/200`, both pairs survive for all 12,000 subject-trials. At
  `1/100`, `{3,5}` survives 12,000/12,000 and `{1,7}` 11,996. Failures begin only when a non-neighbour
  leaves its section.

**Tight configurations** (`tight_search_v1`, `v2`; exhaustive, exact, BSM boundary rule).
- Among 1,180,572 primitive 7-subsets of `[1,28]`, every set is lonely and exactly three are tight:
  `(1..7)`, `(1,2,3,4,5,7,12)` and `(1,4,5,6,7,11,13)`.
- All three are lonely only at `1/8, 3/8, 5/8, 7/8`, and each class is pinned from both sides by
  neighbours at `±1/8`. For class 1 that forces `1` and `7` in the set, which all three contain.
- Tightness is the two-neighbour pinning, so the neighbour analysis applies at each.

**Robust windows for fast blocks** (`robust_window_v1`; exact). Worst stretch with no common clear
point, times `min F`:

| block size | exhaustive max | growth along consecutive blocks `N..N+f−1`, `N = 20 → 160` |
|---|---|---|
| 2 | 0.49 | bounded (≤ 3/4 proved, `pair_window`) |
| 3 | 0.72 | 0.69 → 0.74, bounded |
| 4 | 1.12 | 1.09 → 1.23, bounded |
| 5 | 2.02 | 2.1 → 11.2, **grows linearly** |
| 6 | 2.12 | 3.0 → 17.2, **grows linearly** |

Reason for the growth: a nearly synchronised block rotates at rate `≈ N` while its internal spread
changes at rate `≈ f`. When the spread lays five or more runners with gaps under `1/4`, one is always
blocked, for a time independent of `N`. **No window rule exists for fast blocks of 5 or 6 without a
common factor.** Such a block is an AP translated by `N`, which returns it to the AP analysis.

**The block split in Lean** (Spec gate PASS 1,539/1,539, `spec_gate_block_split.out`).
`BlockSplitEightN.lonely_eight_of_block_split`: a block with common factor `g ≥ 28·max(core)`,
order seven only. `OrderEightCasesN` §2i: `BlockSplit8`, its case, the field `no_block_split`.

**The cascade map** (`cascade_map_v1`; exact).
- Along the cascade from the bound, no runner is in the way at more than 4 steps (1,436 rule-miss
  sets) or 3 (1,500 random sets); paths are at most 11 steps.
- The runner that sets each move is the subject's nearest runner on that side of the circle in
  2,345/2,533 moves (93%), and 1,236/1,404 (88%) on random sets.
- Theorem 13(5) makes finiteness of these per-runner counts equivalent to the event existing, so the
  map is the per-runner form of the obligation. A **bound** on the counts would be a cap-shaped
  statement; the analogous move-count shape is false at order five (`MANUSCRIPT_v20` §16B), so none
  is claimed.

## 2026-09-25 — E14. Confinement to AP segments, tested along the cascade

**Owner's claim.** Placing every runner in its AP segment at the cascade's scale means only the two
neighbours can be in the isolation zone; the other five are confined to their segments.

**Test** (`cascade_zone_v1.out`; exact). At each cascade step `t = 1/(8D)`, reading `s = d/D`. The
zone is `s` within 1 of a multiple of 8. Steps with two or more runners in the zone on one side:
**616/2,533** (rule-miss sets) and **349/1,404** (random 7-sets of `[1,200]`).

Example: `(9, 16, 31, 73, 111, 150, 151)` at `t = 1/72`, `D = 9`, readings `1, 1.78, 3.44, 8.11,
12.33, 16.67, 16.78`. Runners 73, 150 and 151 are each inside an AP segment, `[8,9]` and `[16,17]`,
and those segments are the subject's own zone modulo 8.

**Reading.** Confinement holds when the readings sit near `1..7`: the AP and its small deformations
(E12, E13). Once readings exceed 8 the segments wrap and several runners can share segment 0 or 7.
**Open, for the owner:** which placement is meant.
- (a) By reading: refuted as above.
- (b) By speed rank: the rank-4 runner 73 reads 8.11.
- (c) By a choice of scale that makes the placement work: then its existence is the obligation.

This entry corrects E13's "roughly 10%": the 7–12% there counts moves not set by the nearest runner,
which is a different statistic.

## 2026-09-25 — E15. "The same location around the curve": what it means, and why E14 does not test it

**Owner (2026-09-25).**
- Any arrangement can be read as an AP. The AP is scale invariant, so once the speeds are fixed the
  scale is established; deviations move the local isolation away from the global event, but it
  occurs at the same location around the curve.
- The development had AP / GRID (and enlarged) tiers: where the speeds do not fit the AP, the grid
  at the runner's own scale acts as an AP.
- The cascade finds the scale that is used.

**What this is, in the framework's proved terms.** In the normalised coordinate `u = D·t` every tier
places the isolation at the spine points `p/8` of its own scale. The sharpest form is proved:
`MANUSCRIPT_v20` Theorem 6.15 with 6.16. Every flank opening is the first spine point `u = 1/8` of
the candidate scale `D = e/(8k+1)`, and the subject is lonely iff some candidate scale is clear. The
cascade's final scale is that `D`: it lands at `t = 1/(8·D_final)`. **So "the same location" is a
theorem.** What is open is only that a clear scale exists for every arrangement.

**Worked example** (exact): `(9, 16, 31, 73, 111, 150, 151)`.
- The owner's gap `15` works: at `D = 15` the spine point `p = 3` clears (`t = 3/120 = 1/40`), as do
  the numerators `a = 9, 17, 25, 49, 57, 65, 73`.
- The cascade starts at `D = d_min = 9`, where 73, 150 and 151 are in the way. In one move it reaches
  `D = 73/9` (candidate scale `e = 73`, `k = 1`), lonely at `t = 9/584`, with runner 73 exactly at
  the threshold. That is the first isolation, earlier than `1/40`.

**E14 withdrawn as evidence.** E14 counted runners in the zone at the cascade's intermediate
scales. Those are, by construction, the scales where runners are in the way: that is what makes the
cascade move. The example above is E14's own example, at the cascade's starting scale. E14 measures
nothing about the owner's claim.

**`slot_order_v1` recorded as testing a stronger, different claim**: that all seven other runners
keep their octagon slots at the isolation instant. The test itself is sound (AP: all four classes
for every subject; small AP deformations 800/800, `slot_order_v1_sanity.out`). The claim holds near
the AP and fails away from it (60/400 rule-miss, 661/2,400 random). The owner did not make it. It is
not evidence against "the same location".

## 2026-09-25 — E16. Toward a finite proof: the plan, the synchronised block, the tight sets

**Owner (2026-09-25).** If the scale is set by the arrangement there are only finitely many
arrangements: the AP is scale invariant, and mod `n` converts the rest. Any arrangement must
produce a scale; the question is how to prove it.

**Where finiteness enters, and where it does not** (reasoned).
- Scale invariance fixes `d_min = 1`; the ratios remain a continuum and are unbounded.
- Mod 8 reduces the band test at **one** scale. The cascade's next scale `D·s/(8N+1)` depends on
  `s` itself, not on `s mod 8`.
- Finiteness enters through **compactness**. On a region of bounded ratios, every non-tight
  configuration has a lonely cell of positive length, so one certificate works on an open
  neighbourhood of it; tight configurations are covered by the two-pinner lemma below. So finitely
  many certificate types cover the region.
- Compactness does not create existence. The cover must be **built and verified** (covering is
  admissible, owner ruling E11).
- Unbounded ratios fall to the separation rules.

**The plan.**
1. Close the separation side for every block size.
2. Local analysis at every tight configuration.
3. Choose the separation threshold, size the bounded region, then build and verify a finite
   certificate cover exactly.

**Step 1: the synchronised block** `[Lean: SyncBlockN, gate PASS 1,541/1,541]`. For a block
`{N + eᵢ}` with offsets `0 ≤ eᵢ ≤ E`, the common phase makes a full turn in `1/N` while the offsets
move `≤ E/N`, so the phase is a free shift (`sync_block`, `lonely_of_sync_block`, any block size, real
speeds). Blocks of 5 and 6, which have no window rule (E13), reduce to the `N`-free question

> **R(C, e):** some `t₀` inside the core's clear set leaves the offsets `{eᵢ t₀}` with a gap `> 1/4`.

R holds in all **288,288** cases with speeds in `[1,16]` (f = 5 with a core of 2, f = 6 with a core
of 1). 80% of them fall to the easy case: the core clears before `3/(4E)`, where the offsets bunch
together. The full rule at `N = 10⁶` is lonely exactly in 300/300 (`sync_block_v1`, `v2`).
**R is not proved; it is the separation side's remaining statement.**

**Step 2: every tight configuration so far is locally robust** (`tight_local_v1`; exact). All three
tight sets keep their isolation under deformations up to `1/100` at the openings of the class pair
`{1,7}`, 2,000/2,000 each. In `(1,4,5,6,7,11,13)` the pair `{3,5}` is weaker: class 3 is pinned by
three runners (11 at `+1/8`; 5 and 13 at `7/8`).

**Two-pinner lemma** `[PROVED — below; any order]`. Let a whole-number set be lonely at an isolated
instant `t*` pinned by exactly two runners, `d₊` reading `+1/8` and `d₋` reading `−1/8`. Deform
`d ↦ d(1 + r_d)`, small.
- At `t*` the constraints are `t ≥ (N₊ + 1/8)/d₊'` and `t ≤ (N₋ + 7/8)/d₋'`. Both equal `t*` before
  deformation, so the interval survives iff `r₊ ≥ r₋`.
- At the mirror `1 − t*` the pinners swap sides and it survives iff `r₊ ≤ r₋`.
- So one of the two always survives, at an opening of a pinner. The condition is scale-invariant,
  and the pinners are the subject's circle neighbours at `t*`: the owner's neighbour rule in general
  form.
- The other runners need slack (a radius depending on the set, e.g. `1/85` at the AP, E12).

## 2026-09-25 — E17. R: proved for cores not divisible by 7, and read off the cascade; the two-pinner lemma in Lean

**R at the seventh** `[PROVED — Lean SyncGridN, gate PASS 1,548/1,548]`. At `t = a/q` whole-number
offsets sit on the grid `(1/q)ℤ`. At most six offsets leave one of seven slots empty, so the gap is
`≥ 2/7 > 1/4`, whatever the offsets are (pigeonhole, a tool). A core runner not divisible by 7 reads
at least `1/7` from the integers there. `lonely_of_sync_grid`: a core with no element divisible by 7
and a synchronised block of at most six runners, `N ≥ 56·max`, is lonely at a named instant in
`[1/7, 1/7 + 1/N]`.

With `q ∈ {2,3,6,7}` the grid criterion settles 281,008/288,288 cases with speeds in `[1,16]`, with
no error (`sync_R_grid_v1`). It misses only (f = 6) `42 | c`, and (f = 5) a core with elements
divisible by 6 and by 7. No single grid can reach those: past `q = 7` the offsets can fill the grid,
and by CRT one choice of offsets can fill every small grid at once.

**What the cascade shows** (owner: "look at the cascade and the isolation events";
`sync_divisible_cascade_v1`, `sync_first_event_v1`; exact).
- On 396 divisible-core sets, the full set's isolation sits in the **core's first lap** in every case,
  mostly right at the core's first opening, with the block contributing only its free phase. Only 10
  events lie near a small-denominator fraction. The grids were an artefact of my method; the
  mechanism is the core's own isolation event.
- **R′** (offsets gapped at the core's first isolation event) holds in 283,246/288,288.
  - Of the 5,042 failures, 5,008 have gap exactly `1/4`.
  - Just inside the core's first cell, all but 184 are gapped.
  - Those 184 isolate later in the core's first cell (177) or after its second lonely opening (7).
- Typical survivor: offsets forming an AP, `(0, 3, 6, 9, 12)`, evenly spaced at the core's opening
  until the AP's spread opens a gap. The owner's AP structure appears inside the block.

**Owed for R in general**: within the core's first two isolation cells, the offsets open a gap
`> 1/4`. Its hard instances are offsets in AP. `[EMPIRICAL — all 288,288 cases in [1,16]]`

**The two-pinner lemma** `[PROVED — Lean TwoPinnerN]`.
- `pinners_clear_at_opening`: with `λ₋ ≤ λ₊` within the band's slack, the opening `(N₊ + 1/8)/(d₊λ₊)`
  keeps both pinners clear.
- `mirror_readings`: at `1 − t*` whole-number pinners swap sides.
- `two_pinner`: one of the pinned opening and the mirror opening always keeps both pinners clear.

Scope: the pinners only. The other runners' slack is a set-specific radius, a separate hypothesis.

## 2026-09-25 — E18. The skeleton in Lean; the cascade is a map; the continuity route from global isolation

**Owner (2026-09-25).**
- The cascade is not a search function.
- For any arrangement it identifies the scale.
- The event it identifies rests on the AP's global isolation, deformed.
- Global isolation can be proved by the φ(n) law.

**The cascade, stated as a map** (correcting E16–E17's algorithm words: "terminates", "halts",
"runs"). The cascade is a map on instants fixed by the speeds: an instant goes to the largest next
opening of the runners in the way there, and stays where none is. Its fixed point is the isolation
event, at `u = 1/8` of the scale `D_final` (Theorems 11, 6.15). What a proof must establish is that
**this map has a fixed point for every arrangement**, a property of the map, which Theorem 13 makes
equivalent to loneliness.

**The skeleton** `[PROVED — Lean Order8SkeletonN, gate PASS 1,557/1,557]`. Split on separation of
scale at `T = 9`: separated (a slow core and a fast block of `f` runners) or scale-free. The split
cannot leak.
- `lonelyRunnerAt8_of_holes`: the conjecture at eight runners follows from exactly five named OWED
  statements, `BlockRule8 3/4/5/6 9` and `BoundedCovered8 9`.
- Block sizes 1 and 2 are discharged (`blockRule8_one` by R8, `blockRule8_two` by the fast pair).
- The cascade's own route, `DoorFAM` ↔ lonely (`doors_agree`), stands beside it.

**The continuity route (the owner's deformation argument, made exact)** `[reasoned; not in Lean]`.
Take any path of speeds from the AP (`λ = 0`) to a target (`λ = 1`), and let `Λ` be the set of `λ`
at which the subject is lonely.
- `0 ∈ Λ` by the φ(n) law.
- **`Λ` is open.** A lonely set with a cell of positive length has an interior instant with margin,
  which survives small changes of speed. A lonely set of isolated points only (a tight
  configuration) survives by the two-pinner lemma.
- **`Λ` is closed** if the lonely instants stay in a bounded window along the path: a limit of lonely
  instants is lonely, loneliness being closed.

So `Λ = [0,1]`. The argument concerns the lonely **set**, so the deaths and births along a path
(`deformation_v1`) do no harm. It reduces the deformation argument to two statements:
1. **Persistence at every tight configuration.** The two-pinner lemma covers an isolated instant with
   exactly two pinners at commensurable speeds (its mirror step uses a period). Needed: every tight
   configuration is commensurable and has such an instant, or a version for three or more pinners.
   All three known tight sets are whole-number sets with the pinner pair `{1, 7}`.
2. **No escape to infinity along the path.** A bound on lonely instants, used as a compactness tool.
   It is not a cap on the cascade and asks nothing of when the event falls.

## 2026-09-25 — E19. Statement 1 of the continuity route settled on paper; statement 2 is the integer conjecture

**Statement 1 (isolation survives at tight configurations): no classification of tight sets needed.**
1. **Tight ⇒ commensurable** `[reasoned from RealEightN; Lean owed]`. If the disparities span two or
   more rational directions, `RealEightN`'s rank ≥ 2 argument applies: the exact merge leaves at most
   six readings, order 7 clears them at `1/7`, and stepping (`lonely_of_model_many`) carries them to a
   real time at `1/8`. Stepping with half the error allowance (`η = σ/(2C)`) leaves every reading
   **strictly** above `1/8`, so a small interval is lonely: the lonely set has interior, and the
   configuration is not tight.
2. Commensurable configurations lie on countably many rays (scaled whole-number sets), and a path in
   configuration space can avoid countably many lines except at its endpoints.
3. At the AP, persistence is proved: the end runner by the two-pinner lemma (class 1 or 7, E12); the
   interior runners are not tight.

So along a suitable path the set of lonely stages is **open**.

**Statement 2 (no escape to infinity) is the conjecture at whole numbers** `[reasoned]`. If the target
were not lonely, the first stage `λ*` with an empty lonely set cannot have rank ≥ 2 (those are always
lonely, point 1). So `λ*` is a whole-number configuration with no lonely instant. Closedness is
therefore **equivalent to the conjecture at integer arrangements**. The deformation from global
isolation reduces the problem to whole numbers, exactly the reduction `RealEightN` already proves;
it does not settle it.

**Reading.** The owner's picture is exact in this sense: global isolation deforms, and the only place
it could ever be lost is at a whole-number arrangement. The remaining work is at that level: the
skeleton's five holes, the cascade on integer speeds, the band test mod 8.
- New equivalent form, not yet explored: a whole-number set `S` is lonely iff nearby rank-2
  configurations (all lonely) have lonely instants that stay bounded as they approach `S`.

## 2026-09-25 — E20. Correction: the "tight configurations" of E13/E16/E17/E19 were read in a stationary frame

**Owner (2026-09-25).** No runner is to be made stationary.

**What was wrong.** `tight_search_v1/v2` enumerated 7-element **difference sets** and E13–E19 called
each one a "configuration" (e.g. "the tight set `(1,4,5,6,7,11,13)`"). That fixes one runner, the one
at speed 0, as a global reference and treats its difference set as the arrangement: the stationary
frame the framework excludes (`PAPER_v9_1` §2.2, "no pinned runner"). Reading `v_j − v_i` is
legitimate only as "is runner `i` lonely"; it is not a description of the arrangement.

**Restated correctly.** `(1,4,5,6,7,11,13)` is the difference set of the runner at speed 0 in the
arrangement `{0,1,4,5,6,7,11,13}`. For that runner, isolation is at `t = 1/8` (the AP at gap 1) and
happens at a single instant, because the runners at differences 1 and 7 sit exactly on `1/8` and `7/8`
there. The arrangement as a whole, every runner read in its own differences (exact cascade):

| runner | cascade moves | isolation | scale | tier |
|---|---|---|---|---|
| 0, 1, 4, 6, 7 | 0 | `1/8` | 1 | AP, gap 1 |
| 5 | 1 | `9/64` | `8/9` | enlarged: its difference 8 is a full lap at gap 1 |
| 11, 13 | 0 | `1/16` | 2 | grid at `d_min = 2` |

The owner's reading, "AP gap 1 and let the grid take care of it", is what the cascade does.

**Scope of the correction.**
- E13's and E17's per-runner results (neighbour pinning, the two-pinner lemma) are statements about
  one runner's reading, and stand as such.
- Every place where "tight configuration" was used as a property of an arrangement (E13 table,
  E16 step 2, E17, E19's "tight ⇒ commensurable") should be read as "a runner whose isolation
  happens at isolated instants". E19's reduction (the continuity route ends at whole-number
  arrangements) is unaffected, since it quantifies over each runner's own reading.

## 2026-09-25 — E21. AUDIT: everything built in a pinned frame is void; the redo begins

**Owner (2026-09-25).** Any conclusion or finding that uses a stationary runner must be done again.
The framework's rules are integral, not decoration. Mod n could not be used because the first
runner's speed had been set to 0.

**The rule broken** (`MANUSCRIPT_v21` §1.1): *"Each runner is treated independently: the construction
is performed identically and separately for each of the eight, and no runner is held stationary."* §4:
global isolation iff the **reduced speeds** form a complete residue system mod n; a grid is an AP with
whole extra laps. §6.7: a difference-set enumeration counts only because *"every runner of every
arrangement was evaluated"*. This session built one runner's difference set, putting that runner at
speed 0, treated it as the object, and evaluated only that runner.

**VOID until redone.**

| entry | voided |
|---|---|
| E2 | five-set cell floor |
| E3 | lap null |
| E4–E7 | ladder vs fields, live steps, the resolution field's evidence |
| E9 | the converse `residual_of_lonelyRunnerAt8`, which builds the arrangement `(0, r₁, …, r₇)` |
| E10 | residual members, block split and fast pair evidence |
| E11 | AP deformations at scale |
| E12 | the end-runner analysis with disparities deformed |
| E13 | tight search, robust windows, cascade map |
| E14, E15 | zone and slot-order tests |
| E16, E17 | R, the synchronised-block evidence, the grid-at-7 rule and "divisible by 7", divisible-core cascade readings, tight-set local analysis |
| E18 | the skeleton's `Separated8`, stated on difference sets |
| E19 | "tight ⇒ commensurable" |
| review | `PROOF_SHAPE_REVIEW_2026_09_25_v1` findings built on difference sets |

**Kept as lemmas about one runner's readings** (their supporting evidence is redone):
- `sync_block` (reals)
- the two-pinner algebra
- `pair_window`
- `lonely_iff_translate_mem`, `translate_scale`
- the blocked-count formula
- `ap_neighbours_v1`, which deformed the **speeds** of all 8 runners and evaluated every runner and
  stands as is.

**The redo's rule.**
- Objects are arrangements of 8 distinct positive speeds, none zero.
- Every runner is evaluated in its own readings.
- AP / grid / mod 8 are read on the arrangement's reduced speeds.
- The diagnostic is the cascade run per runner: scale, tier, isolation event.

Shared code: `experiments/nN/redo/arrangement_lib.py`.

**Redo 1: the synchronised block** (`redo/sync_arrangements_v1.out`, `redo/long_cascades_v1.out`; exact).
900 arrangements: a slow group of 1–3 runners (random; multiples of 7; multiples of 42) and a fast
cluster at `10⁵ + e`. **All 7,200 runners reach their isolation event.**

| slow group | AP | grid | enlarged |
|---|---|---|---|
| random | 1,015 | 817 | 568 |
| multiples of 7 | 995 | 848 | 557 |
| multiples of 42 | 1,006 | 900 | 494 |

The distributions of tiers and cascade moves do not depend on divisibility by 7 or 42: **"divisible by
7" was an artefact of the pinned frame.** The only long cascades (191 and 688 moves) are slow runners
whose fast cluster is itself an AP (gaps 11 and 13). The cascade walks through the cluster's AP and
lands where its spread leaves a gap.

## 2026-09-25 — E22. Redo items 1–2: isolated runners and the AP, on arrangements

**Redo 1b: runners lonely only at isolated instants** (supersedes `tight_search_v1/v2`;
`redo/isolated_runners_v1_B20.out`, `_B24.out`; exhaustive, exact, BSM boundary rule).
- Every arrangement of 8 distinct speeds in `[1,24]` with gcd of differences 1, **every runner**:
  734,478 arrangements, **5,875,824 runners, every one lonely**.
- 2,690 runners are lonely only at isolated instants, always at `1/8, 3/8, 5/8, 7/8`. Their readings
  form exactly three sets: `{1..7}` (1,534 runners), `{1,2,3,4,5,7,12}` (830) and
  `{1,4,5,6,7,11,13}` (326).
- At `1/8` each is pinned by the runners at distance 1 (ahead) and 7 (behind); the cascade isolates
  it in 0 moves, AP tier.
- **The arrangements are mostly not APs.** Readings `{1..7}` arise wherever the other seven sit at
  `k ± i` with any choice of sides. The runner reads its own AP; the arrangement need not be one.

**Redo 1c: persistence under deformation of the arrangement** (supersedes `ap_local_v1`,
`tight_local_v1`; `redo/isolated_persistence_v1.out`; exact).
- 150 arrangements from `[1,24]` containing isolated runners, **every speed** deformed by `|r| ≤ ρ`,
  every runner's event read with the cascade map.
- **All runners reach their event at every radius**: isolated runners 1,216/1,216, the others
  8,384/8,384.
- At `ρ = 1/400`, 1,123 of the isolated runners' events sit within `1/64` of a class instant
  (classes 1, 3, 5).

**Redo 2: the AP arrangement `(1..8)` deformed** (`redo/ap_arrangement_v1.out`; exact; extends
`ap_neighbours_v1`, which already stood).
- Every runner reaches its event, 2,000/2,000 at every `ρ` from `1/10` to `1/200`.
- **The owner's neighbour rule holds exactly at `ρ ≤ 1/50`**: every event near a class instant is
  pinned by one of that runner's two circle neighbours at the global event (1,830/1,830 at `1/50`,
  1,954/1,954 at `1/100`, 1,987/1,987 at `1/200`).
- At larger deformations a non-neighbour sometimes enters the sector and pins the event instead
  (1,298/1,319 at `1/20`, 835/894 at `1/10`), and more events move off the class instants: the cascade
  moving the isolation to another scale.

## 2026-09-25 — E23. Redo items 3–4, the cascade map, the five-reading floor, the lap null — on arrangements

All in the framework's frame: arrangements of distinct positive speeds, every runner evaluated in its
own readings. Exact.

**Item 3: separation of scale** (`redo/separation_arrangements_v1.out`; supersedes the pinned-frame
separation evidence).
- Three families (uniform in `[1,10⁶]`, clustered, slow-plus-fast), **9,600 runners, all reach their
  isolation event.**
- Separated runners with a block of 1 or 2 readings are covered by proved rules (R8: 978, fast pair:
  1,205).
- Blocks of 3–6 are covered by no proved rule, but the cascade isolates every one (clustered family:
  AP 989, grid 936, enlarged 535). The block split rarely applies to arrangements not built with a
  common factor.
- The frame shows itself: in slow-plus-fast arrangements a fast runner sees the slow runners as its
  block of 1–3 (R8, fast pair), while a slow runner sees the fast cluster as a block of 5–6.

**Item 4: the residual and the ladder** (`redo/residual_arrangements_v1_B24.out`; supersedes
`eight_residual_count_v6`, `ladder_vs_fields_v1`, `ladder_live_steps_v1`). Every arrangement in `[1,24]`,
**5,875,824 runners**:
- 2,271,460 have collided readings (fewer than seven distinct; order seven).
- 21,404 have readings in the session-start residual.
- **0** have readings in `EightResidual` with the resolution field.
- Ladder: least clearing resolution `≤ 13`, live steps past `L₀` `≤ 10`.

**Cascade map** (`redo/cascade_map_arrangements_v1.out`; supersedes `cascade_map_v1`). 8,000 runners
of random arrangements in `[1,200]` and `[1,10⁶]`:
- every cascade takes `≤ 10` moves;
- no runner is in the way at more than 4 steps;
- the move is set by the subject's nearest runner on that side in 3,587/3,952 (91%) and 3,614/4,167
  (87%) of moves.

**Five-reading floor** (`redo/five_floor_arrangements_v1.out`; supersedes `five_cell_floor_v1/v2`). Every
runner with five readings in every arrangement of 6 speeds in `[1,30]`: least (longest cell × largest
reading) = `5/32`, readings `{1,3,4,5,7}` and `{1,4,5,6,7}`. **Unchanged**: it depends only on a
runner's readings, and is now established over runners of arrangements.

**Lap null** (`redo/lap_null_arrangements_v1.out`, `_v2.out`; supersedes `lap_null_v1/v2`).
- Arrangements in `[1,24]` contain no rule-miss runner.
- The 1,436 known rule-miss reading sets, realised as a runner at speed 100 inside 4,308 arrangements
  (others at `100 ± r`, all speeds positive): every runner of those arrangements reaches its event,
  34,464/34,464.
- The family/null figures are **unchanged** (0 / 1,416 / 1,432 against 1,334 / 1,414 / 1,426), as they
  depend only on the runner's readings.

**What the redo changed, and what it did not.**
- **Changed:** "divisible by 7" was an artefact (E21). The "hard cases of R" are a fast cluster that is
  itself an AP. The "tight sets" are runners whose own readings form one of three sets, in
  arrangements that are mostly not APs (E22). The neighbour rule is confirmed exactly for every runner
  of the deformed AP at `ρ ≤ 1/50` (E22).
- **Unchanged** (reading-level statistics, now established over arrangements): the five-reading floor
  `5/32`; the lap null.
- **Still to redo, needs the owner's say (Lean):** `residual_of_lonelyRunnerAt8` builds the arrangement
  `(0, r₁, …, r₇)`; the skeleton's `Separated8` is stated on difference sets.

## 2026-09-25 — E24. Lean restated in the arrangement frame; the rule for blocks of 3–6, read off the cascade

**Lean** (Spec gate PASS 1,561/1,561, `experiments/nN/spec_gate_arrangement_frame.out`).
- `residual_of_lonelyRunnerAt8` realises a residual set as the readings of the runner at speed 1 in
  `(1, 1 + r₁, …, 1 + r₇)`: every speed positive, no runner at rest.
- `Order8SkeletonN` restated: `readingsOf v k` (a runner's own readings), `Arr8` (eight distinct
  positive speeds), and the OWED holes `ArrBlockRule8 f 9` (f = 3..6) and `ArrBoundedCovered8 9`,
  quantified over arrangements and every runner. `lonelyRunnerAt8_of_arrangement_holes` proves the
  conjecture at eight runners from them.
- Blocks of 1 and 2 are discharged by `blockRule8_one` and `blockRule8_two`, lemmas about a runner's
  readings. The set-form holes are withdrawn.

**Owner: "there must be a rule, it isn't random, it's a deterministic system."** Read off the cascade
(`redo/block_rule_probe_v1.out`, `v2.out`; exact). 3,107 separated runners with blocks of 3–6, from
arrangements in three families, every runner:
- The runner's isolation event `t*` equals the **core's own isolation event** `τ_C` in 1,337 cases and
  lies strictly between `τ_C` and `2τ_C` in the other 1,770: **never at or beyond `2τ_C`**. The core is
  the runner's slow readings, its nearest speeds.
- It lies in the **core's first lonely cell** in 3,093/3,107, pinned by a block reading (1,756), a core
  reading (1,130) or both (221).
- The block usually makes many turns in that cell: 16 or more for about 2,400.
- **The 14 exceptions:** the block makes 5–352 turns in the first cell yet has no joint clear instant
  there, because it contains a nearly synchronised sub-pair (e.g. core `[1,14,15]`, block
  `[1239, 1286, 1292, 1320]`: 1286 and 1292). The event then falls in a later core cell, still before
  `2τ_C`. This also shows the window constant for blocks of 4 (E13) was too optimistic: nearly
  synchronised sub-pairs stretch the blocked runs.

**The rule in the owner's terms** `[EMPIRICAL — 3,107 runners]`. The runner's near neighbours fix the
scale and the event (`τ_C`). The fast block only has to find a clear phase inside the core's lonely
cells, which it does in the first cell unless it contains a nearly synchronised sub-cluster, and
within `[τ_C, 2τ_C)` always.

**What a proof of it needs.** A statement that the block, fast relative to the core, has a joint clear
instant inside the core's lonely cells before `2τ_C`. Its hard instances are blocks containing nearly
synchronised sub-clusters, which the synchronised-block reduction treats as one runner with a free
phase.

## 2026-09-25 — E25. The block rule derived from the cascade; sections; the window-constant detour dropped

**Owner (2026-09-25).**
- The cascade knows which isolation events happen in one or more cycles, so the rule can be derived.
- Using the cascade is not compute heavy.
- At the isolation point the runners not pinning it sit in their sections, so their exact positions
  are not needed.

**Derivation from the synchronised-block lemma, checked against the cascade**
(`redo/block_rule_derived_v1.out`, `v2.out`; 3,107 separated runners with blocks of 3–6, arrangements,
every runner).
- A block splits into synchronised clusters. Each cluster's common phase is free; it imposes only that
  its offsets leave a gap `> 1/4` (plus drift). Clusters of `≤ 3` always do (gap `≥ 1/3`).
- The cluster's offsets are slow quantities and effectively join the core's level. That is why the
  event can move past the core's first cell: core `[1,14,15]`, block `[1239, 1286, 1292, 1320]` =
  base 1239 with offsets `{0, 47, 53, 81}`.
- As a **construction** (core clear with room for one turn; clusters' phases chosen slowest first,
  each inside the window where the slower levels stay clear; final instant checked exactly), it
  produces an exactly lonely instant before `2τ_C` for **2,855/3,107**.
- The failures are all blocks made of several clusters at **comparable** scales, neither synchronised
  nor separated (e.g. core `[8382]`, clusters `[141719], [162436, 179569], [252480], [291750],
  [644004]`): a scale-free level inside the block, where the cascade (not a phase choice) finds the
  instant.

**Sections** (`redo/sections_v1.out`). Segments 1–6 lie at distance `≥ 1/8` from the subject.
- At the core's own event, every non-pinning core reading is in segments 1–6; they crowd segment 1
  (1,607 of 4,157), just past the zone.
- At the runner's event, non-pinning core readings again crowd segment 1 (3,426 of 5,979). Non-pinning
  block readings spread nearly evenly over segments 1–6 (2,616 … 1,760): their phase is free, which is
  the synchronised-block reduction seen directly.

**Dropped.** The window-constant measurements (`level_window_v1/v2`) were a detour toward a proof tool.
The cascade gives each event directly and cheaply (3,107 runners in seconds). The runs were stopped and
the files removed.

## 2026-09-25 — E26. The block rule as the cascade read level by level; the non-pinners near their points

**Owner (2026-09-25).** At the isolation point the five non-pinning runners are near their isolation
point (their slot) but not on it.

**Measured** (`redo/slot_deviation_v1.out`; exact). At each runner's event, deviation of every
non-pinning runner from its nearest octagon point (slot units; random positions: mean 0.25, 25% within
1/8):

| runners | mean deviation | within 1/8 |
|---|---|---|
| scale-free | 0.23 | 31% |
| separated | 0.21 | 39% |
| the 252 | 0.22 | 35% |

2,856 of 42,088 non-pinners sit exactly on a point. So the effect is **real but modest** away from the
AP neighbourhood (near the AP it is exact, E22). If "their isolation point" means the **specific** slot
given by rank at the global event, that version is still to be measured.

**The block rule, derived from the cascade** (`redo/nested_cascade_v1.out`; exact; 3,107 separated
runners with blocks of 3–6, arrangements, every runner).
- **Rule:** start at the core's own event `τ_C` (the runner's slow neighbours fix it); run the block's
  cascade from there to the first instant where the block is clear; if the core is not clear there,
  the core's cascade carries it to its next clear cell, and the block's resumes.
- This lands exactly on the runner's event in 3,107/3,107 (by construction: both are the first instant
  after `τ_C` where everything is clear).
- **Handoffs:** 0 for 3,062, 1 for 44, 2 for 1. **The 252 the phase construction missed all take 0**: the
  block's own cascade finds its clear instant inside the core's first cell. The phase construction
  failed there only because it could not choose phases for several clusters at comparable scales.

**What a proof of the rule needs** (in the framework's objects):
1. From any start, the block's cascade reaches a block-clear instant. The block has at most six
   readings, so it is lonely at `1/(f+1)` by order `f+1 ≤ 7` (native), and for whole-number readings its
   lonely instants recur with its period.
2. That instant falls in a core-clear cell within a bounded number of handoffs (observed `≤ 2`).
   Statement 2 is the content.

## 2026-09-25 — E27. Own-slot test; statement 2 of the block rule splits on a doubly pinned core

**Owner (2026-09-25).** At a runner's isolation point every other runner is within `1/8` either side of
its own isolation point.

**Own-slot test** (`redo/own_slot_v1.out`; exact; every runner). Each runner's own vertex is taken by
**rank** at the global event, `((rank_j − rank_k)·a mod 8)/8`, best class `a`. Every other runner is
within `1/8` of it in:

| arrangements | holds |
|---|---|
| AP deformed by up to `1/20` | 1,179/2,000 |
| AP deformed by up to `1/5` | 207/2,000 |
| uniform | 66/2,000 |
| clustered | 24/2,000 |
| slow-plus-fast | 39/2,000 |

It holds near the AP, not in general, with rank as the reference. Open for the owner: whether the
intended reference is the grid's **residue** slot (a grid is an AP with lapped runners, slot = reduced
speed residue mod 8). With "nearest vertex" as the reference, "within `1/8`" is automatic and carries
no information.

**Statement 2 of the block rule** (`redo/handoff_cause_v1.out`, `v2.out`; 3,107 separated runners, block
3–6; exact).
- The offsets explanation is **refuted**: 44 of the 45 handoff runners have their offsets gapped at
  `τ_C`.
- **Every handoff has a core pinned on both sides at its first isolation.** At `τ_C = 1/(8a)` a core
  reading `a` sits exactly at `1/8` and a core reading `(8m+7)·a` exactly at `7/8`, observed pairs
  (1,7), (1,15), (2,14), (4,28), (1,47), (2,46), (2,30). The core's first lonely cell is then a single
  point.

| core at its first isolation | no handoff | handoff |
|---|---|---|
| not pinned on both sides | **3,009** | **0** |
| pinned on both sides | 53 (block clear at that point) | 45 (44 × 1, 1 × 2) |

**So statement 2 splits:**
- **2a:** when the core's first isolation has room, the block has a clear instant inside the core's
  first cell `[EMPIRICAL — 3,009/3,009]`.
- **2b:** when the core is pinned on both sides by `a` and `(8m+7)·a`, the block lands in a later core
  cell within at most two handoffs `[EMPIRICAL — 45/45]`.

This is the owner's two-neighbour picture at the core's level: the core's own two pinners decide
whether the block has room at the first event.

## 2026-09-25 — E28. The block rule, unified: the core's first isolation, or its first cell with room

**Owner (2026-09-25).** The AP absorbs deviations of up to `1/8` either side, which is why deforming
it works. Away from the AP, at higher speeds, runners settle onto grids: an AP with a variable scale.
So a runner's own point is its grid slot at the scale its arrangement reads at (not its rank; E27's
own-slot test used rank).

**Statement 2b** (`redo/pinned_core_v1.out`; 98 runners whose core is pinned on both sides at its first
isolation `τ_C = 1/(8a)`).
- Predicted from the two pinners alone, the core's next cell starts at the behind-pinner `b`'s next
  opening `t₁ = (8m+9)/(8b)`. True in 72/98.
- Otherwise another core reading near its zone is in the way at `t₁` (core `[1,14,15]`: 14 is in the way
  at `17/120`, and the next instant is its opening `17/112`).
- In general the core's next cell is given by **the core's own cascade continued past `τ_C`**.
- The block then makes from ~1 to thousands of turns in that cell (median about 555).

**The unified rule** (`redo/block_rule_unified_v1.out`; exact; after fixing a cell-end error that
treated a reading exactly at `7/8` as not yet in its zone):

> A separated runner's isolation event is at the core's first isolation `τ_C` if the block is clear
> there; otherwise it lies in the core's **first lonely cell of positive length** (from the core's
> cascade).

It holds for **3,107/3,107** separated runners with blocks of 3–6: 1,337 at `τ_C`, 1,770 in that cell.
`[EMPIRICAL — arrangements, every runner]`

**What proving it needs.**
1. The core (at most five readings) has lonely cells of positive length, since it is lonely at
   `1/(c+1) > 1/8` by lower orders (native); its cascade reaches the first one. Provable.
2. **The block has a jointly clear instant inside the core's first positive-length cell.** This is the
   remaining content: a fast block (min `≥ 9·max core`) in a cell set by the core's neighbours.

## 2026-09-25 — E29. Statement 2 (the block clears inside the core's first cell with room): what bounds each side

`redo/block_in_cell_v1.out`, `v2.out`; exact; the 1,770 separated runners whose block is not clear at the
core's first isolation. Measured in turns of the block's slowest reading: **available** = the core
cell's length, **needed** = from the cell's start to the block's first jointly clear instant (block
cascade).

| block | runners | available (min / median) | needed (median / max) | least margin |
|---|---|---|---|---|
| no nearly synchronised sub-cluster | 50 | 0.73 / 10.4 | 0.073 / 0.375 | 0.54 |
| with a nearly synchronised sub-cluster | 1,720 | 0.33 / 151 | 0.153 / 144 | 0.20 |

- **Needed never exceeds available** (3,107/3,107 overall, E28).
- Only **4** runners need more than 2 turns. All have a single-reading core (`[1]` or `[3]`) and a
  six-reading synchronised cluster (e.g. `[99961, 99974, 99990, 99992, 100003, 100007]`, spread
  `E = 46`). The wait is set by the cluster's spread: needed × `E` ≤ 0.385. The block waits while its
  offsets, turning at rate `E`, rotate out of an evenly spread arrangement. The single core runner's
  cell `3/(4c)` accommodates it.

**Structure of a proof of statement 2** (reasoned from the data; not proved).
- **(i) Non-synchronised levels:** a window lemma. The block clears within a bounded fraction of a
  turn of its slowest reading, observed `≤ 0.375` from the cell's start.
- **(ii) Synchronised clusters:** the common phase is free (`sync_block`). The wait is the offsets' gap
  condition (R in the arrangement frame), on the time scale `1/E` of the cluster's own spread.
- Both are lower-level instances of the same problem (fewer readings, one level down the scale tree).
  That points to an **induction on the scale structure**: each level is carried by the level below it,
  as orders 3–7 were carried by lower orders.

## 2026-09-25 — E30. The induction on the scale tree, stated and tested at every level

**Definitions.** Take runner `k`'s readings `R`, sorted.
- The **scale tree** cuts `R` wherever consecutive readings jump by ratio `≥ 9`, giving levels
  `L₀ < L₁ < … < L_m`.
- A **synchronised cluster** is a run inside a level with consecutive relative gaps `≤ 1/9`.
- `U_j = L₀ ∪ … ∪ L_j`, and `τ_j` is `U_j`'s first isolation event (its cascade).

**Base** `[provable, native]`. For `j < m`, `U_j` has at most six readings, so it is lonely at
`1/(|U_j|+1) > 1/8` by lower orders and has lonely cells of positive length.

**Step(j), as tested** (`redo/scale_induction_v1.out`, `v2.out`; exact; four families of arrangements,
every runner, 9,604 steps at every level `j` of trees with up to 5 levels). Level `j` lands:

| where level `j` lands | steps |
|---|---|
| at `τ_{j−1}` itself (clear there) | 5,543 |
| in `U_{j−1}`'s first lonely cell of positive length | 4,053 |
| in the second such cell | 8 |

- The 8 cells passed over were all narrower than **0.21 turns** of level `j`'s slowest reading.
- "The first cell of positive length" alone fails 8/9,604, because of those cells.
- Stated as **"the first cell of positive length wide enough for level `j`, and never beyond the
  second"**, the step holds 9,604/9,604 `[EMPIRICAL]`.

**Conclusion.** Step(`m`) gives the runner a lonely instant. So loneliness of every runner whose readings
have a gap follows from the Base and the Steps. Scale-free runners (`m = 0`) are the bounded region.

**What a proof of Step(`j`) needs** (level `j` is at least 9 times faster than `U_{j−1}`):
1. **Room**, guaranteed by the Base. `U_{j−1}` (`u ≤ 6` readings) is lonely at `1/(u+1)` somewhere, and
   the margin gives a cell of length `≥ 2(1/(u+1) − 1/8)/max U_{j−1}`. That is at least
   `9·2(1/(u+1) − 1/8)` turns of level `j`: 0.32 (`u = 6`), 0.75 (5), 1.35 (4), 2.25 (3), 3.75 (2),
   6.75 (1).
2. **Level `j` clears inside such a room.**
   - (a) Non-synchronised levels: observed within 0.54 turns from the cell's start (E29: 0.375 for the
     top level).
   - (b) Synchronised clusters: the common phase is free (`sync_block`); the wait is set by the cluster's
     spread, on the time scale `1/E` (E29).

These are the two lemmas of E29, now as the one step repeated down the levels.

## 2026-09-25 — E31. The owner's hunch on narrow cells confirmed; the non-synchronised step level by level

**Owner's hunch: the narrow cells are a ratio of speed differences against the AP ideal.**
`[identity + VERIFIED on all 8, redo/narrow_cells_v1.out]`
- A cell starting at scale `D` (`t = 1/(8D)`) has width `min_c (8m+7 − c/D)/(8c)`: it ends when the
  reading whose ratio `c/D` sits just short of an AP value `8m+7` (the AP's `7/8` slot) enters its zone.
- Each of the 8 narrow cells of E30 is ended that way, with shortfalls 0.004–0.09 of a slot:
  `956/1.9958 = 478.996` vs 479; `12063/807 = 14.948` vs 15; `2398/0.9996 = 2398.993` vs 2399.

**The non-synchronised step, per level size** (`redo/room_vs_kappa_v1.out`; exact interval merge).
- A fast level of `f` readings sits above `u = 7 − f` slower ones.
- **Room:** the lower orders guarantee a slower-level cell of `ROOM(f) = 18(1/(u+1) − 1/8)` turns of the
  level's slowest reading.
- **κ:** the longest the level (no consecutive pair within relative `1/9`, max/min `< 9`) can stay
  blocked from any start, in the same units. κ is scale-invariant.

| `f` | ROOM | κ, exhaustive (small readings) | κ, sampled (mildly synchronised) | status |
|---|---|---|---|---|
| 1 | 0.32 | 0.25 (one zone) | — | **proved: R8** |
| 2 | 0.75 | 0.75 (`pair_window`) | — | **proved** |
| 3 | 1.35 | 0.685 | 0.745 | margin ×1.8 `[EMPIRICAL]` |
| 4 | 2.25 | 1.054 | 1.172 | margin ×1.9 `[EMPIRICAL]` |
| 5 | 3.75 | 1.470 | 1.744 | margin ×2.2 `[EMPIRICAL]` |
| 6 | 6.75 | 2.763 | 2.273 | margin ×2.4 `[EMPIRICAL]` |

- The "tight case" of E30 (six slower readings) has room for exactly one fast reading, which **R8
  already proves**.
- **Route to a proof** for `f = 3..6`: κ depends only on ratio shape, a bounded region (consecutive
  ratios in `[10/9, 9)`), and κ sits about half its room. That margin makes a finite, certified check
  over the ratio region practical: a covering argument (admissible, E11).
- Synchronised levels are carried by `sync_block` (the common phase is free).

## 2026-09-25 — E32. What the non-synchronised step must cover; the cascade's workings in a blocked stretch

**Phases.** E31's κ was measured over one period of whole-number blocks, i.e. only the phases a small
block reaches on its own orbit. Over all arrangements, and as readings grow, a level's orbit fills out
its phase torus. A **uniform** step ("every window of length ROOM holds a clear instant") must therefore
hold for **every** starting phase: a region of `2f − 1` dimensions (`f − 1` ratios, `f` phases).
`full_phase_kappa_v1` (a light local search) found no value above the whole-number ones, and the
whole-number values are valid lower bounds for it. All known values sit below ROOM.

**Owner: the cascade is not a black box.** Traced through the longest blocked stretch of the worst block
of each size (`redo/cascade_trace_worst_v1.out`; exact). **A blocked stretch is a relay:**
- at almost every move exactly one runner is in the way, the one that has just entered its zone at
  `7/8`;
- the move goes to its opening at `1/8`, where the next runner arrives at `7/8`;
- the stretch lasts exactly as long as these handoffs line up.

The long relays are runners travelling **in formation**. In `(10, 13, 16, 19, 29, 35)` (κ = 2.763) the
AP `10, 13, 16, 19` (common difference 3) sits in consecutive eighths (slots 6, 7, 0, 1 at `t = 0.375`)
and passes through the zone in turn (19, 16, 13, 10; later 13, 16, 19), with 29 and 35 filling the gaps.
The relay breaks when the train drifts out of formation, at a rate set by the **differences between the
speeds**: the owner's hunch, seen in the mechanism.

**Route to the non-synchronised step, in the framework's terms** `[proposed]`: bound a relay's length by
its train's formation lifetime, which the speed differences control (and the non-synchronised condition
bounds below).

**Certification in progress** (`certify_f3_v1`, exact rational interval branch and bound, `f = 3`, all
shapes and phases, window = ROOM(3) = 27/20 turns). First run to a 3,000,000-evaluation cap:
1,498,439 boxes certified, **no refuting centre**, 173 boxes open (not complete). Re-running with the
certified volume tracked.

## 2026-09-25 — E33. The law of delayed isolation, found by perturbation

**Certification abandoned.** `certify_f3_v1` (exact branch and bound, `f = 3`, all shapes and phases):
after 3,998,406 certified boxes, **0.0001%** of the volume, stuck near relay configurations, no
refutation. Brute certification is the wrong tool; the cascade's mechanism is the right one.

**Owner (2026-09-25).**
- Take arrangements that delay the isolation, perturb them, and find the exact ratio at play.
- The aim: existence of isolation is held proved (deformation of global isolation); what must be shown
  is that **every arrangement is finite**, i.e. no arrangement only moves the isolation event around.

**Perturbation** (`redo/perturb_delay_v1.out` … `v3.out`; exact).
- Arrangement `[8, 12, 38, 100005, 100016, 100027, 100038, 100048]`, runner 8: 191 cascade moves.
  Moving any one fast speed by `≥ 2` drops it to 1–6 moves; within a window about 2 wide it stays at 191
  (or 784). The last speed is irrelevant. **A resonance.**
- Family: slow `[8, 12, 38]` and a fast train `N + (0, d, 2d, 3d)` plus a tail. Only `d = 10` and
  `d = 11` resonate; there the move count grows in proportion to `N` (`d = 10`: 1,044 / 2,086 / 4,169 /
  8,336 at `N = 5×10⁴ … 4×10⁵`), and the **delay in time is independent of `N`**.

**The law.** Let `t_C` be the core's opening instant, fixed by the runner's slow neighbours (`3/80`
here). The fast train's **speed differences** times `t_C` place its offsets on the circle.

| `d` | offsets × `t_C` | largest gap | delay (time) |
|---|---|---|---|
| 9 | `0, 27/80, 27/40, 1/80, 31/80` | `13/40 > 1/4` | about `1/N` |
| **10** | **`0, 3/8, 3/4, 1/8, 1/2`** | **exactly `1/4`** | **`1/240 = 1/(8·30)`**, every `N` |
| **11** | `0, 33/80, 33/40, 19/80, 49/80` | `19/80 < 1/4` | **`≈ 1/2640 = (1/4 − 19/80)/33`**, every `N` |
| 12 | `0, 9/20, 9/10, 7/20, 29/40` | `7/20 > 1/4` | about `1/N` |

- If the largest gap exceeds `1/4`, there is no delay.
- Otherwise the event is carried along for the time it takes the offsets, moving at rates equal to the
  speed differences, to open a gap. That time is set by the **differences relative to the core's scale**,
  not by `N`. The move count grows with `N` only because each relay move lasts about `1/N`.
- The owner's hunch, "a ratio of the difference between speeds, or from the AP ideal", is this law:
  resonance is the train's offsets sitting on eighth-slots (the AP ideal) densely enough to leave no gap.

**Finiteness mechanism** `[reasoned]`.
- For whole-number differences the offsets all return to 0 together within one period
  `1/gcd(differences)`, where the train bunches and leaves a gap `> 1/4`. So the train cannot hold the
  relay beyond one such period.
- What remains is whether the core is still clear then or hands off to its next cell: a question at the
  core's scale about the core plus the train's differences, the same problem one level down.

---

## E34 — 2026-09-25 — the train at its period points (Lean), and the handoff law at the core's scale

**1. The bunching bound, proved** (`LRC/Spec/SyncPeriodN.lean`, gate: `experiments/nN/spec_gate_sync_period.out`).
- `block_clear_at_period`: a fast block `{N + e}` whose offsets are all multiples of `g`, at the period
  point `t₀ = k/g`, is clear at `1/8` at the named instant `t₀ + fract(−1/2 − N t₀)/N ∈ [t₀, t₀ + 1/N)`,
  whenever `8·Emax ≤ 3N`. There every offset reads a whole number, so the train is one point of the
  circle and the phase `1/2` clears all of it.
- `lonely_at_period`: with a core clear on that turn, core and block are clear together.
- `[PROVED]`, no `sorry`, no `native_decide`. **What it does not cover:** a core that is blocked at every
  period point (e.g. `g` divides every core reading). Item 2 shows that case does not arise as a barrier
  in the arrangements run, but the lemma alone does not close it.

**2. The handoff at the core's scale** (`experiments/nN/redo/handoff_search_v1`, `handoff_directed_v1/v2/v3`).
- Random offsets in `[1,80]` bunch too rarely: 0 handoffs in 4,000 arrangements. So the bunching was
  built in: subject `s`, core `s + a, s + b` with `b/a` just short of 7 (a narrow first cell), and train
  `s + N + j·d`, offsets spread round the circle with no gap `> 1/4` at the core's opening `t_C = 1/(8a)`.
  Every runner is run through the exact cascade.
- **Prediction, exact and independent of `N`:** `t_pred` = the first instant `≥ t_C` at which the core is
  clear and the train's **shape** (offsets × `t`) leaves a gap `≥ 1/4`. Both conditions change only at
  breakpoints `c·t ∈ ℤ ± 1/8` and `(eᵢ − eⱼ)·t ∈ ℤ + {0, 1/4, 3/4}`, so `t_pred` is a finite exact
  computation. The fast phase `N·t` only has to reach the gap, which takes at most one turn `1/N`.
- 180 arrangements (`b ∈ {61..69}`, `d ∈ {12..20}`, `f ∈ {4,5}`, `N ∈ {10⁴,10⁵,10⁶}`): `|t* − t_pred|·N ≤ 0.617`
  in every one.
  - 144 have the event at `t_C` and 3 inside the first cell (the within-cell delay of E33).
  - **33 are handoffs, and all 33 land at the START of the core's next cell** (`t_pred = 9/(8b)`: reading
    `b` reopening), because by then the train's shape has a quarter gap.
- **The one miss, and what it was.** Core `(32, 224)`: `224/32 = 7`, the core is **doubly pinned** at
  `t_C = 1/256` (`32·t_C = 1/8`, `224·t_C = 7/8`), so its clear set there is a single point that the
  cell-midpoint predictor never examined. At an isolated point the train is not decided by its shape but
  by where `N·t₀` falls:
  - `N ∈ [100000, 100016]` (`N/256` frac up to `0.6875`): event at `t_C`.
  - From `100017` on (frac `≥ 0.6914`): event at `t_pred = 9/1792`, the next positive cell.
  - The edge `0.6875 = 7/8 − 48/256` is the `sync_block` window `[1/8, 7/8 − Emax·t₀]` exactly.
  Refined `t_ref` = the first isolated core point in `[t_C, t_pred]` where the actual train is clear, else
  `t_pred`. Across all 195 arrangements `|t* − t_ref|·N ≤ 0.625`. `[EMPIRICAL — constructed families]`
- **Core blocked at every period point** (`(32,208)`, `(16,96)`, `(48,320)`, `(24,162)`, and `(32,224)`
  with step 16 or 6): the event is at `t_C` or at `t_pred` all the same. The train's quarter gap is found
  off the period points, so `lonely_at_period` is sufficient but not the route.

**What this settles, and what it does not.**
- **In these families the fast train does not move the isolation event around.** `t*` converges to
  `t_pred` as `N → ∞`, and `t_pred` is a function of the core and the train's differences alone. `N`
  contributes at most one turn. The only `N`-dependence is at doubly pinned isolated points, and there it
  can only bring the event earlier than `t_pred`, never later.
- **This reduces the handoff to a problem without `N`.** Is there, and how early, a `t` with the core
  clear and the offsets `E·t` leaving a gap `≥ 1/4`, that is, a free phase `y` at distance `≥ 1/8` from
  every `e·t`? That is the core plus the train's differences with one extra free phase, a lower-order
  object.
- **`[OPEN]`:** a bound on `t_pred` in terms of the core and `E`.
  - Available: the train's quarter-gap set contains every window `|t − k/g| ≤ 3/(4·Emax)`.
  - Not available: that some positive core cell meets one of those windows. The lemma of item 1 covers
    exactly the windows in which the core is clear.

---

## E35 — 2026-09-25 — every arrangement only relocates the isolation event: what the cascade shows

Author's framing (restated after reading every prompt): any arrangement is just deviations from the AP; the
φ(n) law gives the AP's global isolation; the cascade shows where each runner's isolation moves to. Task: use
the cascade to show any arrangement only relocates the event. Scripts `experiments/nN/redo/relocation_v1/v2`
(LonelyRunner repo), exact, arrangements of 8 positive distinct speeds, every runner, signed differences.

**The runs.** Arrangements built as AP gap 840 plus deviations up to `ρ` gaps, `ρ` = 1/100 … 16 (for `ρ ≥ 1` runners lap past
other slots), and 400 random arrangements in `[1, 10⁶]` (each is its fitted AP plus deviations). 32,000 runners.
- **Every runner's event is the AP's first spine point `u = 1/8` at some scale `D*`**, with its flank exactly at 1/8 or 7/8
  (Thm 6.2(d)) and every other runner in `[1/8, 7/8]`: 32,000 of 32,000, no cap reached.
- **The relocation is a change of scale, not a loss.** `t*/t_ref` (`t_ref` the fitted AP's instant, `W/7`) ranges from about 0.2
  to about 1,800; the number of moves stays at most 16 and averages about 1 at **every** deviation size.
- **Near the AP the relocated event is the AP's event, slot for slot.** At `ρ = 1/100`, all 3,200 runners have the seven others
  on the seven distinct slots 1..7 (nearest eighth) at `t*`. At `ρ = 1/8`: 1,669 of 3,200. At `ρ ≥ 1`: about 20 of 3,200. So
  far from the AP the others share slots at the event; what the event needs is only that **none sits in the subject's slot**.

**What a move is, in AP terms.** Just before every one of 13,086 moves, the setter sat **in the subject's own slot** at that
scale: eighths in `[0, 1)` (6,468) or just under it in `(7, 8)` (6,618), i.e. the runner has lapped onto the subject, the
residue-sharing of §4.5. The move re-reads the arrangement at the scale where that runner sits exactly one slot ahead
(`8N + 1` eighths); every other reading dilates by the same factor. So **the cascade cures slot-sharers one at a time, and
each cure relocates the event to a finer scale.** The setter is rarely the subject's nearest speed (91–100% "other"): it is
a far runner that lapped round, and after the move it is the subject's circle neighbour at one eighth.

**A trace** (`relocation_v2.out`): `(8308, 9358, 9593, 11119, 11359, 11836, 12776, 14328)`, runner 9593. Scales
235 → 196.2 → 169.6 → 142.8 → 131.9 → 127.3. The first cure (1766 to 9 eighths) put three others into the subject's slot;
each later cure removed one and created at most one; at `D* = 127.3` no runner shares the slot.

**What this establishes, and what it does not.** `[EMPIRICAL — 32,000 runners]` every arrangement tested only relocates
the event, and the relocation is the cascade curing slot-sharers. **Not established:** that the curing always ends. A cure
dilates every reading and can put new runners into the subject's slot (the trace's first move made three). The move count is
not the handle: resonant trains (E33) make it grow with `N` while the relocated time stays bounded, and §0 excludes move
counts. The object for a proof is the **set of scales** the cure can visit.

**E35 correction (same day, author).** "That the curing always ends" and "why can't the stretching keep feeding runners
in forever" are termination questions, which treat the cascade as an algorithm. It is not one and does not need to
terminate: it identifies the event. The owed statement is static: **every arrangement has, for every runner, a scale
at which no other runner sits in the subject's slot** (Thm 6.15's candidate scale `e/(8k+1)`, no time, no iteration).
The cascade reads that scale off; nothing is asked of its path.

---

## E36 — 2026-09-25 — review of MANUSCRIPT_v21 and PAPER_v9_1; one correction under the owner's positive-speed rule

**Review written:** `docs/n8/REVIEW_MANUSCRIPT_v21_PAPER_v9_1_v1.md`. The grade-affecting items are M1–M4 there. One check
is on disk: `experiments/n8/thm11_3_proof_step_check_v1.{py,out}`, exact `Fraction`.

**Owner rules restated today:**
- Exact arithmetic only; no floating point.
- The Boundary Set Method, not brute force.
- No runner is ever stationary, and every speed is positive.

**Correction to the review's M2 under these rules.** M2 realised a disparity set `ds` with the subject at `0` and runners at
`−d`. That uses a stationary runner and negative speeds. The statement is unchanged, but the arrangement must be restated:
- Put the subject at `c = max ds + 1`.
- Put a runner at `c + d` for each `d ∈ ds`, and at `c − d` for `7 − card ds` of them.
- Every speed is then positive and distinct, and the disparities from the subject are exactly `ds`.

`lonelyAt_add_const` (`Cascade/Arrangement.lean`) is the shift that makes the two placements equivalent. So the equivalence
`ExistenceAt8 ↔ LonelyRunnerAt8`, the equivalence M2 states, stands under the positive-speed rule. `[PROVED — in the text; not
yet in Lean]`

---

## E37 — 2026-09-25 — what the conjecture asks, statement by statement; owner opens covering

**Owner rulings recorded here:**
- Pre-registration applies to ECC work only.
- Covering is now admissible as a proof form. The ban was needed early, to clear away things that did not apply; the
  framework is now developed.
- Density is of no use: the framework works natively on all positive reals.
- Pigeonhole is a tool, not an object.

**The statements, against the conjecture.** The source is the Lean definitions: `Spec/Target.lean`, `Spec/Doors.lean`, and
`experiments/n8/RCapObligation_v1.lean`.

| statement | relation to the conjecture | extra requirement |
|---|---|---|
| `LonelyRunnerAt8`: every injective `v`, every `k`, `∃ t > 0` with every other runner at circle distance `≥ 1/8` | **is** the conjecture | none. Common start, distinct speeds, some `t > 0`, closed `1/8`, a separate `t` for each runner. It admits zero and negative speeds, which is equivalent by `lonelyAt_add_const` and asks nothing more |
| `DoorFlank`, `DoorArrives`, `DoorCapped`, `DoorFAM` | `↔` per subject (`doors_agree`) | none |
| `ExistenceAt8`, `_congruence`, `_flank`, and the `EightResidual` statement | `↔` (the card ≤ 3 case is proved; E36 gives realisation with positive speeds) | none |
| `CascadeCapped` | `↔`: the cap `U` is chosen per set (`∃ U` inside `∀ ds`) | none. Its docstring and v21 §6.7 l.1196 say "uniform", which overstates it |
| `RCapped B` | sufficient only | **yes**: one `B` for every arrangement |
| `DoorFirstLap` | sufficient only, and `[REFUTED]` | **yes**: a bound on when |
| "the first isolation" | a proved property of the cascade's output (Thm 6.2(b)) | only if someone requires the witness to be first, or bounds where it falls |
| §6A named/bounded-witness test, covering ban | rules about the form of a proof, not about what is proved | **yes, on the proof** |

**Witness or proxy.** The conjecture asks for `∃ t`. A proof of any statement proved equivalent to it proves the conjecture:
a certificate, a candidate scale, the cascade arriving, or the bad zones failing to cover `(0, ∞)`. So does a proof by
contradiction; Lean's `Classical.choice` is already among the three permitted axioms. Naming the witness is not required.

---

## E38 — 2026-09-25 — TrainCollapseN recovered and committed; two of my statements corrected

**Recovered.** The session that lost its context left `LRC/Spec/TrainCollapseN.lean` uncommitted. It builds cleanly and
has been committed as `6304771`. Spec gate PASS, 1,568 of 1,568 declarations axiom-clean
(`experiments/nN/spec_gate_train_collapse.out`).

**The result, `lonely_of_train_collapse` `[PROVED]`.**
- **Setup:** a core `C` and a fast train `{N + e : e ∈ E}`, with `|C| + |E| ≤ 7`. Every core reading and every offset
  is at most `m`. Take two offsets `i < j` with no offset at their midpoint; any adjacent pair qualifies.
- **Conclusion:** for every `N ≥ 56·m`, the runner is lonely at a named instant in `[2τ, 2τ + 1/N)`. The time `τ`
  depends on `C` and `E` only, not on `N`.
- **Checked before formalising:** `experiments/nN/redo/train_collapse_bound_v1.out`, 780 arrangements, 0 violations.

**Corrections.**
- **E36 said** M2 (`ExistenceAt8 ↔ LonelyRunnerAt8`) was "not yet in Lean". That was wrong. Commit `f32daf4` proves it
  (`lonelyRunnerAt8_iff_residual`), and `4ceb484` restates it with positive speeds `(1, 1 + r₁, …, 1 + r₇)`.
- **E37's answer to the owner** said a continuation from the AP fails on openness and on boundedness. Both
  objections are withdrawn, because both tested the wrong object:
  - *Openness.* It asked whether the AP's exact instant survives a perturbation. The claim is that the **event**
    relocates. Example: in `(1, …, 7, 8 + ε)`, runner `8 + ε` is lonely at `1/(8(1 + ε)) → 1/8` on a stretch of positive
    length. Also, "end runner" was a word about speed order; on the circle every runner is held from both sides
    (Thm 4.1).
  - *Boundedness.* It compared events **across** arrangements. Within one arrangement the event is bounded by its
    speeds: the period `1/gcd` for whole-number speeds, and `TrainCollapseN` for compact fast trains.

**The gap to the skeleton (`Order8SkeletonN`).**
1. The theorem needs separation ratio 56; the skeleton splits at `T = 9`. Separation at 56 implies separation at 9,
   so the skeleton can take `T = 56`.
2. The train's spread must be at most `N/56`. Spread-out blocks remain owed.
3. `ArrBoundedCovered8` remains owed.

---

## E39 — 2026-09-25 — arrangement types through the cascade; late events need the far runner in the subject's slot

**Scripts.** `experiments/nN/redo/arrangement_types_v1`, `late_event_law_v1`, `late_event_law_v2` (`.py` and `.out`). Exact
`Fraction` arithmetic; eight distinct positive speeds; every runner. Definitions:
- `u* = d_min·t*`, the event measured in laps of the nearest runner;
- **first cycle** means `u* ≤ 1`;
- `S = d_max/d_min`.

**1. Arrangement types** `[EMPIRICAL — 5,448 runners, 17 families]`. Every runner of every family resolves in the first
cycle. The families include: the AP deformed by `1/100` to 2 gaps; uniform on `[1,40]` and `[1,1000]`; separated core
with a compact train or a spread train; four close pairs; geometric; near-wrap; the seven `[1,40]` residual sets. The
only events past the first cycle are three of the three recorded hard cases (`u* = 2401/1872, 165/128, 219/184`), all
found by adversarial search. Spread and compact trains alike stay small (`max u* ≤ 1575/8144`). The hard compact
trains of E33 are constructed resonances and do not appear at random.

**2. The late events share one pattern** `[EMPIRICAL — 4 late events; knife-edge]`. In every late event the subject's
**far** runner (largest difference) reads `S` inside the subject's slot zone at the AP scale `d_min`, that is within 1
of 8:
- the three hard cases have `S = 366/49, 224/30, 15134/1974`, i.e. `7.47, 7.47, 7.67`;
- a hill-climb constrained to `S ≥ 8` found one more, `(109, 154, 234, 313, 273, 337, 390, 469)`, subject 109, with
  `S = 8` exactly (an exact sharer) and `u* = 2565/2248`.

Constrained to `S ≥ 8`, the climbs push `S` down to `8.02–8.09` (`u* ≤ 0.81`) and find nothing past the first cycle
there. On the circle the subject and its far runner are neighbours across the wrap. That is the owner's "two runners
essentially sharing a slot".

The pattern is necessary-looking but not sufficient: of 2,289 random runners with `S ∈ (7, 8)`, none is late. Lateness
also needs the other runners in a chain of slot-sharing pairs (for example `(27,70), (70,107), (107,137), (137,159),
(159,188)` in the 28-move case). Every one of those runners is critical: shifting any single speed by 2–5% of `d_min`
brings the event back inside the first cycle. The setters are spread across all seven runners. This is the relay of
E32, not a single pair.

**3. The factor 56 in `TrainCollapseN`** `[EMPIRICAL — 300 per ratio]`. 56 is the proof's margin: the gap between
`1/7` and `1/8` is `1/56`, which absorbs the core's drift `c/N` during the one fast turn. The collapse instant itself is
lonely far below 56: 300 of 300 at ratios 56, 40, 30, 20 and 12; 299 of 300 at 15; 297 of 300 at 9. So 56 is a
property of the argument. The construction mostly works at 9 but fails on a few sets there.

---

## E40 — 2026-09-25 — adversarial search at far-runner readings of 9 or more: nothing past the first cycle

**Script.** `experiments/nN/redo/late_event_S9_search_v1.{py,out}`: exact hill-climb with annealing and plateau moves.
Three arms of 60 restarts × 3,000 steps. The objective is the largest `u* = d_min·t*` over runners whose far reading
`S = d_max/d_min` lies in the arm's range. Starts are random at four speed ranges plus the recorded hard cases with the
far runner stretched.

| arm | restarts past the first cycle (`u* > 1`) | largest `u*` |
|---|---|---|
| control, `S ∈ [7, 9]` | **34 of 60** | `39/28` at `(1,31,70,96,126,158,176,225)`, subject 1, `S = 112/15` |
| `S ≥ 9` | **0 of 60** | `735/856` at `S = 9.067` |
| `S ∈ [9, 15]` | **0 of 60** | `305/352` at `S = 9.377` |

`[EMPIRICAL — adversarial search, the stated budgets]`

**Reading it.**
- The control fires, so the search can find late events. Its late events span `S = 7.003` to `S = 213/26 = 8.19`, on both
  sides of 8, all within 1 of 8.
- Theorem 11.2 (`R = 8u*` avoids `(7, 9)`) makes the first cycle exactly `u* ≤ 7/8`, or `R ∈ [1, 7]`. The `S ≥ 9` maxima
  sit just under `7/8` (`R ≤ 6.94`), so every event found there is in band 0.
- The hardest `S ≥ 9` instances sit at the edge of a slot zone: `S` just above 9, or `S = 15.12`, which is within 1 of 16.
- In every best instance some reading lies within 1 of a multiple of 8.
- `39/28` exceeds `u*` for every recorded hard case (`165/128`, `2401/1872`, `219/184`). In `R` it is `78/7 ≈ 11.14`, below
  the manuscript's `R ≈ 11.97`.

---

## E41 — 2026-09-25 — the late events read off the cascade: one relay template; extra laps on the far runner end it

**Owner (2026-09-25).** The cascade is not a black box and tells you where the isolation point is. Read it; do not
search.

**Script.** `experiments/nN/redo/late_event_trace_v1.{py,out}`. It covers 37 distinct late subjects: the 34 from E40's
control arm, the three recorded hard cases and E39's `S = 8` case. Exact arithmetic, in the coordinate `R = 8·d_min·t`
with readings `s = d/d_min`.

**1. The route into band 1** `[PROVED — from Thms 11.2 and 6.25; VERIFIED on 37 of 37]`. A move multiplies `R` by less
than `9/7`, so from `R ≤ 7` the next `R` is below 9. A late event therefore needs some step to land in `(7, 9)`. There
the nearest runner's own reading `R` is within 1 of 8, which puts `d_min` in the subject's slot. The next move is set by
`d_min` itself, to `R = 9`. Observed: 37 of 37 land in `(7, 9)`, and in 37 of 37 the next setter is `d_min`.

**2. The far runner starts it** `[VERIFIED — 37 of 37]`. The far runner is in the way at the bound `R = 1` in every case,
with its reading within 1 of 8. It then carries 2–6 of the band-0 moves.

**3. One template** `[EMPIRICAL — 37 cases]`. Every late case has nearly the same readings:
`1, ≈2.3–2.5, ≈3.2–3.3, ≈4.1–4.3, ≈5.1–5.4, ≈5.6–6.0, S ≈ 7.0–7.8`. That is the AP's `2, …, 7`, each pushed up by a
fraction of a slot. The band-0 climb follows almost the same setter word in every case (reading, lap):
`(S,1) (5.9,1) (5.2,1) (4.2,1) (S,2) (3.2,1) (5.9,2) (5.2,2) (2.4,1) (4.2,2) (5.9,3) (S,4) (5.2,3) (3.2,2) … (S,6) (2.4,2)`,
landing in `(7, 9)`. So a late event is the AP deformed in one specific way: the isolation point moves from `R = 1`
through a relay across every runner, into band 1.

**4. Extra laps on the far runner** `[VERIFIED — exact, 37 of 37]`. Replacing `d_max` by `d_max + 8·d_min` or
`d_max + 16·d_min` (reading `S + 8`, `S + 16`, still within 1 of a multiple of 8) makes every one of the 37 resolve at
`u* ≈ 0.13–0.30`, mostly in one move. The template needs the far runner **on its first lap** of the subject's slot.
Direct constructive evidence against late events near 16 or 24; not a proof.

**Route this suggests** `[proposed]`.
- The climb is a word of `(setter, lap)` pairs, and each step is `R' = (8M + 1)/s`. The word is valid exactly when each
  landing lies inside the next setter's zone, `|s'·R − 8M'| < 1`. That is a system of strict linear inequalities in the
  readings: an exact polytope for each word.
- So the late set is the union of the polytopes of the words that reach `(7, 9)`. That is the exact rational-LP method
  of the order-5 certificate (v21 §8.2), which gave `sup R = 31/9` there.
- What such a certificate would show: that every such word forces `S` within 1 of 8, and that past `R = 9` band 1 holds
  a clear point.

---

## E42 — 2026-09-25 — the climb certificate, first form; one reading of the owner's one-slot statement

**Word polytopes** (`experiments/nN/redo/late_word_certificate_v1.py`, `late_word_validate_v1.py`). Exact rational
simplex (order-5 solver), readings `1 ≤ s₂ ≤ … ≤ s₇`. The relaxed rows (each setter in the slot just before it sets)
are sound: **38 of 38 real late climbs lie strictly inside their own word's polytope** `[VERIFIED]`. They use 24
distinct words, of lengths 15–23.

**Not tractable in this form.** 5,332 words tested to length 6 and 17,483 to length 8, a factor of about 1.8 per step.
Length 23 would need of the order of 10⁸ LPs. The relaxation drops "latest opening", so it admits far more words than
the cascade takes.

**Next form** `[proposed]`. Label every runner at every step by its slot class: clear in gap `M`, meaning reading in
`[8M+1, 8M+7]`, or in the way at lap `M`, meaning reading in `(8M−1, 8M+1)`. With `R_i = (8M+1)/s_p`, every label is a
linear constraint in the readings. Given the labels, the cascade is exact: the in-the-way set is known, and the
latest-opening choice is linear. Each runner's label only advances, by at most a few classes per step. The branches are
then the cascade's own cells (v21 §12, walls `e(8M±1)/(8N+1)`), not a relaxation.

**Owner (2026-09-25):** *"All intervening runner at the time of isolation will be near their own isolation point
depending on the speeds and their variation from AP. The max they can go is 1/8 away on either side."*

One reading was tested exactly (`event_vertex_test_v1.{py,out}`) and **does not hold**:
- **The reading:** own point = `a_k·r mod 8`, with `r` the odd integer nearest `R*` and `a_k` the nearest integer to
  `s_k`; claim `|dev| ≤ 1` slot.
- **Result:** it holds for every runner in 777 of 1,200, 1,053 of 1,200 and 682 of 1,200 subjects in three families,
  and in **0 of 34** late events (worst deviation 4 slots).
- **Also found:** the median `|R* − nearest odd|` is 0. Most events sit exactly at an odd `R`, a unit instant of the
  AP at scale `d_min`.

This refutes that reading only, not the owner's statement. The intended meaning of "own isolation point" is to be asked.

---

## E43 — 2026-09-25 — the owner's vertex statement, tested as stated

**Owner:** *"Runner 1 isolation point is near 1/8, runner 2 is 2/8 etc etc runner 8 is 8/8"*, with at most 1/8 on either
side.

**Test** (`experiments/nN/redo/event_vertex_test_v2.{py,out}`, exact). At each subject's cascade event `t*`, is every
runner of speed rank `k` within `1/8` of `k/8`, up to one common rotation? Also with the vertices `k·a/8` for the AP's
other global instants (`a` = 3, 5, 7). "Band" is the smallest deviation that works, in slots.

| family (800 subjects each; late: 34) | class 1 | some odd `a` | band (some `a`), median / max |
|---|---|---|---|
| AP + deviation `1/100` gap | 708 | **800** | 0.02 / 0.09 |
| AP + deviation `1/8` gap | 668 | 707 | 0.32 / 3.11 |
| AP + deviation `1/2` gap | 288 | 300 | 1.42 / 3.02 |
| AP + deviation 2 gaps | 91 | 93 | 2.05 / 2.90 |
| uniform `[1,60]` | 99 | 101 | 2.00 / 3.00 |
| uniform `[1,1000]` | 86 | 86 | 2.07 / 2.96 |
| late events | 0 | **0** | 2.45 / 2.71 |

`[EMPIRICAL — exact per case]`

**Reading.** As stated, the property holds for small deformations of the AP. It holds for every subject at `1/100` of a
gap, and 707 of 800 already fail to hold it at `1/8` of a gap. It fails in general and at every late event. E35 found
the same far from the AP: the others share slots at the event, and what the event needs is only that no runner sits in
the subject's slot.

**Open question for the owner:** is "own point" meant at the event's own scale `D*`? That would relabel runners by
their slot at `D*`, not by speed rank.

---

## E44 — 2026-09-25 — each runner at its own event against its own vertex

**Owner:** each runner is near its vertex `k/8` at **its own** isolation, not at the others'.

**Frame.** At its own event a runner is at 0 relative to itself, so the statement is about absolute positions. Those
depend on a common speed shift, to which loneliness is blind. Frame used: the AP anchored at the slowest and fastest
speeds, gap `D = W/7`, `v₀ = v_min − D` (v21 §2.3).

**Test** (`experiments/nN/redo/own_vertex_test_v1.{py,out}`, exact): at runner `k`'s own cascade event `t*_k`, is
`(v_k − v₀)·t*_k` within `1/8` of `k/8`? A random position passes with probability `1/4`.

| family (800 runners each; late: 34) | within `1/8` of `k/8` | chance |
|---|---|---|
| AP + deviation `1/100` gap | 749 | 200 |
| AP + deviation `1/8` gap | 682 | 200 |
| AP + deviation `1/2` gap | 355 | 200 |
| AP + deviation 2 gaps | 252 | 200 |
| uniform `[1,60]`, `[1,1000]` | 275, 281 | 200 |
| late events (subject) | 5 | 8.5 |

`[EMPIRICAL — exact per case]`

**Design error, recorded.** The second column of the `.out` ("some odd `a`") is uninformative for odd `k`: the arcs
around `1/8, 3/8, 5/8, 7/8` cover the whole circle. Do not cite it.

**Reading.** Near the AP, each runner's own event sits at its own vertex. By half a gap of deviation the rate is 44%,
and in general it is close to chance. The runners' own events move with the deformation (median event 2.2–2.4 times
the AP instant in the uniform families). Together with E43, the vertex picture describes the AP and its small
deformations, not the general event.

---

## E45 — 2026-09-25 — the exact climb cells; readings up to 9

**Owner (2026-09-25).** *"Do we need to know where the other runners are as long as they are more than 1/8 away?"*
**No.** Loneliness asks only that each other runner be at least `1/8` from the subject. So each runner carries one
coarse label per cascade step:
- **clear in gap `M`**: reading in `[8M+1, 8M+7]`;
- **in the subject's slot at lap `M`**: reading in `(8M−1, 8M+1)`.

The lap number is kept only to follow the cascade.

**Method** (`experiments/nN/redo/climb_cells_v1.py`). With `R = (8M+1)/s_p` after each move, every label and the
latest-opening choice of setter are linear inequalities in the readings. The cascade is followed exactly, with nothing
relaxed: every real climb lies in the cell of its own label sequence, and every cell with margin `τ > 0` contains real
climbs.

**The LP.** Exact rational arithmetic (`gmpy2.mpq`), solved through the dual with a 7 × 7 basis and Bland's rule.
Cross-checked against the order-5 `Fraction` simplex: 600 of 600 feasible LPs agree on the exact optimum, and 400 random
LPs agree (38 optima, 362 infeasible) (`climb_cells_lpcheck_v1*.out`).

**A bug, fixed before any result was used.** The first run crashed. Closing the cell zeroed `τ` in `τ`'s own bound
rows, which are part of the starting basis, so the basis went singular. A guard now raises an error on any singular
basis.

**Readings in `[1, 9]`** (`climb_cells_B9.out`, `_S1_words.txt`, `_validate.out`) `[VERIFIED — exhaustive, exact]`:
- 659,744 LPs over 71,990 cells; 32,380 climbs end in band 0 (early events).
- **1,810 cells climb into `(7, 9)`**, using 579 words of lengths 15–25.
- **Completeness: 38 of 38 real late climbs are found**, each in its own word and `S` range.
- First setter: the far runner in 1,752 cells, `s₆` in 57, `s₅` in 1. In every case the far runner reads in `(7, 9]`,
  which inside this box is forced by the setup. This run is the control.

**Running:** readings up to 17 with `S ≥ 9`, covering the next slot zone at 16. This is the informative run.

---

## E46 — 2026-09-26 — climb cells v2: faster, restartable, regression-tested

**Organisation.** The owner asked for a better way to run long jobs than one blind run. `climb_cells_v2.py` makes these
changes:
- **Witness shortcut.** A child cell only adds rows; if the parent's witness point satisfies them, no LP is needed.
- **Warm start.** When an LP is needed, it starts from the parent's dual basis.
- **Queue.** 126 tasks after the first move, fed through a shared queue.
- **Checkpoints and progress.** An append-only `.jsonl` checkpoint and a `.progress` file.
- **Early positives.** Any climb into `(7, 9)` goes to `.TERMINALS.txt` the moment it is found.
- **caffeinate.** Always run under it. The first long v1 run (readings ≤ 17) was not, and the Mac slept through most
  of a night; it was stopped once v2 passed.

**Regression, readings ≤ 9** `[VERIFIED]`. Identical to v1: 71,990 cells, 32,380 early events, 1,810 terminal cells,
579 words, the same exact `S` ranges cell for cell, 38 of 38 real late climbs. 137 s against 1,968 s.

**The first regression failed.** It gave 47,396 cells against v1's 71,990. A per-task comparison
(`climb_cells_v2_pertask.out`) found the cause: the task id hashed only the word and the labels, so cells with
different histories collided and the bookkeeping kept one of each pair. The search and the LP were right; the totals
were wrong. The id now hashes every constraint row, and a guard stops the run on any collision.

**Lemma used from here** `[PROVED — in the text]`. Inside band 0 (`R ≤ 7`) every move lands on an opening
`(8M + 1)/s_j` with `M ≤ (7s_j + 1)/8`: finitely many values. `R` strictly increases, so the cascade either reaches a
fixed point (the event) or exits into `(7, 9)`. The same holds in every band. So **"no climb leaves band `b`" is
existence of the event** for every runner in the box. No cap is imported.

**Running:** stepped boxes `S ∈ [9, B]`, `B = 10 … 17` (`run_stepped_boxes.sh`, `stepped_boxes.log`).

---

## E47 — 2026-09-26 — CORRECTION to E40/E41: late events exist with far reading S > 9

**Found by the exact box `S ∈ [9, 10]`** (`climb_cells_v2_B10_S9.out`): 14 climbs into `(7, 9)`, with `S ∈ [9, 65/7]`.

**Confirmed** `[VERIFIED — exact; late_S9_witness_v1.{py,out}]`. For each of the 14 cells, a witness point strictly inside
(`τ > 0`) was realised as positive integer speeds and run through the plain cascade: **14 of 14 late**, `u* ≈ 1.13`,
`S ≈ 9.26`. Example: runner at speed 27897393 of `(27897393, 55794786, 110795338, 140358898, 168620898, 208085778,
228479138, 286202778)`, readings about `1, 2.97, 4.03, 5.04, 6.46, 7.19, 9.26`.

**What this corrects.**
- **E40 said** 0 of 120 adversarial restarts found a late event with `S ≥ 9`, and "suggested" the case split "far
  reading ≥ 9 ⇒ event in the first cycle". That split is **false**: the cells are thin and the search missed them.
- **E41's** "the far runner starts every late climb" holds on its 37 cases only. Here the second-farthest reading,
  about 7.19, is the one in the subject's slot at `R = 1`.
- **What survives:** a late event needs some reading in the subject's slot at the bound (someone must be in the way at
  `R = 1`); it need not be the far one.

**The exact box enumeration found what adversarial search did not.** This is the reason for the exact enumeration.

**Also.** `climb_cells_v3.py` adds `bands`. With `bands = 1` it is identical to v2 on readings ≤ 9 (regression PASS).
Next: every climb with readings ≤ 9 through band 1 (`bands = 2`), i.e. does any climb leave `[9, 15]` into `(15, 17)`?

---

## E48 — 2026-09-26 — stepped boxes for S ≥ 9 (band 0 only)

Source: `climb_cells_v2_B{10,11,12}_S9.out` `[VERIFIED — exhaustive exact enumeration of each box]`.

| box `S ∈` | cells | climbs into `(7, 9)` | largest `S` among them |
|---|---|---|---|
| `[9, 10]` | 69,385 | 14 | `65/7 ≈ 9.286` |
| `[9, 11]` | 112,548 | 27 | `2993/273 ≈ 10.963` |
| `[9, 12]` | 210,432 | 27 (the same) | `2993/273` |

- Late climbs with `S ≥ 9` occupy `S ∈ [9, 2993/273]`; the box `(2993/273, 12]` has none.
- The boxes followed band 0 only, which cannot prove existence where climbs leave it, so the run was stopped at
  `B = 13`.
- **Next:** each box followed through band 1 (`climb_cells_v3`, `bands = 2`), starting with readings ≤ 9 (running) and
  then `S ∈ [9, 12]`.

---

## E49 — 2026-09-26 — readings ≤ 9 through band 1: no climb leaves band 1

`climb_cells_v3.py 9 1 2` (`climb_cells_v3_B9_bands2.out`): readings `1 ≤ s₂ ≤ … ≤ s₇ ≤ 9`, every climb followed exactly
while `R ≤ 15`, with the nearest difference tracked from `R > 7`. **0 climbs exit into `(15, 17)`**. 181,068 cells;
78,568 events; 1,222,578 exact LPs solved and 868,363 skipped by the witness; 1,108 s.

**Consequence, with E46's lemma** `[VERIFIED — exhaustive exact enumeration; grade held until the positive control
reports]`: every subject with `d_max ≤ 9·d_min` has its isolation event at some `R ≤ 15`, i.e. `t ≤ 15/(8·d_min)`.
This extends R1 (`d_max ≤ 7·d_min`, Thm 4.8) to ratio 9. It is not in Lean: the LP certificates (Farkas vectors for
pruned cells, witness points for kept ones) are owed.

**Positive control running** (`band1_control_v1.py`). The real late climbs with readings ≤ 9 must each appear, with
their full cascade word, as a band-1 event cell. A zero exit count is only meaningful if the run produces the known
band-1 events.

---

## E50 — 2026-09-26 — every subject with d_max ≤ 12·d_min has its isolation event by R = 15

**Positive control PASS** (`band1_control_v1.out`). Of the real late climbs with readings ≤ 9, **38 of 38** appear, with
their full cascade word, among the band-1 event cells of the readings-≤-9 run (4,331 distinct band-1 event words). The
band-1 logic finds the known events, so E49's zero is a real zero.

**`S ∈ [9, 12]` through band 1** (`climb_cells_v3_B12_S9_bands2.out`): **0 exits into `(15, 17)`**. 210,561 cells
against 210,432 in band 0 alone, so the 27 late climbs of E48 add 129 cells and all reach their event in band 1. 241 s.

**Result** `[VERIFIED — exhaustive exact enumeration (gmpy2 mpq, dual simplex cross-checked against the order-5
solver), with positive control; not in Lean]`. This combines E49 (`S ≤ 9`), this run, and E46's lemma (in a band the
cascade reaches its event or leaves through the next gap).

> **For every subject whose largest difference is at most 12 times its smallest (`d_max ≤ 12·d_min`), the cascade
> reaches its isolation event at some `R ≤ 15`, i.e. `t ≤ 15/(8·d_min)`. So the subject is lonely.**

This extends R1 (ratio ≤ 7) to ratio ≤ 12 at order 8, for real speeds (readings are real; the cells are polytopes in
reading space).

**Owed for `[PROVED]`:** a Lean check of the enumeration's certificates, i.e. a Farkas vector for every pruned branch
and a witness for every kept cell, or an independent re-derivation.

**Remaining:** ratios above 12 (the stepped boxes continue; cost grows with `B`), and an argument for unbounded ratio
(the skeleton's separated side and the region with no separation).

---

## E51 — 2026-09-26 — unbounded S: the split-chain rule (R8 and the fast pair, generalised)

**The template of the two proved fast-block cases.** Lower orders make the slow core lonely at a stricter threshold,
which leaves a window of room; a window lemma puts the fast runners' clear instant inside it (`pair_window`: any window
of `3/4` of `a`'s lap).

**Nested windows** `[PROVED — in the text; the argument of pair_window iterated]`. A runner is blocked on
`(j − 1/8, j + 1/8)` of its own laps. So a window of `2ℓ + 1/4` laps holds a clear stretch of length `ℓ`, for `ℓ ≤ 3/4`.
Chaining from the fastest down, with readings `s₁ < … < s₇` and ratios `rᵢ = sᵢ₊₁/sᵢ`:
`W₇ = 1/4;  ℓᵢ = Wᵢ₊₁/rᵢ;  Wᵢ = 2ℓᵢ + 1/4;  every ℓᵢ ≤ 3/4`.

**Split-chain rule.** Split at `u`. The core `s₁..s_u` is lonely at `1/(u+1)` (native lower orders), so it stays clear
at `1/8` on a window of `ROOM_u = 2(1/(u+1) − 1/8)·r_u` laps of `s_{u+1}`. The top `s_{u+1}..s₇` runs the chain. The
rule holds iff the chain is valid and `W_{u+1} ≤ ROOM_u`. At `u = 6` this is R8 (`r₆ ≥ 7`). At `u = 5` it is the fast
pair. The plain chain (`u = 0`) uses the nearest runner's first band.

**Checked** (`ratio_chain_v1`, `split_chain_v1`; exact). Soundness: 0 violations. Wherever the plain chain applies, the
cascade's event is in band 0. Coverage among subjects with `S > 12`:

| family | covered |
|---|---|
| geometric-like, ratios 1.5–3 | 76% |
| many scales | 42% |
| uniform `[1,1000]` | 4% |
| uniform `[1,100000]` | 3% |

**What it misses: dense blocks.** A subject with one close neighbour and six readings of moderate spread has `S` large,
but no ratio chain. There `ROOM₁ = (3/4)·r₁` is large, and what is needed is a **window constant** for the 6-runner
block: every window of `K` laps of its slowest runner holds a clear instant.
- `K` is **not** uniform in laps of the block's slowest runner. Compact resonant trains (E33) delay the event by a fixed
  time independent of `N`, which is unboundedly many laps.
- Compact sub-blocks must therefore be collapsed (`SyncBlockN`, `TrainCollapseN`: the free phase, then the offsets at
  their own scale). Bounded-shape blocks need exact window constants, computable by the cell method with a free phase.

**The architecture this implies**, the E30 scale-tree induction with three step types:
1. Separated levels, by nested windows (this rule).
2. Compact levels, by collapse (`TrainCollapseN`).
3. Bounded-shape levels, by window constants from exact cell enumeration.

**Formalisable now:** the split-chain rule. It is `pair_window` iterated plus the native lower orders.

---

## E52 — 2026-09-26 — the split-chain rule in Lean; slabs to S = 15; the framing corrected

**Owner (2026-09-26).** *"Why are we talking coverage? Aren't we supposed to be proving that any arrangement moves the
isolation?"* The proof is the deformation argument, the continuity route of E18/E19:
- Global isolation holds at the AP.
- It survives small changes: interior margin, or the two-pinner lemma at isolated instants.
- What is owed is that the relocated isolation cannot escape to infinity: the owner's "bounded by the speeds of the
  arrangement".

The box certificates are exactly that bound on their region, `t ≤ 15/(8·d_min)`. The rules are regions where the bound
is available. "Coverage" figures were a diagnostic of which regions are not yet reached, and are not to be reported as
progress.

**Lean: `LRC/Spec/SplitChainN.lean`** (commit below; gate `experiments/nN/spec_gate_split_chain.out`, PASS 1,576 of
1,576) `[PROVED — axiom-clean]`:
- `stretch`: every window of `(2ℓ + 1/4)/a` holds a clear stretch of `ℓ/a`, for `ℓ ≤ 3/4`.
- `nested`: `needT (a :: L) = 2·needT L + 1/(4a)`, `Valid` = every `a·needT L ≤ 3/4`. Every window of `needT L` holds an
  instant clearing the whole list.
- `lonely_of_split`: a core lonely at `θ ≥ 1/8` (elements `≤ m`) plus a valid list with `needT F ≤ 2(θ − 1/8)/m` gives
  both clear at some `t > 0`.
- `lonely_eight_of_split`: the order-seven instance, with room `1/(28m)`.
- `r8_of_split`: R8 recovered.

**Gate hardened.** The Prop detector matched only `def … : Prop`, so a false `def Foo : A → Prop` would have passed
unregistered. It now also matches `… → Prop`. Only `Valid` was affected, registered ROUTE (a condition used only as a
hypothesis).

**Slabs through band 1** (`slabs_band1.log`) `[VERIFIED — exhaustive exact]`: `S ∈ [12, 13]`, `[13, 14]`, `[14, 15]`,
each with 0 exits from band 1. With E50: **every subject with `d_max ≤ 15·d_min` has its event by `R = 15`.** Caveat:
no positive control inside these slabs (no late climb with `S > 2993/273` is known). The `S ≤ 9` control covers the
same code path.

---

## E53 — 2026-09-26 — one runner deformed from the AP, traced exactly

**Script.** `experiments/nN/redo/deform_one_runner_v1.{py,out}`, exact `Fraction` arithmetic. The AP is `v_k = k·840`,
`k = 1..8`; one runner's speed moves by `δ ∈ (−G, G)`. For each step and each chosen subject the cascade gives:
- `t*`, shown as `t*·G`, so the AP's global instant is `1/8 = 0.125`;
- `d_min`;
- `S = d_max/d_min`;
- `R = 8·d_min·t*`;
- the runner pinning the event at exactly `1/8`.

`[VERIFIED — exact trace; 39 steps × 6 subject/deformation pairs]`

**1. While `S ≤ 7` the event sits at `R = 1`, `t* = 1/(8·d_min)`; `d_min` sets the scale.**
- Runner 8 moved outward (`δ ≥ 0`): its `d_min = G + δ` grows and the event slides continuously from `0.125` down to
  `0.0641` at `δ = 0.95G`. It is pinned throughout by runner 7, its nearest speed and circle neighbour, at exactly `1/8`.
- Runner 4 moved either way up to `|δ| = 0.45G`: the event slides from `0.125` to `0.2273` as `d_min` shrinks, pinned by
  runner 3 or runner 5.

**2. When `S` crosses 7 the event relocates within band 0 and is never lost.**
- Subject 1 with runner 8 moved outward: at `δ = 0.05G … 0.25G` the event jumps to `R = 3`, `t* = 3/8`, the AP's own
  `3/8` global instant, pinned by runners 4 and 6. Further out it moves to `R ≈ 2.3` (pinned by 8), then `R = 9/4`
  (pinned by 5), then `R ≈ 1.13–1.16` (pinned by 8).
- Runner 8 moved inward toward 7 (its `d_min` shrinks): `R` ranges over `1 … 475/99 ≈ 4.8`, pinned mostly by runner 1,
  its circle neighbour across the wrap.
- Every event in the trace has `R ≤ 475/99`, i.e. `t* < 5/(8·d_min)`: bounded by the speeds.

**3. Grids re-form the global event.** Where the deformed arrangement is a grid again (runner 8 at `7.5G`, `7.25G`,
`7.05G`; runner 4 at `3.25G`, `4.75G`, `3.05G`, `4.95G`), the event returns to `R = 1` with four pinners `[1, 3, 5, 7]`.
That is the φ(n) global instant of the new, finer grid.

**4. Runners whose `d_min` and `S` do not change keep the AP event.** Subject 4 while runner 8 moves, and subjects 1
and 8 while runner 4 moves, stay at `t* = 1/8`, pinned by their AP neighbours.

**Reading, in the owner's terms.** The deformation moves each runner's isolation point along the AP's own spine at
scale `d_min`, pinned by its circle neighbour. It is never lost. It jumps to another AP instant (`3/8`) or a
cascade-found instant in band 0 when `S` crosses 7, and snaps back to a global instant whenever the arrangement is a
grid again. Time scales as `1/d_min`: as a runner closes on a neighbour, `d_min → 0` and `t*` grows like `R/(8·d_min)`.

---

## E54 — 2026-09-26 — two runners deformed; the deformation step in Lean; the owner's taxonomy of shapes

**Two runners deformed together** (`deform_two_runners_v1.{py,out}`, exact): pairs `(8,1), (8,4), (2,7), (4,5)`, each
over a 13 × 13 grid of deformations in `(−0.9G, 0.9G)`, every subject: 5,408 subject-events.
- None lost; every event in band 0; largest `R = 17/4`.
- `S ≤ 7 ⇒ R = 1` held in every case, and every event is pinned by a circle neighbour. Both are forced by theorems
  (R1, Thm 6.2(d)), so they confirm the code and add nothing.
- The informative part is the band-0 containment, the same picture as one runner (E53).

**Lean: `LRC/Spec/DeformationN.lean`** (commit `4f5a39e`, gate PASS 1,580 of 1,580) `[PROVED — axiom-clean]`:
- `lonelyAt_of_close`, **openness**: lonely at `t` with margin `ε` stays lonely at `t` under any change of speeds of
  size `η` with `2η|t| ≤ ε`.
- `lonelyAt_of_limit`, **closedness**: a limit of arrangements lonely at instants in `[c, T]` is lonely at an instant
  in `[c, T]`.
- `lonely_along_path`, **the deformation theorem**: along a continuous path of speeds, isolation at the start that is
  locally stable and never leaves a fixed window of instants `[c, T]`, `c > 0`, is present at the end. Real induction.

Its two conditions are explicit hypotheses:
- **Local stability** holds wherever the lonely set has interior. Isolated instants need the two-pinner lemma.
- **The window** is the owner's "bounded by the speeds". The box certificates supply it where `d_max ≤ 15·d_min`
  (`t* ≤ 15/(8·d_min)`).

**Owner (2026-09-26), the shapes an ordered arrangement can take.** *"All speeds are in order. So basically you have
evenly spaced, you have clumped with outliers and evenly spaced with a clump somewhere. Giant spaced can still be seen
as even spaced. All clumped is also like even spaced."*

The shape is the vector of the seven consecutive **speed gaps** `g₁..g₇` up to scale: an arrangement-level object that
treats every runner at once. A subject's readings are sums of consecutive gaps.

**Evenly spaced** `[PROVED — in the text; the bound rests on E50/E52]`. If `g_max ≤ ρ·g_min`, then for every subject
`d_min ≥ g_min` and `d_max ≤ Σg ≤ 7·g_max`, so `S ≤ 7ρ`. That gives:
- `ρ ≤ 1` (all gaps equal, the AP): R1, in Lean;
- `ρ ≤ 15/7`: every runner by the box certificates (`[VERIFIED]`, not in Lean).

"Giant spaced" and "all clumped" are the same class: scale invariance, one gap.

**Clumped with outliers, or evenly spaced with a clump.** Some gaps are much smaller than others.
- A tight clump is a compact train: `TrainCollapseN`, `SyncBlockN` (free phase).
- Levels separated by large gaps: the split-chain rule (`SplitChainN`, `pair_window` iterated).
- **Owed:** a case split on the gap vector, with thresholds, that makes these classes jointly exhaustive, plus the
  bound at each class's boundary.

---

## E55 — 2026-09-26 — deformations through crowded slots; margin stability in Lean; one end is enough

**The close-pair rule (owner).** It is E35's slot-sharing cure: *"where two runners crowd a single slot, but it is really
sensitive because it's easy for it to slip into a different scale."*

**Map of deformations through crowded slots** (`deform_map_v1`, `v2`; exact). Three paths: the AP with runners 3, 4
crowded into one slot; the AP with 7, 8 crowded; and the late case `(1,31,…,225)` with its close pair pulled apart.
- **The first event jumps between nearby scales, often:** 7–12 jumps per crowded subject along a path, `R` moving
  within `1 … 1.37`. That is the owner's sensitivity. The first event is sometimes a single doubly pinned instant.
- **The lonely set never loses its interior.** At every step every subject has a lonely cell of positive length within
  `R ≤ 16`: 0 genuinely tight points on these paths.
- **So local stability holds by margin throughout.** In the interior of a lonely interval every reading is strictly
  above `1/8`. Genuine tightness, where no cell has interior, occurs at special whole-number configurations such as the
  exact AP's end runners; there the two-pinner lemma is needed.

**Lean** (commits `7129a6e`, and the one below) `[PROVED — axiom-clean; gate PASS 1,583 of 1,583]`:
- `DeformationN.eventually_lonely_of_margin`: lonely with margin at `p s` implies lonely at every nearby `p r`.
- `DeformationN.lonely_along_path_of_margin`: the deformation theorem with local stability supplied by margins.
- **`EndRunnerN.lonelyRunnerAt8_of_slowest`**: if the slowest runner of every arrangement of eight distinct positive
  whole-number speeds is lonely, the conjecture holds for every runner of every real arrangement. This is the owner's
  *"runner 1 is runner 8's neighbour … if you prove it at one end it is proved all over"*, made exact. Every subject's
  readings are the slowest runner's readings in `(1, 1 + s₁, …, 1 + s₇)`, and sets of at most six fall to order seven.
  Reversing the speeds swaps the ends.

**What this does to the case split.** Only the slowest runner remains. Its readings are the cumulative speed gaps:
`d_j = g₁ + … + g_j`, `d_min = g₁`, `d_max = W = Σg`. So the owner's shapes are directly the subject's cases:
- `g₁ ≥ W/7`, the subject's own gap at least the mean: R1 (`ratio_condition`; Thm 4.9, the wide-gap lemma for an end
  runner). **In Lean.**
- `W/15 ≤ g₁ < W/7`: the box certificates, event by `R = 15`. `[VERIFIED — computer]`; Lean owed (certificate export).
- `g₁ < W/15`: the subject's own first gap is small against the spread. Open. The late events all have a close pair
  elsewhere and `g₁` comparable to the mean; the slabs continue upward.

---

## E56 — 2026-09-26 — proof plan; WP1 in Lean; WP2 maps Case C

**Plan:** `docs/n8/PROOF_PLAN_ORDER8_v1.md`. The owner's direction: certificates are kept, since they do no harm, and
other methods are tried as well.

**WP1** (`LRC/Spec/SlowestSkeletonN.lean`, commit `d38da5e`, gate PASS 1,588 of 1,588) `[PROVED]`:
`lonelyRunnerAt8_of_cases T`. The conjecture at eight runners follows from two OWED statements on the slowest runner,
both registered on the gate:
- `CaseB8 T`: `7m < max ≤ T·m`;
- `CaseC8 T`: `max > T·m`.

Case A (`max ≤ 7m`) is discharged by R1. At `T = 22`, Case B is verified by the slab certificates (not Lean).

**WP2: Case C mapped by the cascade** (`case_c_map_v1`, `case_c_paths_v1`; exact) `[EMPIRICAL — 1,350 arrangements +
76 path steps]`.
- Setting: the subject is the slowest runner with `g₁ < W/22`.
- Shapes of the other gaps: even; clumped with outliers; even with a clump.
- Subject's gap: `g₁ ≈ W/30, W/100, W/1000`.

Results:
- **The event always lies in the nearest runner's first clear band**, `t ∈ [1/(8g₁), 7/(8g₁)]`: 1,350 of 1,350.
- **The other six clear together within at most 1.297 laps of `d₂`** after that band opens. The band gives
  `(3/4)·s₂` laps, and the largest share used was 12%.
- **Along the paths the event relocates often and stays very early:** 24 jumps in 76 steps, `u* ≤ 0.135`,
  `WAIT/ROOM ≤ 0.013`.

**What Case C therefore needs** (WP3): a window lemma for the six, i.e. every window of `K` laps of `d₂` holds an
instant clearing all six, with `K ≤ (3/4)·s₂`. The room is large unless runner 3 is also close to the subject; then the
core is the clump at the subject end (a larger `u`, lower order at `1/(u+1)`).
- **A plain count cannot give the window lemma:** six runners block `6 × 1/4 > 1` of a window.
- **What it needs** is the structure of the E31/E32 blocked stretches (κ ≤ 2.76 measured), with compact clumps
  collapsed (`TrainCollapseN`).

---

## E57 — 2026-09-26 — WP3: the scale law for a six-runner block's longest blocked stretch

**Owner:** *"there is an interesting relationship between scale."*

**Measured** (`block_blocked_v1`, `v2`; exact, Boundary Set Method; one period `1/gcd`; touching zones do not merge).
`L(F)` is the longest stretch of time during which some runner of a six-runner block `F` is in the subject's slot.
Neither single scale bounds it:
- **Compact trains** `N + E`: `L × min F` grows with `N` (4 → 34 → 334 laps), while `L × spread ≤ 1.95` and shrinks.
  The train blocks on the time scale of its internal spread, independent of `N` (E33's resonance law).
- **Spread blocks** (evenly spaced, random): `L × min F ≤ 1.9` laps, while `L × spread` grows.

**The law** `[EMPIRICAL — 11 families, exact per block]`. Let `σ₅(F)` be the smallest spread of any five of the six.
Then `L(F) × min(min F, σ₅(F)) ≤ 1.31` in every family, including one slow runner with a tight five-train, two slow
runners with a tight four-train, tight six-trains, evenly spaced blocks and random blocks.

**Why five.** A runner blocks an open quarter of the circle, and open quarters that only touch leave a clear point. So
four cannot hold the slot continuously; at least five are needed. A tight four with two slow runners stays short
(`L × min F ≤ 0.49`).

**Use in Case C.** Runner 2's first band gives a window of `3/(4g₁)` in time. Any window longer than `L(F)` holds an
instant clearing all six (startup stretch to be included in the check). So Case C closes wherever
`min(d₂, σ₅) ≥ (4C/3)·g₁`. The two exceptions:
- **Runner 3 also close to the subject:** a larger core at the subject's end, lower order at `1/(u+1)`.
- **A five-cluster tighter than about `1.75·g₁`:** its free phase collapses it (`SyncBlockN`, `TrainCollapseN`).

**Owed:**
1. Exact `C`: map the worst blocks by perturbation.
2. A proof of the block law, in two regimes: no tight five (`L ≤ C/min F`); a tight five (`L ≤ C/σ₅`).
3. The startup stretch included.
4. The Lean lemma.

---

## E58 — 2026-09-26 — WP3 item 1: the extremal block and its mechanism (resonance at t = 1/2)

**Search** (`block_extremal_v1`, `v2`, `v3`; exact; local ascent, one runner at a time with decreasing steps): 31
climbs from spread, random, compact, slow-plus-five and structured starts, and 20 climbs seeded at resonances `q = 2..6`.

**Correction to E57.** The measured bound `1.31` was a sampling artefact. The ascent reaches
**`Q = L·min(min F, σ₅) = 13/4`** at `F = [165, 166, 337, 494, 505, 772]` (shape about `1, 1, 2, 3, 3.06, 4.68`). Every
top block contains a close pair: 165/166, 355/357, 232/233, 195/197, 165/170.

**Mechanism** `[VERIFIED — exact, on the extremal block]`.
- The longest blocked stretch is `[647/1320, 673/1320]`, centred exactly at `t = 1/2`, and is a relay of 47 zones from
  all six runners.
- At `t = 1/2` the even readings (166, 494, 772) sit on the subject and the odd ones (165, 337, 505) sit opposite, at
  `1/2`.
- So near a small-denominator instant `p/q` the runners with `q | d` restart as at `t = 0`, and the rest start from
  fixed fractions. The long blocked stretch is a start-up stretch re-read at the scale `1/q`: the self-similarity of
  scale the owner pointed to.

**Robustness** `[EMPIRICAL]`:
- Scaled ×5 and ×20 and re-climbed with fine steps, `Q` stays exactly `13/4`.
- Pairs at progression positions peak at `650/201 ≈ 3.234`.
- Starts seeded at `q = 3..6` reach at most `4725/1996 ≈ 2.37`, still centred at `t = 1/2`.
- **Start-up stretch (item 3):** `Q₀ ≤ 0.196`, harmless.

**For Case C** (`L < 3/(4g₁)`). With the constant `13/4`, the six clear inside runner 2's first band when
`min(d₂, σ₅) ≥ (13/3)·g₁`. The two exceptions stand as before: a larger core at the subject's end, or collapse of a
tight five.

**Owed:**
- Item 2, the law proved. Its content is now concrete: blocked stretches are longest at resonant instants `p/q`, where
  a sub-block restarts, and are then bounded like a start-up stretch.
- Whether `13/4` is the supremum. It is found by local ascent from 51 starts, not proved.

---

## E59 — 2026-09-26 — WP3 item 2: the longest blocked stretch is a bridge over the slowest runner's clear bands

**Owner:** *"the cascade does this instantly and forcibly, so while it may be empirically found we should be able to
analytically prove it."* The cascade moves by force to the latest opening, so the stretch is fixed by the speeds and
should be derivable.

**Exact reading of the stretches** (`block_bridge_v1.{py,out}`) `[VERIFIED — exact, on the top blocks]`.
- **The `13/4` extremal** `[165,166,337,494,505,772]`: the stretch is
  `[647/1320, 673/1320] = [(81 − 1/8)/165, (84 + 1/8)/165]`. It opens where the slowest runner enters its lap-81 zone
  and closes where it leaves its lap-84 zone. The other five cover its **three** clear bands between, so
  `L·d₁ = 3 + 1/4` exactly.
- **Its centre** is `t = 1/2`, and every runner's phase relative to the slowest is exactly `0` or `1/2`: 166, 494 and
  772 are half a lap from 165, while 337 and 505 are level with it. A runner half a lap away puts its zone in the middle
  of the slowest runner's clear band.
- **Other top blocks** bridge 3, 1, 1, 1 and 0 of the slowest runner's clear bands. `[355, 357, 373, 524, 561, 784]`
  bridges 3 with `L·d₁ ≈ 4.18`; there `Q` is smaller because `σ₅ = 206 < min F`.

**Analytic target, restated.** A blocked stretch is: the slowest runner's zones, plus the other five covering every
clear band of the slowest runner that lies between them. So `L·d₁ < (number of bridged bands) + 5/4`. The block law
becomes a bound on how many consecutive clear bands of the slowest runner (each `3/4` of its lap) the other five can
cover without a gap.
- **Covering one band** needs a runner near half a lap from the slowest: a phase relation, i.e. a resonance.
- **Covering `k` consecutive bands** needs that relation to persist for `k` laps. Its drift rate is set by the speed
  differences (the owner's scale relation).
- **Next:** prove the per-band covering condition from the cascade's relay (each landing must lie in another runner's
  zone), and bound how many consecutive bands a fixed set of phase relations can cover.

---

## E60 — 2026-09-26 — the off-lattice rule, at every order (owner: check it seriously)

**Owner:** *"Hey don't throw away something so easily. If we prove n=8 most of this framework will generalise…
Please check this seriously, not just dismissed."* The session had set the argument aside as "too strong" before
checking it. Checked, it is correct and carries a precise condition.

**The rule** `[PROVED — Lean, axiom-clean]` (`LRC/Spec/OffLatticeN.lean`, commit below; gate PASS 1,590 of 1,590).
- **`lonely_of_off_lattice`**, every `n ≥ 4`. Split the readings into `x` and `D`. Let `h` divide every element of `D`
  but not `x`, and let `D` be lonely at `1/n` at `τ > 0`. Then the subject is lonely at `τ + k/h` for some `k`. Each
  `d ∈ D` moves by `d/h` whole laps per step, so `D` stays put; `x` advances by `frac(x/h) ∈ (0, 1)` of a lap, so
  `Flanks.exists_clear_step` clears it. No density, no count.
- **`lonely_eight_of_off_lattice`**: at order eight `D` (at most six) is supplied by native order seven.

**What it is.** It is the step `LRC(n−1) ⇒ LRC(n)` for every set with an off-lattice reading.
- It leaves exactly the sets in which every reading is a multiple of the gcd of the others; for a reduced set, every
  `n − 2` of the `n − 1` readings are coprime.
- It holds for real readings as well: the rest must be whole multiples of a common unit `u` with `x/u` not a whole
  number, rational or irrational.

**Checked** (`off_lattice_v1.{py,out}`, exact) `[VERIFIED]`:
- 164 of 164 applicable random reduced sets are lonely at the constructed instant.
- It closes 3 of the 7 `[1, 40]` residual sets of v21 §17D, e.g. `(4,5,6,14,16,34,38)`: `x = 5`, `h = 2`, `t = 1/28`.
- The class it leaves, every six coprime, is 2,811 of 3,000 random reduced sets. So it closes real cases but not the
  generic case.

**Recorded as an error of this session:** dismissing a derivation as "too strong" without checking its hypotheses.
This is the deflationary failure mode `CLAUDE.md` names.

---

## E61 — 2026-09-26 — the near-lattice rule (an invariant scale in place of the lattice): an uninformative test, and why

**Owner:** *"What if you replaced the lattice with an invariant scale like cascade does?"*

**The rule.** Choose a time step `Δ` with every `d ∈ D` within `δ` of a whole number of laps per step, and step
`t = τ + kΔ` from `D`'s order-seven instant, which has margin `μ ≥ 1/56`. `D` stays clear while `kδ ≤ μ`, and `x`
advances by `frac(xΔ)` of a lap per step. It fails only when `x` stays near-whole wherever `D` is, i.e. when `x` is tied
to `D` by small integer relations (AP- and grid-like). That suggests a structure-versus-generic split.

**Test** (`near_lattice_v1.{py,out}`, exact): 300 generic reduced sets (every six coprime) and the four residual sets
the exact rule left, with `Δ = a/b`, `b ≤ 40`, `k ≤ 6`.
- The "rule fires" on 300 of 300 and on 4 of 4, **but the drift condition `k·drift ≤ μ` holds in 0 cases**. The drift
  per step was `2/5` or `1/2`. The hits are density: `6 × 780` trial instants and one happened to be lonely (the §17E
  null). `[EMPIRICAL — uninformative as evidence for the mechanism]`

**Why** `[reasoned]`. For whole-number readings, a step with all six readings within `1/56` of whole numbers is one of:
1. an exact lattice `Δ = 1/h` (the proved off-lattice rule);
2. a tiny step `Δ ≲ 1/(56·d_max)`, where `x` moves enough only if it is about 14 times the others (scale separation:
   R8, split-chain);
3. a Diophantine near-coincidence of the fractions `n/d` across all six, which needs readings of order `56k` or more.

So, limited by order seven's margin `1/56`, the near-lattice drift argument adds nothing on small generic readings;
the margin is the binding constraint.

**Open:**
- the large-reading regime, where near-coincidences exist and scaling changes nothing (simultaneous approximation, a
  pigeonhole tool; needs a designed test);
- a larger margin taken from `D`'s own lonely cell instead of the `1/7` threshold.

---

## E62 — 2026-09-26 — a lattice at the smallest gap: static part and movers

**Owner:** *"what if the lattice is based on the smallest gap."* Step `t = τ + k/g`. Multiples of `g` stay exactly put
(the static part); the others move by `frac(x/g)` per step (the movers). One mover is the proved off-lattice rule.
`m` movers need a common clear step: the mover ladder of v21 §6.11. There `m ≤ 1` is proved; `m = 2` fails only for a
half-lap pair; `m ≥ 3` is open. What is new: the static part is supplied by a lower order at a free instant with room,
not at a fixed flank opening.

**Measured** (`gap_lattice_movers_v1.{py,out}`, exact; 2,000 generic reduced sets, every six coprime, random in
`[1, 400]`):
- **At `g = g₁`** (the nearest runner's gap): movers `{6: 1536, 5: 298, 4: 87, 3: 28, 2: 14, 0: 37}`. Generic readings
  are not multiples of the smallest gap. The `0` cases are `g₁ = 1`, a degenerate step.
- **At the best lattice** `g ∈ [2, max]`: movers `{2: 405, 3: 725, 4: 655, 5: 208, 6: 7}`, typically at `g = 2`
  (parity).
- **Residual sets:** three of the four have 2 movers at `g = 2` (their odd readings), and one has 4.

**Reading.** The smallest-gap lattice itself leaves about six movers. The useful lattice is usually parity, which is
the `t = 1/2` resonance of the extremal block (E58/E59) again. At `g = 2` every mover moves exactly half a lap per step,
so a step alternates between `τ` and `τ + 1/2`. Two movers then fail only if at every admissible `τ` one sits in
`(3/8, 5/8)` and the other in `(−1/8, 1/8)`. Here `τ` ranges over the whole lonely set of the even (static) part, not
one instant.

---

## E63 — 2026-09-26 — digression: the parity lattice with two odd movers

**The statement.** For sets with exactly two odd readings `x₁`, `x₂` and five even `E`: some `τ` in the lonely set of
`E` has both odd readings clear at `τ` or both at `τ + 1/2`. **This is equivalent to the subject being lonely**, since
the lonely instant itself serves as `τ`. Only its structure can help.

**The structure** `[PROVED — in the text]`.
- **Failure at `τ`** means one odd reading is within `1/8` of half a lap and the other within `1/8` of the subject.
  Equivalently, `‖2xᵢτ‖ < 1/4` for both, with `(x₁ − x₂)τ` away from whole numbers.
- **A mover** stays in its failure arc for at most `1/(4x)`.
- **Order six gives `E` a room** of `1/(12·max E)` around its instant. So **if both odd readings exceed
  `3·max E`, failure cannot last across the room, and the subject is lonely.** This is a separation case.

**Tested** (`parity_two_movers_v1.{py,out}`, exact): the order-six instant of the evens, 9 points across its room, and
the half-shift.
- Generic reduced sets with two odd readings: **946 of 1,000**. Of these, the separation case applies to 1.
- Residual sets: 2 of 3 (`(4,5,6,8,14,32,37)` at `t = 31/768`, `(4,5,6,14,17,32,38)` at `t = 37/912`). Not
  `(2,12,15,21,32,34,38)`.
- **Not evidence of a mechanism.** The failure pattern has probability about `1/8` per instant for random positions,
  so a 95% success rate over 9 correlated instants is what the geometry predicts. The guarantee holds only in the
  separation case.

**Reading.** At comparable speeds the parity route needs a room longer than the odd movers' failure passages. Order
six's room is too short unless the odd readings are fast; this is the same margin bottleneck as E61. What the
digression does confirm: failures at comparable speeds sit at the `t = 1/2` resonance, the mechanism of the extremal
blocked stretch (E58/E59). So the window law and these residual cases are one problem.

---

## E64 — 2026-09-26 — WP3 steps 1–2: the relay across clear bands, checked exactly

**Step 1** `[PROVED — from the cascade's definition]`. Covering a clear band of the slowest runner `d₁` is a cascade
relay from `d₁`'s opening to `d₁`'s next zone. Each link has the form `|d′(8M + 1) − 8M′·d| < d`, the climb-cell
relation.

**Step 2, per link** `[VERIFIED — exact, two links on the extremal block]`. Over one lap of `d₁` the landing of setter
`j` advances `n_j` of its laps, and the next runner `j′` drifts, to first order, by `ε_{j′} − (n_{j′}/n_j)·ε_j`. Here
`ε = d/d₁ − n` is the deviation from the progression at the block's smallest gap.
- 165 → 494: predicted `−0.0061`, observed `0.0083 → 0.0023`.
- 505 → 166: predicted `−0.0141`, observed `0.0156 → 0.0017`.

(`block_drift_v1.{py,out}`)

**Step 2 as first stated ("the same word repeats") is false** `[VERIFIED]`. The words differ band to band. When a link's
slack runs out, a runner far from the progression takes over: in the extremal block 772 (`ε = −0.32`) replaces
165 → 494 at lap 83. In `[355, …, 784]`, 524 (`ε = +0.48`), 561 (`−0.42`) and 784 (`+0.21`) change position every
band.

**Consequence: the owner's smallest-gap lattice, at the block's own scale.**
- **Near-progression runners** (small `ε`) form a slowly drifting core. Their links last at most `slack/drift` bands,
  which is analytic.
- **Far runners** are movers. They extend a bridge only by landing in the right arcs band after band: the mover problem,
  band by band.

The window law's proof therefore has two parts: the drift bound for the core, and a bound on how many consecutive bands
the movers can patch.

---

## E65 — 2026-09-26 — WP3 part 1 in Lean: the core drift bound

**`LRC/Spec/CoreDriftN.lean`** (commit below; gate PASS 1,594 of 1,594) `[PROVED — axiom-clean]`:
- **`link_offset`**: a setter `d` landing at `t_b = (M + bn + 1/8)/d`, one landing per band, leaves the next runner `d′`
  offset from its lap line `M′ + bn′` by exactly `o + bη`, with `o = d′(M + 1/8)/d − M′` and `η = nd′/d − n′`. The
  offset is linear in the band.
- **`link_persistence`**: if the link holds at bands `0` and `b`, then `|b|·|η| < 1/4`. A link lasts fewer than
  `1/(4|η|)` bands either side.
- **`link_drift_eq`**: `η = (nε′ − n′ε)/(n + ε)` for `d = (n + ε)d₁`, `d′ = (n′ + ε′)d₁`. The drift is the deviation
  from the progression at the block's smallest gap.
- **`block_persists`**: a block whose readings are all within `ε` of whole multiples of `d₁`, clear at `τ` with margin
  `μ`, is clear at `τ + b/d₁` for every whole `b` with `|b|·ε ≤ μ`. A near-progression core has a clear instant in every
  band for `μ/ε` bands around any lonely instant with margin.

**Consistent with E64's exact data.** Link 165 → 494 has slack `0.0083` and drift `−0.0061` per band, so it holds for
2 bands and breaks at the third. Observed: laps 81 and 82 held, 83 broke.

**Still owed for the window law:**
- Part 2, the mover bound: how many consecutive bands far-from-progression runners can patch.
- Part 3, the assembly into the window lemma, then Case C.

---

## E66 — 2026-09-26 — the movers; Case C read off the cascade; slabs to 24

**Lean.** `CoreDriftN.mover_consecutive` (commit `c9497b9`, gate PASS 1,595 of 1,595) `[PROVED]`: a phase that moves by
more than a quarter lap per band never lies within `1/8` of a fixed lap line in two consecutive bands.

**Movers are resonant** (`mover_pattern_v1`, exact). In the long stretches of the top blocks, every far-from-progression
runner has a deviation near a small-denominator fraction:
- 772 `≈ −1/3`;
- 524 and 561 `≈ ±1/2`;
- 784 and 742 `≈ 1/4`;
- 361 and 365 `≈ −1/2`.

So they are near-progression at the finer gap `d₁/q`, `q ≤ 4`: long stretches need the whole block near a progression
at `d₁/Q`, `Q` small.

**Owner:** *"Just check any arrangement through cascade and then design your test about how the isolation occurs. The
cascade is deterministic and will give you the answer."*

**Case C read off the cascade from the bound** (`case_c_cascade_path_v1`, `case_c_repeat_setters_v1`; exact; 1,350
arrangements). The designed hypothesis was "every runner sets at most once", which gives
`WAIT ≤ Σ zone widths < 1.5` laps of `d₂`.
- It holds in **1,333 of 1,350**.
- In **16**, one runner sets twice; the waits are short (`≤ 0.69` laps of `d₂`).
- In **1**, one runner sets seven times (31 moves, wait `1.297`). The set has gaps `[7172, 32274, 65, 74, 63, 51]`: a
  tight five-group with `σ₅/d₂ = 0.035`, the train resonance.
- Runner 2 never sets.

**The Case C law, as the cascade shows it** `[EMPIRICAL — 1,350]`:
1. With no tight five-group, every runner sets at most twice, so `WAIT ≤ 3` laps of `d₂`. This fits inside runner 2's
   first band when `d₂ ≥ 4g₁`. **To prove:** no five runners can bridge two consecutive clear bands of a sixth, outside
   resonance.
2. With a tight five-group, the free-phase mechanism is needed. `TrainCollapseN`, as proved, needs the train 56 times
   faster than the core; here it is not.

**Slabs complete** (`slabs_band1.log`) `[VERIFIED — exhaustive exact]`: `S ∈ [12, 13] … [23, 24]` through band 1, 0 exits
in every slab. With E50, **every subject with `d_max ≤ 24·d_min` has its event by `R = 15`**. So Case B is verified at
`T = 24`.

---

## E67 — 2026-09-26 — Case C: the cascade's accounting is additive; how a runner comes to set twice

**Owner:** *"But cascade doesnt, so it must work differently"* (on the nested-window recursion doubling for comparable
speeds); *"use the cascade pertubate the speeds to find the mechanisim"*.

**Why the cascade does not double** `[PROVED — from the cascade's definition]`. `SplitChainN.needT` pays a worst-case
phase at every layer: `needT (a :: L) = 2·needT L + 1/(4a)`. The cascade pays only the moves that happen: each move ends
at the setter's zone exit, so it is at most that setter's zone width, and `WAIT < Σ_d n_d/(4d)`, where `n_d` counts the
settings of `d`. A runner that has just set stays clear for `3/(4d)`, so it sets again only if the other runners'
moves carry the cascade across that whole clear band. Fast runners' zones that fall inside a slower setter's zone are
jumped over and cost nothing. The object to bound is `n_d`, not a window.

**Candidate H2 refuted** (`relay_law_v1.{py,out}`, exact; 1,350 Case C runs) `[VERIFIED — refutation]`. H2 said a
runner sets again only if a runner at least 3 times slower sets between. Of 52 repeated settings, 18 have such a setter;
34 do not. Of the 34, 20 come from the one tight five-group arrangement (E66). The other 14 are near-progression sets
(the "even" family, ratios near `k : j`, e.g. `3G + g₁` against `G + g₁`, just under 3 : 1) and three clumped sets.

**Perturbation through the cascade** (`relay_perturb_v1.{py,out}`, exact, bisection to the boundary; 176 one-runner
moves over the 17 arrangements with a repeat) `[VERIFIED — exact, on these 17]`:
- **Every repeat has one shape:** `d` sets; a relay of other runners carries the cascade across `d`'s clear band;
  `d` sets again. In 306 of 340 loops the relay's setters are all distinct and none is `d`. The other 34 are in
  the tight five-group arrangement and its perturbations. Relay lengths: 1 (33), 2 (43), 3 (118), 4 (128), 5–9 (16),
  21–22 (2, tight five-group).
- **A repeat is destroyed in only two ways.** In 117 of 176 moves the relay breaks: at some exit instant no runner
  is in the way, so the event comes earlier and the chains agree up to there. In 34 the first setting of `d` is
  absorbed at the start: another runner is in the way at `1/(8g₁)` with a later exit. The remaining 25 are changes
  of setter where exits cross.
- So a second setting of `d` is a closed relay loop around `d`'s band. Each link of the loop is the climb-cell
  relation `|d′(8M + 1) − 8M′s| < s` (E64). A third setting needs a second loop around the next band.

**Next:** bound the loops. A third setting needs two consecutive loops. If the second loop reuses the first loop's
links, `CoreDriftN.link_persistence` with `b = 1` forces `|η| < 1/4` on every link, i.e. a near-rational relation
between consecutive setters. Movers can substitute (E64), so a second loop with different runners still has to be
bounded. Grade of "every runner sets at most twice outside the tight five-group": `[EMPIRICAL — 1,350]` (E66).

Note: `case_c_map_v1` prints its table on import (E-lesson 13); harmless here, recorded.

---

## E68 — 2026-09-26 — Case C: towards a third setting, then the wait itself; the E57 block law is refuted

**Owner:** "Ok" to perturbing the loop arrangements towards a third setting.

**A third setting is easy to reach** (`relay_third_v1.{py,out}`; exact; one-runner moves of the six, `g₁` fixed, order,
distinctness and `W > 24g₁` kept; the objective is the cascade's own settings count plus the covered fraction of the
repeater's next band) `[VERIFIED — exact, 68 climbs from the 17 loop arrangements]`. 47 of 68 climbs reach three
settings, one reaches four outside the tight five-group. Consecutive loops almost never share a word, except in the
tight five-group (7 and 11 settings, same word every band). Most repeaters are fast runners bridged by a slow one,
which costs little. **So "every runner sets at most twice" (E66) is false as a law; the settings count is not the
invariant.** What Case C needs bounded is the wait itself against the room `(3/4)(d₂/g₁)` laps of `d₂`.

**The wait, climbed directly** (`relay_wait_v1.{py,out}`; exact; 90 starts, every 15th Case C arrangement per family;
3,000 one-runner moves each) `[VERIFIED — exact per arrangement]`. The largest waits reached, in laps of `d₂`:
13.389 and 12.717 (all six readings within 6.3% of each other), 5.304, 4.712, 4.427, 4.199, 3.636, 3.565. **Every one
of the twelve largest has a clump**: two to six readings within a few per cent of each other (e.g. `1.0, 1.037, 1.067`;
`1.331 … 1.411`; `2.058, 2.061`). In the four largest the relay repeats one word 4, 4, 3 and 2 times; in others there is
no repeated word.

**The E57 block law is refuted** `[VERIFIED — exact counterexample]`. The 5.304 arrangement has readings
`d/d₂ ≈ [1.0, 1.037, 1.067, 2.064, 3.064, 4.038]` and `σ₅/d₂ = 2.064`, so `min(min F, σ₅) = d₂`, and the cascade from
`1/(8g₁)` is blocked for 5.304 laps of `d₂`. The blocked stretch containing it is at least that long, so
`L·min(min F, σ₅) ≥ 5.304 > 13/4`. The law was found by local ascent from 51 starts (E57, E58); it misses clumps
smaller than five. Here a tight **triple** sits at `d₂` inside a near-progression `1, 2, 3, 4`. E58's use of the law
("Case C closes wherever `min(d₂, σ₅) ≥ (13/3)·g₁`") falls with it.

**Not a finding:** every link ratio in these chains lies within about 0.06 of a fraction with denominator at most 6,
but that is roughly the chance level (any real lies within `1/12` of such a fraction). It is not evidence of resonance
and is not to be cited as such (E-lesson 9, density versus mechanism).

**What the wait follows, as far as these runs show** `[EMPIRICAL — 90 climbs]`: long waits need clumps. A clump of `k`
runners fans out on the time scale of its own spread, so it acts like one runner whose zone widens up to `k/4` of a lap.
The one-zone-per-setting accounting of E67 then undercounts; the train (E33, `TrainCollapseN`) is the five-and-six case
of this. **Next:** group the readings into clumps and test whether, clump by clump, the cascade sets each clump about
once, with a clump's cost being its fanned zone; that is the accounting a proof would use.

---

## E69 — 2026-09-26 — deformation paths from the progression: every pinch-off located exactly

**Owner:** the loneliness exists (the progression) and speed deformations move it; *"I don't think of it as a jump, more
displaced to somewhere else in the geometry"*; locating every pinch-off along deformation paths *"is a good place to
start"*. The wait bounds, block laws and clump accounting of E66–E68 are statements about blocked stretches from an
arbitrary start, and are set aside as proxies; the object is the displacement at a pinch-off.

**Set-up** (`pinchoff_v1.{py,out}`, `pinchoff_v1_summary.out`; exact, BSM). 85 paths: 45 Case C arrangements (every
30th of E56's 1,350) and 40 random arrangements of speeds in `[1, 300]`. Each path is `v(s) = (1 − s)v_AP + s·v`, with
`v_AP` the progression with the target's slowest speed and spread, so every speed stays positive, the order is kept,
and the slowest runner's readings are linear in `s`. The event is followed on a 400-point grid, with bisection to
`2⁻⁴⁴` wherever its pinning changes. A pinch-off (runner `a` leaves exactly as runner `c` enters) is linear in `s` and
solved exactly. The landing is computed **at `s*` itself**: from the pinched instant, the entering runner holds the
slot until its own exit, and the cascade from there gives the first lonely instant.

**First run defect, repaired before reading results.** The entering runner at the component's right end can change
inside a grid step; v1 solved only for the runner seen at the left of the bracket, giving 72 solutions outside their
bracket and one "no landing" at `s* = 1.446`, off the path, where speeds are negative. Cascading from the bound there
ends at once with no moves (the artefact is confirmed). Repaired: every runner's entry is a candidate, and only
solutions inside the bracket count.

**Results** `[VERIFIED — exact, on these 85 paths]`:
- **1,753 pinch-offs. Every one is displaced to a lonely component that already has positive length at `s*`**: the
  isolation moves to another place in the geometry, and the event just after `s*` agrees with the landing in all
  1,753.
- **Where:** 1,624 of 1,753 pinch the first spine instant `R = 1`. There the nearest runner leaves as a farther one
  enters. The entering runner is rank 6 (571), 5 (375), 4 (286), 3 (223), 2 (89) and 1 (80). The other 129 are
  elsewhere.
- **How far:** `R` grows by a factor of at most 2.54 (1,305 of 1,753 under 1.05). The largest landing is `R = 5.81`,
  and none lands in `(7, 9)`.
- **Handover:** in 555 the isolation lands exactly where the entering runner leaves its zone, with no relay. In 492
  it takes one move, in 397 two, and at most 12.
- **191 births:** the event is displaced *back*, to a component born at that moment (length 0 at detection), by a
  factor of at least 0.34.
- **73 transitions at `s = 0` itself:** at the progression every isolation instant is already pinched (at `R = 1` the
  first runner sits at `+1/8` and the last at `−1/8`), and the first step off it displaces the isolation to `R = 3` or
  `R = 5`.

**The first step off the progression** (`ap_first_step_v1.{py,out}`) `[PROVED — first order, below; VERIFIED 400 of 400
exact directions]`. Take readings `j·d + s·e_j`. At `t = a/(8d)`, `a ∈ {1, 3, 5, 7}`, every runner sits on an odd
multiple of `1/8`. Only two sit on the zone boundary: `j ≡ a` at `+1/8` and `j ≡ −a` at `−1/8` (mod 8, since
`a² ≡ 1`). To first order, instant `a` stays lonely iff some `y` has `e_j + j·y ≥ 0` for the first and
`e_{j′} + j′·y ≤ 0` for the second. So:
- `a = 1` opens iff `e₇ ≤ 7e₁`, and `a = 7` iff `e₇ ≥ 7e₁`;
- `a = 3` opens iff `3e₅ ≤ 5e₃`, and `a = 5` iff `3e₅ ≥ 5e₃`.

**The four isolation instants come in two complementary pairs, and every direction opens at least one of each
pair.** The progression's isolation is never destroyed by the first step; it is displaced within the pair. `a = 1`
survives exactly when the spread grows at most 7 times as fast as the smallest reading, which is R1 (Case A) to first
order. The event matched the predicted first open instant in 400 of 400 directions; the one tie (`e₇ = 7e₁`) is
`W = 7·d_min` exactly, lonely at `R = 1` by R1.

**Next:** (i) the pair law in Lean, beyond first order: every deformation of the progression small enough keeps one
instant of each pair lonely. (ii) The pinch-off displacement: at a pinch-off every runner except the two pinchers is
clear, with room. In 555 of 1,753 the entering runner's exit is already lonely; read off, from the geometry at `s*`,
what forces the landing in the others.

---

## E70 — 2026-09-26 — the pair law in Lean; at every pinch-off the geometry holds many other lonely places

**Owner:** "yes" to (1) the pair law in Lean beyond first order and (2) the displacement at a pinch-off.

**(1) `LRC/Spec/ProgressionPairN.lean`** (commit `428c341`; Spec gate PASS, 1,601 declarations, axiom-clean)
`[PROVED — axiom-clean]`. Readings `d j` with `|d j − j·c| ≤ c/20`, `j = 1 … 7`:
- **`instant_lonely`:** for `a ∈ {1, 3, 5, 7}` with `a·d (8 − a) ≤ (8 − a)·d a`, all seven are clear at
  `a²/(8·d a)`. Runner `a` is leaving its zone there, runner `8 − a` is at most at its entry, and the other five
  stay within `1/8` of their progression positions `2/8 … 6/8` (`dev_bound`: the deviation is at most `14/152`).
- **`pair_law`:** for `a ∈ {1, 3}` one of `a`, `8 − a` is lonely. The two conditions of a pair are complementary
  (`d 7 ≤ 7·d 1` or `7·d 1 ≤ d 7`; `3·d 5 ≤ 5·d 3` or `5·d 3 ≤ 3·d 5`).

Exact, not first order. The progression's isolation survives every deformation in the neighbourhood and is displaced
within its pair. Condition `a = 1` is R1.

**(2) The lonely places at a pinch-off** (`pinchoff_components_v1.{py,out}`; exact, BSM; the 1,753 pinch-offs of E69)
`[VERIFIED — exact, on these 85 paths]`:
- **At every pinch-off the geometry already holds at least 7 other lonely components with `R ≤ 15`** (20 or more in
  1,672 of 1,753).
- The isolation is displaced to the first of them after the pinched instant, in 1,753 of 1,753. This is by
  construction (the event is the first lonely instant); the content is the count.
- Some of these components are isolated points (length 0), e.g. `R = 9` exactly: the next places that can pinch.

**Reformulation.** Loneliness is lost along a path only if the last lonely component pinches off. The progression
starts with two that survive the first step (the pair law). Along the path, pinch-offs remove components one at a
time and births add them. **The relocation statement is therefore: the lonely components within reach never fall to
a single one that then pinches.** On these paths the count never fell below 8.

**Next:** track each component's lineage along the paths (birth, pinch-off, merger, split). Establish whether those
descended from the progression's pairs survive the whole path, and what keeps the count up.

---

## E71 — 2026-09-26 — lineages of the lonely stretches along the deformation paths

**Owner:** *"just remember that there is no arrangement that can move so it isn't isolated. The scale invariance and
the fact runners are always bound by their neighbours speed means that any arrangement just pushes the isolation."*

**Coordinates.** In `R = 8·d_min·t` only the ratios `ρ_j = d_j/d_min` matter: runner `j` holds the slot on
`R ∈ ((8k − 1)/ρ_j, (8k + 1)/ρ_j)`. A pinch-off or birth is the linear relation `ρ_b(8k + 1) = ρ_a(8m − 1)`, and a
pinch at `R = 1` is a ratio crossing `8m − 1`.

**Tracking** (`lineage_v1.{py,out}`; exact, BSM; 55 paths: the 40 random and the 15 Case C `W/30` paths of E69; grid
300). Each lonely stretch in `R ∈ [1, 15]` is labelled by its ends: the zone exit that opens it and the zone entry that
closes it, as (runner, lap). It continues across a grid step if one label persists (a hand-off), pinches off if neither
does, and unmatched new stretches are births. **Resolution check** (`lineage_v1_fine.out`, 12 paths at grid 3,000):
births 1,305 against 1,312 at grid 300, pinch-offs 1,065 against 1,072, ambiguous matches 0 against 4, and identical
lineage answers and minimum counts. Grid 300 is adequate for these counts. `[VERIFIED — exact, these 55 paths]`
- **Births 10,069, pinch-offs 8,353, hand-offs 11,906** (90 ambiguous matches, flagged, not guessed). Births exceed
  pinch-offs: away from the progression the lonely stretches multiply.
- **Just after the progression (`s = 1/300`) every path has exactly 4 stretches in `R ∈ [1, 15]`** (55 of 55): one
  from each pair `(1, 7)`, `(3, 5)`, `(9, 15)`, `(11, 13)`, as the pair law predicts (`lineage_count_v1.out`).
- **The progression is where isolation is scarcest:** on 54 of 55 paths the count never falls below 4. At the targets
  it ranges from 4 to 396.
- The one dip, to 3 for `s ∈ [217, 239]/300`, is a **window artefact**. That arrangement is in Case A (all ratios at
  most 3.65), lonely on the long stretch `R ∈ [1, 2.0]`; its stretches lie in `R < 4.3` and again beyond 17, so the
  window `[1, 15]` straddles the gap. A window fixed in `R` is not natural at every scale.
- **Lineage:** the stretch holding the target's isolation descends by hand-offs alone from one present just after the
  progression on **13 of 55** paths. On the other 42 every original stretch pinches off along the way, and the
  isolation is carried by stretches born on the path. The φ(n) isolation is pushed and displaced into new places, not
  carried as one continuous stretch.

**Next:** where births happen and which runners open them (the source of the count), read in the ratio coordinates.
Also, a window matched to the arrangement's own scale in place of `R ≤ 15`.

---

## E72 — 2026-09-26 — what "bound by their neighbours" does, read off the cascade

**Owner:** *"Test the cascade and find out"* (on what "runners are always bound by their neighbours' speed" means for
the isolation).

**(1) Births and pinch-offs by runner pair** (`birth_labels_v1.{py,out}`; the 55 paths of E71; grid 300; exact)
`[VERIFIED — exact, these paths]`. There are 9,362 births and 8,237 pinch-offs. By rank difference `|a − b|` of the
opening and closing runners, births number 2,855 / 2,250 / 2,079 / 1,238 / 719 / 136 for `|a − b| = 1 … 6`. Per
available pair (6, 5, 4, 3, 2, 1 pairs) that is 476 / 450 / 520 / 413 / 360 / 136, roughly uniform apart from the
subject's circle-neighbour pair `(0, 6)`. **Speed neighbours are not preferred in opening new places.** The fastest
runners take part most often, because they have the most zones in any stretch of `R`: births follow zone density.

**(2) Neighbour sweeps** (`neighbour_sweep_v1.{py,out}`; exact) `[VERIFIED — exact, 305,920 subject events]`. Twenty
random arrangements (speeds below 400). Each runner is swept through its whole range between its speed neighbours in
239 steps (the slowest over `(v₂/8, v₂)`, the fastest over `(v₇, v₇ + (v₇ − v₁))`), and **every** runner's cascade event
is found at every step.
- **Every event lies in the nearer neighbour's first clear band, `R ≤ 7`: 305,920 of 305,920.** The largest is
  `R = 4.02`. No cascade hit its cap.
- None lies in `(7, 9)`, and `R ≤ 7` whenever `S ≤ 7` (R1).

**Reading.** In the cascade, "bound by the neighbours" acts on **where** the isolation sits, not on which runners open
new places. Each runner's isolation is held inside its nearer neighbour's first clear band, well inside it on these
sweeps. The exceptions known are the knife-edge late events (E39–E48, `S ≤ 2993/273`), which sit in the second band,
`R ≤ 15`.

**The window the deformation theorem needs.** `lonely_along_path` asks for a fixed window of instants. In the
scale-free coordinate `R` the neighbour bound supplies one, `R ∈ [1, 15]`: the first two clear bands of the nearer
neighbour. A pinch-off can then always be displaced inside that window exactly when the bound holds at the pinch. So
the relocation proof and the neighbour bound are one statement:

> **Neighbour bound.** Every runner of every arrangement is lonely at some `t` with `8·d_min·t ≤ 15`, where `d_min`
> is its gap to its nearer speed neighbour.

Status: `[VERIFIED — exact certificates]` for `S ≤ 24` (Case A proved; Case B slabs, event by `R = 15`, E49–E52 and
E66). `[EMPIRICAL]` for `S > 24` (Case C: event in the first band, `R ≤ 7`, in 1,350 of 1,350, E56). In these sweeps,
`R ≤ 4.02`.

---

## E73 — 2026-09-26 — the neighbour bound in Case C: adversarial test, and what the proved lemmas close

**Owner:** *"prove the neighbour bound for Case C."*

**Tested before any proof attempt** (`casec_R_climb_v1.{py,out}`; exact; 179 climbs of `R` itself, with free moves of
the six other speeds and `W > 24g₁` kept; starts: every 10th E56 arrangement plus hand-built shapes — runner 3 also
close, trains of 3–6 near `d₂` or at the top, near-progressions with an outlier) `[VERIFIED — exact, 179 climbs]`.
**All 179 end in the first band; the largest is `R = 6.42`**, at readings
`(1, 1.75, 2.92, 4.06, 5.14, 6.86, 24.09)·g₁`: five within `7g₁`, one just past `24g₁`. The stronger form, `R ≤ 7`
(the nearer neighbour's first band), survives the push in Case C.

**What the proved nested windows already close in the first band** (`casec_split_cover_v1.{py,out}`; exact). Two
forms, both from `SplitChainN.nested`:
- **(A)** the core is the readings at most `7g₁`, clear on `[1/8, 7/(8ρ_max)]` in `u = g₁t`;
- **(B)** the core is `{g₁}`, clear on `[1/8, 7/8]`.

Together they close **232 of 1,365**: 127 of 450 clumped-with-outliers, 105 of 450 even-with-a-clump, **0 of 450
even**, and 0 of the 15 climbed shapes. The doubling in `needT` fails as soon as the fast group holds comparable
speeds (E67), and in the even family all six are comparable.

**Status of the neighbour bound in Case C: not proved.** The proved lemmas cover a minority (17% of this data) and
none of the comparable-speed fast groups. The empirical bound (`R ≤ 7`) is strong and survives an adversarial push.
The missing piece is the same object seen three times now (E56 window lemma, E67 accounting, E68 clumps): a fast group
of comparable speeds must find a common clear instant inside the core's clear set, without the nested-window doubling.

---

## E74 — 2026-09-26 — the circle geometry at the isolation; grids; the grid pair law in Lean

**Owner** (in order): *"Test the cascade and find out"*; *"Do you see that you are trying to explain what the cascade
does, so if any part fails your explanation is wrong because the cascade doesn't fail. Please keep going autonomously
until you have a proof"*; *"why does it seem like you are trying to prove all these proxies rather than how and why speed
changes deform the location of the isolation?"*; *"why do you need bands? … any arrangement of speeds simply moves the
isolation point. Deforms the circle geometry to relocate the isolation … USE cascade"*; *"other global isolations happen
other than just AP, so you can have 1…7, 16 but the runners need to be on a speed on a mod n location I call in early
work grid"*.

**Proxies set aside.** The window forms (`Q(F)`, `q_window_v1`, `q_climb_v1`: every blocked stretch of a six-set past
`T₀` ends within 7× its start; 4,276 of 4,276 random, then climbed to 5.83 of 7) are statements about stretches of time,
not about where the isolation is. They are recorded and not built on.

**The circle geometry, traced** (`circle_deform_v1`, `circle_mechanism_v1`; exact; paths from the progression, every
runner as subject) `[VERIFIED — exact, 25 arrangements × 8 subjects]`:
- At the progression each subject sees the other seven one per eighth (`1/8 … 7/8`).
- The runner pinning the isolation sits exactly on an edge of the subject's slot: `1/8` if it moves forward, `7/8` if
  it moves backward.
- **1,634 relocations:** 613 forward and 982 back. In 618, two runners sat at the same slot edge just before, one leaving
  and one arriving from the other direction: the pinch-offs. After such a pinch the arriving runner pins the relocated
  isolation from the far edge in 185; the cascade relays on in 432. The backward relocations are to a place that opens
  earlier; no pinch is involved.

**Grids (owner).** Global isolation holds at every grid, not only the progression: reduced speeds a complete residue
system mod 8. At `t = a/(8g)`, each subject sees the others at `a·n_j/8`, one on each nonzero eighth.

**The grid pair law** (`LRC/Spec/GridPairN.lean`, commit `a376e70`; Spec gate PASS, 1,606 declarations, axiom-clean)
`[PROVED — axiom-clean]`. `grid_pair` covers any subject at any instant `t` of any arrangement. Suppose runner `p` sits
exactly at `a·n_p/8 ≡ 1/8`, runner `q` within `1/56` of `a·n_q/8 ≡ 7/8`, and every other runner within `1/56` of
`a·n_j/8 ≡ 2 … 6`. Then the subject is lonely at `t` or at `((8 − a)/a)·t`. At the partner instant each position is the
reflection of `a·n_j/8 − ((8 − a)/a)·D_j` (`partner_position`), so `q` is on the clear side at one of the two. For
`a = 1` the partner is `7t`. This generalises `ProgressionPairN` from the progression to every grid pattern.

Checked first (`grid_pair_v1`): random grids, all subjects, perturbations up to `0.001` per speed keep both pairs, 2,400
of 2,400. At `0.01` the losses were the search window: with it widened ×4, 2,400 of 2,400. At `0.05`, 2,340 of 2,400.

**How far ordinary isolation sits from a grid pattern** (`event_pattern_v1`; exact; 400 random arrangements × 8
subjects) `[VERIFIED — exact]`. At the cascade isolation point the seven others fall on distinct nonzero nearest eighths
in only **26 of 3,200** events. Within `1/56` of their nearest eighths: 61; within `1/56` and a grid pattern: 1.
Ordinary isolation points are far from grid patterns: runners share eighths. The grid pair law is the local
displacement law around every grid; it does not by itself carry an arbitrary arrangement.

---

## E75 — 2026-09-26 — "a deformation only moves the isolation", made exact: closed, open, connected

**Multipliers at a pinch are not the mechanism** (`pinch_multiplier_v1.{py,out}`; exact; 1,753 pinches) `[VERIFIED —
exact]`. At a pinch `t*` the pinching pair sits on the edges `1/8`, `7/8`; at `λt*`, `λ ≡ 3, 5 (mod 8)`, it sits at
`3/8`, `5/8`. All seven are strictly clear at `3t*` or `5t*` in 824 of 1,753. The smallest working `λ` then decays
geometrically, and 10 pinches have none up to 200. That is the chance rate, not a law (E-lesson 9).

**The reduction** `[PROVED — in the text below; the pieces marked are in Lean]`. Work in ratio coordinates for the
slowest runner: `X = {1 = ρ₁ < ρ₂ < … < ρ₇}`, open and convex in `ℝ⁶` (every runner, every positive-speed arrangement,
by `EndRunnerN` and scale invariance). Fix a window `R = 8·d_min·t ∈ [1, B]`.
1. `P = {ρ ∈ X : lonely at some R ∈ [1, B]}` is **closed** in `X`: a limit of lonely instants in a compact window is
   lonely (`DeformationN.lonelyAt_of_limit`).
2. `P` is **open** at every `ρ` whose lonely set in the window has an interval of positive length: its interior points
   are strictly clear and stay so under small changes (`DeformationN.lonelyAt_of_close`). Call `ρ` **fragile** when
   its lonely set in the window is finite (isolated points only).
3. Every isolated lonely point lies on a **wall**: a hyperplane `ρ_b(8k + 1) = ρ_a(8m − 1)` (runner `a` leaving at
   `1/8` exactly as `b` enters at `7/8`; at `R = 1`, `ρ_b = 8m − 1`). The fragile set lies in the countable union of
   walls.
4. A polygonal path in general position avoids every pairwise intersection of walls (codimension 2). At a fragile
   point on it, every isolated lonely point lies on the same wall. Crossing that wall, each such point opens on one
   side and vanishes on the other. For a pair of the progression type (`t*`, `7t*`: the same two runners with roles
   reversed) the two open on opposite sides.
5. **Start** at a grid: every direction off it keeps a lonely instant (`GridPairN.grid_pair`,
   `ProgressionPairN.pair_law`, proved).

Hence `P = X` (lonely within `R ≤ B` for every arrangement, so LRC at eight runners) **if and only if** the following
lemma holds:

> **(L) Wall lemma.** At every fragile point on a single wall, the window's isolated lonely points do not all open on
> the same side.

The simplest failure of (L) is an arrangement whose window lonely set is a single degenerate point. (L) is the
precise content of "a speed change only moves the isolation": at every wall, the isolation survives on both sides.
If (L) fails at some wall, then arrangements just across it are not lonely within the window.

**Evidence** `[VERIFIED — exact, these paths]`: at each of the 1,753 pinch-offs of E69 and the 8,353 of E71, the window
held at least 7 other lonely components with positive length (E70). So no pinch met a fragile point, and (L) held
trivially. The known fragile points are the tight instances `{1…7}`, `{1,2,3,4,5,7,12}`, `{1,4,5,6,7,11,13}` (memory
`project_n8_tight_instances`: lonely only at `{1/8, 3/8, 5/8, 7/8}`). `grid_pair` needs one runner `≡ 1`, one `≡ 7` and
the rest `≡ 2…6 (mod 8)`, not distinct residues, and all three fit it for both pairs `(1,7)` and `(3,5)`.

**Next:** prove (L). First establish, with the cascade and BSM, which fragile points exist at all (every lonely point
degenerate), starting from the known tight instances and pushing arrangements towards fragility exactly.

---

## E75 correction — 2026-09-26 — the three tight arrangements, in positive speeds only

**Owner:** *"NEVER USE A STATIONARY RUNNER."* E75 cited the tight instances as reading sets taken from a memory recorded
in a rest frame, and the session then described them through a runner at rest. That is withdrawn. The arrangements,
every runner moving at a positive speed (any common shift gives the same geometry):

| arrangement (speeds) | slowest runner's readings | residues mod 8 | grid |
|---|---|---|---|
| `8, 9, 10, 11, 12, 13, 14, 15` | `1 … 7` | `0 … 7` | yes (the AP) |
| `8, 9, 10, 11, 12, 13, 15, 20` | `1, 2, 3, 4, 5, 7, 12` | `0,1,2,3,4,4,5,7` | no |
| `8, 9, 12, 13, 14, 15, 19, 21` | `1, 4, 5, 6, 7, 11, 13` | `0,1,3,4,5,5,6,7` | no |

**Cascade, every runner** (both sides of each subject) `[VERIFIED — exact]`. First arrangement: every runner isolated at
`R = 1` (`t = 1/8`), 0 moves. Second: seven runners at `R = 1` with 0 moves, and the runner at speed 12 at `R = 9/8` after
1 move. Third: the same, with the runner at speed 13 at `R = 9/8` after 1 move. All are in the first window. "Tight"
means only that the isolation has zero room (an isolated instant), not that it is hard to find.

---

## E76 — 2026-09-26 — the owner's rule at the cascade's own scale; the six grid residues traced

**Owner:** *"cascade already gives you the scale, use it. But informally I think it is, try and place most of the front
half in AP and grid can take care of the rest"*; then *"trace the six grid residues."*

**At the cascade's scale** `D* = 1/(8t*)` (`front_half_v1.{py,out}`; exact) `[VERIFIED — exact]`. A reading is in the
**AP part** when `r = d/D* ≤ 7` (first lap) and in the **grid part** when it wraps (`r mod 8 ∈ [1, 7]`).
- Random arrangements, every runner (4,000 events): the smallest half is entirely AP in 2,115. The number of AP
  readings spreads from 1 (705) to 7 (1,092).
- Case C sample (1,350): 1 AP reading in 796, 2 in 277; front half entirely AP in only 112.
- The 15 hardest Case C climbs: 1 AP reading in 14, 2 in 1.

**Where isolation is hardest, the AP part is the nearest runner alone and the grid carries the other six.**

**The six residues** (`grid_residue_trace_v1.{py,out}`; exact; the five hardest climbs and the five Case C samples with
the most moves). With `u = r₁ = g₁/D` running over the nearest runner's first lap `[1, 7]`, each wrapped reading's
residue `ρ_j·u mod 8` rotates at its own rate `ρ_j`. The blocked arc is `(7, 9)`, width 2 of the 8. At each move the
setter is the residue inside the arc with the latest exit; it jumps to exactly `1.00` and every other residue rotates
on.
- **Near-progression six** (readings `≈ 6, 11, 16, 21, 25, 30` in units of `g₁`, step `≈ 5`): the cascade ends at
  `u ≈ 1.63`, with all six residues bunched in `[1.0, 3.0]`, just past the arc. At that scale (`u ≈ 8/5`) each back
  reading is about `8j + 1.6`: **the back six are themselves an AP, placed at their own scale (`D ≈ step/8`) so that
  every one sits just past a multiple of 8.** This is AP and grid mixed: an AP for the nearest runner at scale `g₁`,
  and an AP for the back six at scale `step/8`, read on the grid.
- **A fast train** (five readings `1012.4 … 1018.9`): the members' residues form a fan with spacing `Δρ·u ≈ 1.6–1.9`,
  under the arc width 2, so one member is always in the arc. The setters cycle `4, 3, 2, 6, 5, 4, …` (the relay word
  repeats) until the spacing opens past 2, at `u ≈ 1.056`.
- **The hardest climbs:** the setters relay through all six with no repeated word. Each move moves one residue to
  `1.00`, and the isolation arrives when every residue is out of the arc at once (e.g. `u = 6.42`).

---

## E77 — 2026-09-26 — the flank sum criterion in Lean; how a grid achieves isolation

**Owner:** *"keep going, use the survey and prove the grid part … There is a proof there to be found. Cascade working
for all arrangements tested is not a fluke"*; *"Yes start on step 1. And after maybe we need to map how the grid achieves
isolation if there is a pattern and then we can look at how cascade is mapping those isolation points when the speeds
are moved off grid, just like we did with AP."*

**The survey** (a read-only sweep of `docs/n8`, `docs/nN`, `LRC/Cascade` and `LRC/Spec`) found that no proved result
seats more than three wrapped readings. At order 8 the flank sum criterion (`T4_FLANKS_v3` §3(d)) reaches three
movers, and the termination results (`ManyDifferences`, `FourDifferences`) stop at `2k < 8`.
`docs/nN/RESIDUE_DYNAMICS_v1.md` already has the residue picture of E76: the cascade is a map on the residue vector,
and non-termination is a blocked cycle covering a whole period.

**`LRC/Spec/FlankSumN.lean`** (commit `238f4e8`; Spec gate PASS, 1,613 declarations, axiom-clean) `[PROVED —
axiom-clean]`:
- **`arc_count`:** an open quarter-lap arc holds at most `c/4 + 1` of the points `i/c + β`, `i = 0 … c − 1`
  (`card_filter_shift` moves the count to a window where the arc does not wrap; `card_int_Ioo_le` counts the integers).
- **`mover_count`:** a mover of ratio `a/c` (`c`, `a` coprime) is in the way at most `N/4 + N/c` times among the
  openings `0 … N − 1`, for `c ∣ N` (`count_mul`: periodicity; `k ↦ a·k mod c` is injective on one period).
- **`flank_sum`:** at a flank `e`, suppose every runner outside the movers `M` has a whole ratio `A` with `8 ∤ A`, and
  `Σ_{d ∈ M} (1/4 + 1/c_d) < 1`. Then some opening of `e` is lonely.

This is the rational (whole-number arrangement) case of `T4_FLANKS_v3` §3(d), now in Lean. It seats up to three movers.
Four movers reach the sum `1` and are the open core.

**How a grid achieves isolation** (`grid_map_v1.{py,out}`; exact, BSM; 150 random grids × 8 runners, the complete lonely
set over one period `[0, 1/g)`) `[VERIFIED — exact]`:
- **Every runner of every grid has exactly four lonely components through the φ(8) instants `a/(8g)`**, one per
  instant (1,200 of 1,200); many are single points.
- **Every runner also has other lonely components:** from 4 to 46 or more per runner, and none of the 1,200 is lonely
  only at the φ(8) instants.
- The cascade's isolation is a φ(8) instant in only 177 of 1,200. Usually it finds an earlier, runner-own isolation:
  the bound `1/(8·d_min)` comes before `1/(8g)` when `d_min > g`.

The φ(8) instants are the grid's guaranteed global isolation; each runner holds more isolation of its own besides.
Their persistence off the grid is `GridPairN.grid_pair`.

**Next (owner):** move the speeds off the grid and map with the cascade how those isolation points are displaced, as E69
did from the progression.

---

## E78 — 2026-09-26 — off the grid: the nearest grid, and how the cascade carries each runner's isolation from it

(`offgrid_v1.{py,out}`; exact; 60 random targets, speeds in `[1, 200]`, every runner as subject; 300-step paths)
`[VERIFIED — exact, these targets]`
- **Every target has a grid within two speed units**: each speed moved by at most 1 for 36 targets and at most 2 for 24,
  order kept, residues mod 8 all different. The path from that grid to the target is short.
- **At the grid, each runner's cascade isolation is its own, not a φ(8) instant**, in 451 of 480. It sits at `R` between
  1 and 2.32, set by the runner's nearest neighbour. The φ(8) instant is the isolation in only 29.
- **Carried the whole way, with no relocation: 346 of 480.** The rest relocate a few times (forward pinches up to 8,
  backward births up to 7 on one path).
- `R` at the targets is at most 2.60.

So an arrangement is a small move from a grid, and its runners' isolation mostly rides through that move unchanged. The
isolation it carries is each runner's own isolation near its nearest neighbour's first band, which the grid also has,
not the grid's shared φ(8) instants. The relocations that do occur are the walls of E75, now few per path.

---

## E79 — 2026-09-26 — the relocations off the grid, traced; the grid 1…7, 16

**Relocations** (`offgrid_trace_v1.{py,out}`, `offgrid_bound_v1.{py,out}`; exact; the 60 targets of E78, every runner)
`[VERIFIED — exact]`. There are 327 relocations: 158 forward, 169 back.
- **Forward:** 122 of 158 start from the bound `R = 1`, the nearest neighbour's first edge. An arriving runner is found
  at the slot edge in 158 of 158. It carries the isolation straight across by itself (landing at its own exit) in only
  7; otherwise the relay runs 2–5 moves (at most 9). `R` grows by a factor of at most 2.06.
- **Back:** 147 of 169 return the isolation to `R = 1`. `R` falls by a factor of at least 0.48.
- **Pattern:** the isolation sits at `R = 1` whenever that instant is clear. A runner reaching the slot there pushes it
  forward through a short relay, and when that runner leaves, the isolation returns to `R = 1`.

(A first recount was run from inline code; on macOS multiprocessing could not start its workers, and the parent kept
respawning them for 24 minutes and filled a 64 MB error log. It was killed; the rerun from a script file took under a
minute.)

**The grid 1…7, 16** (`grid16_v1.{py,out}`; exact; every runner moving). Owner's suspicion: 16 fills the place of 8
but also coincides with other positions, delaying global isolation. The cascade: runners 1–7 are isolated at `t = 1/8`
with no moves, exactly as in the progression `1…8`. Runner 16 is isolated first at `t = 1/72` (its nearer neighbour 7
is 9 away) and is also clear at `t = 1/8` (it reads the others at `7/8 … 1/8`). **Global isolation is at `t = 1/8`,
not delayed.** Runner 16 does sit in other runners' slots at other instants: sampled at 799 instants, it is the only
runner in the way at 6–98 of them per runner. Even so each runner has more lonely stretches per lap with 16 than with
8 (runner 1: 10 against 4).

---

## E80 — 2026-09-26 — the flank sum criterion at the event: a corner, not the main road; the hard-case plan

**Check** (`flank_at_event_v1.{py,out}`; exact; 1,500 whole-number arrangements × 8 runners) `[VERIFIED — exact]`. At
the cascade's isolation the flank is the pinner's reading. The flank sum criterion (`FlankSumN`) holds there in only
347 of 12,000, and at any reading's flank in 360. Movers at the event's flank: 6 in 9,402, 5 in 1,552, 4 in 441. **The
typical isolation has all six other readings as movers**, clear at that particular opening, not by a count over
openings. So four to six movers is the ordinary case, and the hard cases must be defined by the cascade itself: first
openings blocked, a long relay, a late landing.

**Plan (owner: "find those hard cases, permutate them through cascade … a pattern, then a rule or law, from that a
mechanism and proof"):**
1. **Find:** exact climbs on relay length and `R`, plus the known hard sets (Case B late events, the Case C climbs, the
   longest off-grid relays).
2. **Perturb:** one-runner moves through the cascade; record each relay (who hands to whom, at which laps, where it
   lands).
3. **Pattern to rule:** what every long relay has in common.
4. **Mechanism to proof:** the rule as a lemma in the scale objects, in Lean.

---

## E81 — 2026-09-26 — hard cases found and perturbed (plan steps 1–2)

**Step 1, find** (`hard_cases_v1.{py,out}`; exact climbs on relay length, then `R`; 90 starts, speeds `≤ 600`, every
runner moving; the slowest runner) `[VERIFIED — exact]`. The longest relays reached are 23–27 moves, and **all of them
are late events**: `R` between 9.2 and 11.5, in the nearest neighbour's second band. `S` is just above 7, and the
readings are about `1, 2.4–2.5, 3.2–3.3, 4.0–4.3, 4.4–5.3, 5.5–5.9, 7.0–7.6` times `d_min`, the late template of
E41/E47. Every relay word starts `6, 5, 4, 3, 2` (fastest to slowest), and the nearest runner (rank 0) sets exactly
once, in `R ∈ (7, 9)`.
- **The mechanism at the start:** reading `ρ`'s first zone is `R ∈ (7/ρ, 9/ρ)`. Two neighbouring readings' first zones
  overlap exactly when their ratio is under `9/7`. In every hard case the three links between the four fastest readings
  are under `9/7`, so their first-lap zones form a staircase from the fastest runner down. Where a lower step is too big,
  a later-lap zone of a faster runner bridges it.

**Step 2, perturb** (`hard_perturb_v1.{py,out}`; exact; the top 15; every speed moved by `1/8 … 1` whole-speed unit,
one at a time; 1,920 moves) `[VERIFIED — exact]`:
- **Late survives in 1,451 of 1,920.** At this size (below 2% of `d_min`) the hard cells have width, and they close as
  the move grows: 112–115 survivors at `±1/8`, 70–74 at `±1`.
- **Every surviving late event passes through the nearest runner's zone** (rank 0 sets): 1,451 of 1,451. A late event
  is exactly a relay that blocks all of band 0 and hands through `(7, 9)` into band 1 (Thm 11.2).
- The moves that end the lateness drop the event back to band 0: to `R < 2` in 159, `R ∈ [4, 7)` in 282.

**Pattern for step 3:**
- **Observed:** the relay covers at most one whole band.
- **Candidate law:** if every instant of band 0 (`R ∈ [1, 7]`) is blocked, some instant of band 1 (`R ∈ [9, 15]`) is
  clear.
- **Evidence:** the exact certificates show it for `S ≤ 24` (no climb leaves band 1, E49–E52, E66). In Case C band 0 is
  never fully blocked (E56, E73).
- **Next:** find the reason in the configuration at `R = 9`, where runner 0 hands the relay into band 1.

---

## E82 — 2026-09-26 — step 3 probe: band 1 is band 0 mirrored and shifted; the landing sits over band 0's thinnest point

**The mirror** `[PROVED — one line]`. In `R = 8·d_min·t`, runner `j` sits at `ρ_j·R/8`, and at `16 − R` it sits at
`2ρ_j − ρ_j·R/8`: the reflection of its band-0 position, shifted by `frac(2ρ_j)`. The nearest runner (`ρ = 1`) and any
runner with `2ρ_j` whole are mirrored exactly. So band 1 (`R ∈ [9, 15]`) is band 0 (`[1, 7]`) reflected, with every
other runner displaced by its own shift.

**Hard cases, read through the mirror** (`band_mirror_v1.{py,out}`; exact; the top 8 of E81) `[VERIFIED — exact]`. At
the landing `R*` in band 1, the mirror instant `16 − R*` in band 0 is blocked, as a late event requires. It is blocked by
**one** runner in 6 of 8 cases and by two in 2, each sitting just inside its zone edge (`0.1–0.5` or `7.2–7.9` eighths).
Its shift `frac(2ρ_j)` carries it clear at `R*`, while the pinner sits exactly on an edge at `1.00`. Band 1 opens over
band 0's most thinly blocked point.

**Candidate law for step 4:** a full block of band 0 must be thin somewhere, at a point covered by a single runner near
its edge, and that runner's shift `frac(2ρ_j)` frees the mirror point in band 1 unless `2ρ_j` is whole. To test next:
- does band 1 always open at the mirror of a singly covered band-0 point?
- which full blocks of band 0 are thick everywhere (every point covered twice, or by mirrored runners), and do any exist?

---

## E83 — 2026-09-26 — the long relays in the cascade's own terms

**Owner:** *"Hard cases is a misnomer. Cascade deals with every single case instantly without a problem. So the hard
case seems to be about your band/flank or other addition. Use cascade to show you what happens."* The labels "hard",
"band" and "mirror" (E80–E82) are the session's framings, not the cascade's; E82's mirror probe is set aside.

**What the cascade does** (`cascade_own_terms_v1.{py,out}`; exact; the three longest relays of E81, subject the slowest
runner, time in units of `1/d_min`) `[VERIFIED — exact]`:
- **Every move is a hand-off.** The setter leaves the slot. During its jump (the rest of its time in the slot) the
  runners arriving at the slot enter, and the latest to leave sets the next move.
- **The relay is single file.** In the first trace, 19 of 27 jumps catch exactly one arriving runner, and that runner
  sets the next move. Several arrive together only during the long jumps: the nearest runner's jump (0.229 laps of
  `d_min`) catches 4.
- **It ends at the first jump during which nobody arrives.** In trace 1 the 27th jump (runner 3's, 0.056) catches no
  one, and the slot is empty from `t·d_min = 1.4329`. The next runner arrives 0.0039 later. Each runner sets 1–6 times.
- The cascade resolves each case in 26–27 exact steps.

---

## E84 — 2026-09-26 — every reading set up to 24: what the final hand-off looks like

**Owner:** *"The reason I say density is not the case is because our framework operates on a different basis … are we
bringing in density because it's logical or because that's what other frames have used?"* Answer recorded: imported,
not logical. Each arrangement's cascade is an exact finite computation, and counts over arrangements say nothing about
why any one stops. The E83–E84 tallies below only record which exact situation each arrangement is in; they are not
offered as rates.

**Exhaustive** (`exit_vs_arrival_v1.{py,out}`, `final_handoff_v1.{py,out}`; exact; all 346,104 sets of seven distinct
readings in `1 … 24` of the slowest runner, every runner moving) `[VERIFIED — exhaustive exact]`:
- Isolated at the bound with no move: 200,736. The longest relay has 19 moves. The latest isolation is at `R = 5.67`,
  readings `(3, 9, 11, 14, 15, 19, 24)`, so every set in this range is isolated within the nearest neighbour's first lap.
  The final setter is never the nearest runner.
- **At the final hand-off, runners are not used up.** In relays of 1, 2 and 3 moves every setter is a different runner.
  The runner that comes closest to arriving in time (the nearest miss) has not set a move in this relay in 121,543 of
  145,368 arrangements. The relay ends because the runners still available are not at the entry edge when the setter
  leaves, not because the available runners have run out.
- The nearest miss often arrives very soon after the exit: within a quarter of the setter's last stretch in 23,283.

So the mechanism of the stop is the positions of the runners that are still available at the setter's exit instant.
Those positions are set by their speed ratios to the setter at that exact instant.

---

## E85 — 2026-09-26 — reasoning in the framework's own objects: the ray through the grid, residual sets, the grid nudge

**Owner:** *"You don't need a full proof immediately, you just need to follow what the cascade is doing to deform the
isolation point and slowly piece together the actual proof … We are doing novel mathematics."* The owner also rejected
reducing the residual case to the E77 movers problem: *"it looks a bit like it but this is nuanced."*

**The single object.** For whole-number readings the isolation is at a rational instant `a/N`, and each reading sits at
`(a·d mod N)/N`. So isolation is a modulus `N` (the grid) and a multiplier `a` with every residue in `[N/8, 7N/8]`. The
cascade always takes `N = 8e` (`e` a reading, the AP scale) and `a = 8k + 1`: `clear_at_int_flank_iff_emod`. Seen
geometrically, the subject's view is the ray `t·d` (scale invariance), and isolation is the ray entering a box of the
mod-8 grid (each coordinate of `8t·d` in `[8m + 1, 8m + 7]`). Why every positive ray enters a box is the open
question, not a result.

**The ladder** (memory `project_n8_tight_instances`, proved). If some `q ∈ {2, …, 8}` divides no reading, the subject
is isolated at `t = 1/q`. A set is **residual** when every `q` from 2 to 8 divides some reading.

**The cascade on residual sets** (`residual_cascade_v1.{py,out}`: readings `≤ 40`, 3,996,993 sets;
`residual_scale_v1.{py,out}`: readings `≤ 32`, 715,822) `[VERIFIED — exhaustive exact]`. 61% (431,258 of 715,822) are
isolated at the bound. The rest move to another reading's scale with a small lap (`8k + 1 ∈ {9, …, 41}`). In 24,252 of
them the new scale is the multiple of 8 that the unit grid leaves blocked, with multiplier `e + 1`.

**The grid nudge** (`grid_nudge_v1.{py,out}`; exact, every residual set up to 32) `[VERIFIED — exhaustive exact]`. At
`t = 1/8` every reading not divisible by 8 is already clear; only the multiples of 8 are blocked. Nudging to
`t = (1/8)(1 ± 1/d₀)`, with `d₀` the largest multiple of 8, puts `d₀` exactly on the slot edge and moves every other `d`
by `±d/(8d₀)`.
- **The rule when `d₀` is the largest reading and the only multiple of 8** (elementary, owed as a lemma): the shifts
  are all under `1/8`, so residues 2–6 stay clear. The forward nudge works iff no reading is `≡ 7 (mod 8)`; the backward
  one iff none is `≡ 1`. With two or more multiples of 8, the smaller ones move by less than `1/8` and stay blocked.
- **Data:** a nudge isolates 230,085 of 715,822 residual sets. In every set with a reading `≡ 7` the forward nudge fails,
  as the rule says. The other mismatches with the simple rule come from readings larger than `d₀`, which move by more
  than `1/8`.
- **Where the nudge cannot work:** the sets holding readings at both edges, `≡ 1` and `≡ 7 (mod 8)`, the pinned pair of
  the grid. There the cascade moves to a different reading's scale. That is what to follow next.

---

## E86 — 2026-09-26 — the grid nudge in Lean; the pinned pair through the cascade; reverse patterns

**Owner:** *"Are you trying to force all runners to agree on a scale? That is not required in the framework. Merely any
speed is just AP/grid and a deviation that is forced by d_min"*; *"lets see if we can turn it into a lemma of worth"*;
*"Reverse patterns show up all the time. For the AP 4 global isolation, its two patterns and its inverts."*

**`LRC/Spec/GridNudgeN.lean`** (commit `477c551`; Spec gate PASS, 1,617 declarations, axiom-clean) `[PROVED — axiom-clean]`.
Take any instant `t₀` of any arrangement where every reading sits exactly on an eighth (`w j · t₀ = m j / 8`), and let
the largest reading `w p` be the only one on `0 (mod 8)`.
- **`grid_nudge_forward`:** if every other reading is on residues `1 … 6`, the subject is isolated at
  `t₀ + 1/(8·w p)`.
- **`grid_nudge_backward`:** if every other reading is on residues `2 … 7`, it is isolated at `t₀ − 1/(8·w p)`.
- **`nat_nudge_forward`:** the whole-number case at `t₀ = 1/8`.

The nudge is each reading's own grid position plus the deviation `w j/(8·w p)` forced by one blocked runner. No common
scale is imposed. The two nudges fail together exactly when both edges `1` and `7` are occupied: the pinned pair.

**The pinned pair through the cascade** (`pinned_pair_cascade_v1.{py,out}`; exact; the 180,875 residual sets up to 32
with one multiple of 8 and both edges occupied) `[VERIFIED — exhaustive exact]`. 97,724 are isolated at the bound
(the smallest reading's own AP scale, `k = 0`). The rest move to another reading's scale, mostly with `k = 1`: an edge
reading, an interior one or the multiple of 8, in comparable numbers. A recurring shape is the **largest** reading at
its second opening, `t = 9/(8e)`. Every other reading then sits in the first lap, at `9d/e` eighths (e.g.
`(3, 4, 5, 6, 7, 8, 25)`: `1.08 … 2.88`, with 25 on the edge).
- **Reverse R1** (elementary, owed as a lemma): if every other reading lies in `[e/9, 7e/9]`, the subject is isolated
  at `9/(8e)`. It is the counterpart of R1, which uses the smallest reading at `k = 0` with all others in
  `[d_min, 7·d_min]`.
- **The owner's framing:** reverse patterns recur throughout. The AP's four global isolation instants are two patterns
  (`a = 1`, `3`) and their inverts (`a = 7`, `5`).

---

## E87 — 2026-09-26 — the map onto the proved lemmas; the rest is a ladder instant plus a deviation forced by `d_min`

**The map** (`lemma_map_v1.{py,out}`; exact; every set of seven distinct whole-number readings in `1 … 32`, 3,365,856
sets, the slowest runner of eight moving runners) `[VERIFIED — exhaustive exact]`:

| proved lemma | settles | alone |
|---|---|---|
| ladder (some `q ∈ 2…8` divides no reading) | 2,650,034 | 1,111,648 |
| R1 (`max ≤ 7·min`) | 1,338,125 | 250,706 |
| grid nudge (`GridNudgeN`, at `a/8`) | 387,321 | 61,984 |
| flank sum (`FlankSumN`) | 320,804 | 668 |
| reverse R1 (others in `[e/9, 7e/9]`; one-line, owed in Lean) | 278,241 | 9,699 |
| off-lattice (`OffLatticeN`) | 132,943 | 15,629 |
| **none** | **231,062** | |

**The ladder nudge** (`ladder_nudge_v1.{py,out}`; exact) `[VERIFIED — exhaustive exact, readings ≤ 32]`. **All
231,062** unsettled sets are isolated at an instant within `1/(8·d_min)` of a ladder instant `t₀ = a/q` (`q ∈ 2…8`,
`a` coprime to `q`) where one reading sits exactly on a slot edge. By rung: `q = 2` (the half lap) 155,159; `q = 3`
70,686; `q = 4` 3,957; `q = 5` 1,249; `q = 7` 10; `q = 6` 1. The reading on the edge is the largest in only 2,232.

**So, for every reading set up to 32, the isolation is either a proved lemma's or a ladder (grid mod `q`) instant plus
a deviation of at most `1/(8·d_min)`.** This is the owner's *"any speed is just AP/grid and a deviation that is forced
by `d_min`"*, measured.

**Next:** why the half lap `t₀ = 1/2` serves so often. There every odd reading sits at `1/2`, with margin `3/8`, and
every even reading at `0`, blocked. The deviation must move the even readings out while the odd ones keep within
their margin.

---

## E88 — 2026-09-26 — the half lap is halving; rung R1 settles all but 10 of the unsettled sets

**Why the half lap** (`half_lap_v1.{py,out}`; exact; the 155,159 half-lap cases of E87) `[VERIFIED — exhaustive exact]`.
At `t = 1/2 + δ` every even reading sits where it sits at `δ`, so the full set is isolated there exactly when the evens
are isolated at `δ` (automatic, not a finding) and the odds, riding from `1/2`, stay clear. In 92,289 of 155,159 the
cascade's `δ` is `±1/(8·e_min)`: the evens' own bound, a lower-order isolation with fewer runners. The evens satisfy
R1 among themselves in most cases. This is halving. Memory records **Theorem P (halving)**, `[PROVED — in the text,
from LRC(4)–LRC(7)]`, as settling about a tenth of the residual case by shifting the evens along their own period and
counting. The cascade's version is different: it deviates from the rung by the evens' own bound.

**Rung R1** (`rung_r1_v1.{py,out}`; exact) `[VERIFIED — exhaustive exact, readings ≤ 32]`. For a ladder rung `a/q`
(`q ∈ 2…8`, `a` coprime to `q`), let `D_q` be the readings divisible by `q`, and test `t = a/q ± 1/(8·min D_q)`. Every
`d ∈ D_q` sits where it sits at `D_q`'s own bound. Every other reading rides from its nonzero multiple of `1/q`. **This
family isolates 231,052 of the 231,062 sets that no proved lemma settles**. By rung: `q = 2` 112,296; `q = 3` 79,824;
`q = 4` 24,791; `q = 5` 12,700; `q = 6` 711; `q = 7` 702; `q = 8` 28.

**The 10 it misses:** `(3,4,5,6,7,9,32)`, `(3,4,5,7,9,12,32)`, `(3,4,5,7,17,18,32)`, `(3,5,6,7,8,26,27)`,
`(3,5,6,7,8,27,30)`, `(3,5,7,8,12,26,27)`, `(3,5,7,8,12,27,30)`, `(3,5,7,8,18,26,29)`, `(3,5,7,8,18,29,30)`,
`(4,5,6,8,14,27,32)`.

**So every reading set up to 32 except those 10** is isolated at an instant from a finite explicit menu: the bound
`1/(8·d_min)` (R1), `1/q` (ladder), the nudges, `9/(8e)` (reverse R1), and `a/q ± 1/(8·min D_q)` (rung R1). That is
AP/grid plus a deviation forced by the multiples' own `d_min`. It is a map, not a proof. The next steps are the 10
exceptions through the cascade, and the condition under which rung R1 must succeed.

---

## E89 — 2026-09-26 — the ten exceptions through the cascade; rung R1 in Lean

**The ten** (`exceptions10_v1.{py,out}`; exact) `[VERIFIED — exact]`. The cascade isolates all of them immediately. Six
are isolated at the bound `1/(8·d_min)` with no moves (e.g. `(3,4,5,6,7,9,32)` at `1/24`). Three are at reading 26's
second opening `9/208` (`R = 1.04`, one move). One is at `9/216 = 1/24` (reading 27, `R = 1.33`). They were
exceptions only to E88's menu, which tested R1 (`max ≤ 7·min`), a sufficient condition for the bound, instead of the
bound instant itself. **The menu's missing entry is the grid at the bound:** at `1/(8·d_min)` each reading sits at
`(d mod 8·d_min)/(8·d_min)`, so isolation holds when every residue is in `[d_min, 7·d_min]` (32 mod 24 = 8 here). With
it, 4 remain, each isolated one move later at a second opening.
- **Owner's addition:** where two runners share an eighth and no scale separates them, isolation may take several
  cycles; the cascade still determines it. In these ten, runners share clear eighths at the bound (e.g. 3 and 4; 5, 6
  and 7), which is harmless. The case that matters is two runners sharing the subject's own slot. E35 records the
  cascade curing slot-sharers.

**`LRC/Spec/RungR1N.lean`** (commit `59a9cd6`; Spec gate PASS, 1,621 declarations, axiom-clean) `[PROVED — axiom-clean]`:
- **`rung_r1_forward` / `rung_r1_backward`** hold at any instant `t₀` of any arrangement. Readings on whole laps at
  `t₀` with `m ≤ w ≤ 7m` sit, after the deviation `±1/(8m)`, exactly where they sit at their own first instant. Every
  other reading at `K + ρ`, `ρ ∈ [1/8, 7/8]`, rides within its room (`ρ + w/(8m) ≤ 7/8`, or `ρ − w/(8m) ≥ 1/8`
  backward).
- **`half_lap_r1`:** whole-number readings with the evens in `[m, 7m]` for some `m > 0` and every odd reading at most
  `3m` are isolated at `1/2 + 1/(8m)`.
- **`rung_r1_nat`:** every rung `a/q`, `2 ≤ q ≤ 8`, with the explicit room condition `(a·u mod q)/q + u/(8m) ≤ 7/8` for
  the non-multiples.

This is the owner's *"AP/grid and a deviation forced by d_min"* as a theorem: the multiples of `q` become their own
smaller problem at their own bound, and the rest ride with margin `r/q − 1/8`.

---

## E90 — 2026-09-26 — every reading set up to 24 has an AP/grid view with room

**Owner:** asked what structurally guarantees that the cascade always lands on room: *"Because any arrangement can be
viewed in an AP/grid fashion."*

**The menu of views** (`menu_forcing_v1.{py,out}`, `menu_single_v1.{py,out}`; exact; all 346,104 sets of seven
distinct readings in `1 … 24`) `[VERIFIED — exhaustive exact]`. Each instant in the menu is a way of viewing the
arrangement:
- `B`: the bound, an AP at scale `d_min`;
- `L`: ladder rungs `a/q`, the grid mod `q`;
- `N`: nudges, the grid mod 8 plus one deviation;
- `R_q`: rung R1, the multiples of `q` as their own AP plus the grid mod `q` for the rest;
- `V`: reverse R1.

**Every set is isolated by at least one of them (0 missed).** The views overlap heavily. How many sets each works for:

| view | `B` | `L` | `N` | `R2` | `R3` | `R4` | `R5` | `R6` | `R7` | `R8` | `V` |
|---|---|---|---|---|---|---|---|---|---|---|---|
| works for | 200,736 | 268,853 | 112,169 | 179,748 | 223,910 | 170,807 | 211,811 | 135,254 | 206,136 | 160,107 | 27,185 |
| the only one | 14 | 324 | 0 | 5 | 5 | 6 | 1 | 0 | 19 | 0 | 1 |

Only 375 sets depend on a single view. For those, the cascade often isolates at a different view's instant (e.g.
`(1, 2, 3, 8, 17, 22, 23)`: ladder only; the cascade lands at `25/176`, reading 22 on lap 3).

**Reading.** The owner's guarantee, stated as what must be proved: *every arrangement has an AP/grid view in which
every reading's deviation from its grid position stays inside that position's margin.* The menu gives explicit views
(`B`, `L`, `N`, `R_q`, `V`, all with proved conditions in Lean: R1, the ladder, `GridNudgeN`, `RungR1N`), and
exhaustively up to 24 one of them always has room. The next step is the case structure of that "always", starting
from the residual sets (multiples of 5, 6 or 2 and 3, 7 and 8 all present), where only the `R_q` and `N` views remain.

---

## E91 — 2026-09-26 — the single-view sets, perturbed

(`single_perturb_v1.{py,out}`; exact; the 375 sets up to 24 that exactly one view isolates; each reading moved by ±1,
±2, i.e. one runner's speed changed; 7,718 perturbed sets) `[VERIFIED — exact]`:

| single view | perturbed sets | its view still works | mean views open after | no view |
|---|---|---|---|---|
| `B` | 234 | 219 | 3.99 | 0 |
| `L` | 6,770 | 6,649 | 3.05 | 0 |
| `R2` | 98 | 70 | 4.05 | 0 |
| `R3` | 81 | 54 | 3.74 | 0 |
| `R4` | 116 | 74 | 3.90 | 0 |
| `R5` | 19 | 15 | 3.47 | 0 |
| `R7` | 382 | 320 | 3.50 | 0 |
| `V` | 18 | 10 | 4.06 | 0 |

- **No perturbed set loses every view.** The one view mostly survives, and on average three to four views are open
  after a single change.
- **A set that depends on one view is a coincidence among views, not a thin place in the isolation.** One runner's
  change reopens several.
- The cascade's own isolation moves by more than a factor 1.5 in only 188 of 7,718.

The views behave like the pair laws: each is locally robust, and where one closes others are open.

---

## E92 — 2026-09-27 — the crowding test

**Owner:** runners are bounded by their neighbours (distinct speeds); *"crowd them too evenly and all of a sudden you
have AP again."*

(`crowding_v1.{py,out}`; exact; the 145,368 sets of seven readings in `1 … 24` where the bound `1/(8·d_min)` is not
lonely) `[VERIFIED — exhaustive exact]`:
- Some other runners' neighbour gap is smaller than `d_1`: 77,173.
- **The runners blocking the bound are in a crowded pair (a neighbour gap `< d_1`) in only 32,913**; every blocker in
  31,553. Mostly the bound fails because a reading, spread well away from its neighbours, wraps onto a multiple of 8 at
  the nearest runner's scale (residue within `d_min` of `0 mod 8·d_min`): a grid collision, not crowding.
- **At the cascade's isolation the tightest pair is still within one eighth of each other in 72,354** (separation
  `8·g_min·t*`: `< 1` in 72,354, `[1, 2)` in 63,237, `[2, 3)` in 8,397, larger in 1,380). Crowded runners ride together
  in one clear eighth, harmless, as the owner said of shared eighths.
- The scale reading at the isolation sits next to a smallest gap in 53,448.

**Reading.** As operationalised here (a gap under `d_1`), crowding is not what closes the bound; the grid collision
is. Crowded groups are carried through intact and do not need separating. The owner's "evenly crowded is an AP again"
is consistent with that: a crowded group moves as one. What the cascade has to resolve at the bound is the reading
that collides with the subject's own residue class, and its first move goes to that reading's own exit
(`(8k+1)/(8b)`, the bound nudged by the colliding reading).

---

## E93 — 2026-09-27 — the first move is a nudge at the nearest runner's scale

(`nearest_nudge_v1.{py,out}`; exact; the 145,368 sets of seven readings in `1 … 24` where the bound is not lonely)
`[VERIFIED — exhaustive exact]`. At the bound `t₀ = 1/(8m)`, `m = d_min`, each reading sits at `ρ = d/(8m) mod 1`. The
first move goes to the latest collider's exit `t₁ = (8k+1)/(8b)`, which multiplies the scale by `λ = t₁/t₀` and moves
every reading forward by `Δ = d·(t₁ − t₀) = (λ − 1)·d/(8m)` laps, in proportion to its size.
- **The first move isolates 54,642.**
- **In all 90,726 others, the reading left in the slot was clear at the bound and was pushed forward across the
  entering edge `7/8`** (`Δ < 3/4`). There are no wraps (`Δ ≥ 3/4`) and no colliders returning.
- `λ − 1 < 1/4` in all 145,368 (`< 1/8` in 47,481).
- **Caveat, recorded before use:** with readings `≤ 24`, the shift `(λ − 1)·d/(8m)` stays under about `3/4`, so "no
  wraps" is largely forced by the range. It is not evidence about wide-spread sets and must be checked on them.

**Reading.** The first move is a nudge at the nearest runner's own scale: every reading shifts forward in proportion to
its size, and the move fails only when a reading near `7/8` is pushed over the edge. The room condition is
`ρ + Δ ≤ 7/8` for the readings near the edge. The pushed reading's exit is the next move, so the relay is a chain of
such nudges.

---

## E94 — 2026-09-27 — the first move on widely spread readings: the E93 caveat confirmed

(`nearest_nudge_wide_v1.{py,out}`; exact; random sets with `d_min ∈ 1…20` and the rest up to 2,000; 49,654 with the
bound not lonely) `[VERIFIED — exact, this sample]`. The first move isolates 20,767. Of the 28,887 failures:
- edge pushes alone in 23,807;
- wraps (a reading shifted `≥ 3/4` lap into the slot) in 3,875;
- a collider back in the slot in 1,811 (combinations counted in each).

**E93's "edge pushes only" was forced by the range.** In general a failed first move leaves three kinds of readings in
the slot:
- **edge:** near readings nudged over `7/8`;
- **wrap:** far readings carried round by a shift of most of a lap, their grid residue re-read at the new scale;
- **back:** a collider that returns.

The edge kind is the nudge's room condition. The wrap kind is the grid at the new scale, as in E76 (six residues turning
at their own rates).

---

## E95 — 2026-09-27 — the chain of nudges; repeats are what exceed the budget, and they are not slot-sharing

**The chain** (`nudge_chain_v1.{py,out}`; exact; exhaustive readings `≤ 24`, 145,368 relays; wide sample, 30,997)
`[VERIFIED — exact]`:
- The nudges do not shrink step by step: the factors `λᵢ` decrease along the chain in only 26,649 of 90,726 chains of
  length `≥ 2` (wide: 8,642 of 17,978).
- A setter repeats in 9,091 relays (wide: 1,253). A wrap occurs in 376 (wide: 3,346).

**The budget** `[PROVED — from Thm 6.25]`. Each move multiplies `R` by less than `9/7`, and `(9/7)⁷ < 7`. A chain whose
setters are all different has at most 7 moves and ends inside the first lap. Only repeats take a relay further.

**Are repeats the owner's multiple cycles, two runners sharing a slot?** (`repeat_crowding_v1.{py,out}`; exact,
readings `≤ 24`) `[VERIFIED — exhaustive exact]`. At the repeat, the repeating setter shares its eighth with another
reading (`|d − s|·t < 1/8`) in **540 of 9,091**. For comparison, some setter shares its eighth when it sets in 40,776 of
the 136,277 chains without a repeat. **As operationalised here, repeats are not caused by slot-sharing.** E67 recorded
their commoner shape: a fast runner whose clear band is bridged by others, often by a slower runner's longer zone.
Those cost little, since a fast setter at lap `M` multiplies `R` by less than `(8M+1)/(8M−1)`.

---

## E96 — 2026-09-27 — who repeats, at which laps, and which ratio caps the displacement

**Owner:** *"I believe there is a scale or ratio that will dictate how far out the isolation point gets pushed,
similar to d_min."*

(`displace_ratio_v1.{py,out}`; exact; the 145,368 relays of readings `≤ 24`) `[VERIFIED — exhaustive exact]`:
- **Repeaters are the fast runners.** By rank: 6 in 4,428, 5 in 3,162, 4 in 2,539, 3 in 1,486, 2 in 458, 1 in 49. By
  `ρ = d/d_min` they cluster just below 8 (8 in 2,963; 7 in 1,850), with peaks at 16 (1,549) and 21 (1,150): the runners
  that collide at the bound.
- **They set on consecutive laps:** (1, 2) in 5,536, (2, 3) in 2,830, (3, 4) in 2,663. A runner with `ρ ≈ 8` passes the
  slot about once per unit of `R`, so a relay spanning a unit or two meets it again.
- **Ceilings on the displacement** (largest final `R` per value):
  - the collider's lap `k` at the bound (`b ≈ 8k·d_min`): `k = 1` 5.667, `k = 2` 3.571, `k = 3` 3.571;
  - `b/d_min`: 4.7–5.7 for `b ∈ [7.3, 8.5]·d_min`, and 3.571 at 16 and 24;
  - `g_min/d_min` (crowding): 5.667 at 0.33, 4.714 at 0.5, 4.688 at 0.67, 3.905 at 1, 4.4 at 1.5, 3.3 at 2, 2.2 at 3;
  - `S`: peak 5.667 at `S = 8`, falling to about 3.5 by `S = 14`;
  - `d₂/d_min` and `d_min/g`: no ordering.

**Reading.** The displacement is set by the runner that collides at the bound, and it is largest for a collider on its
first lap (`b ≈ 8·d_min`), the same runner that repeats. It is a candidate for the owner's ratio: `d_min` sets where
the isolation starts, and the collider's lap sets how far it can move. **Range caveat:** readings `≤ 24` restrict
`k ≤ 3` and cap `S`. **Next:** the wide sample, measuring the displacement in the collider's own units against `k`.

---

## E97 — 2026-09-27 — the displacement on widely spread readings; the spread against 8 is the ratio

(`displace_collider_v1.{py,out}`; exact; random sets, `d_min ∈ 1…20`, readings to 2,000; the slowest runner)
`[VERIFIED — exact, this sample]`. For every collider lap `k` from 1 to about 250 the final `R` stays at most 1.92. In
the collider's own laps the displacement grows about as `k·(R − 1)` (0.75 at `k = 1`, up to 39.1 at `k ≈ 250`). That
follows from the collider's lap time being about `1/k` of the bound, so it is not an invariant: `R`, in units of
`d_min`, is.

**The ratio that sets the displacement** (with E47, E96 and the certificates):
- `S ≤ 7`: isolated at the bound, `R = 1` (R1).
- `S` from 7 to about 11: a reading near `8·d_min` collides on its first lap. The displacement is largest here: `R` up
  to 5.667 for readings `≤ 24`, and late events up to `R ≈ 15` for `S ≤ 2993/273` (E47–E48).
- `S` larger: the ceiling falls (about 3.5 by `S = 14`; under 2 on the wide sample).

So `d_min` sets where the isolation starts, and the spread's nearness to `8·d_min` sets how far it can move. That is the
grid collision at the bound (E92), and the repeating runner is that collider coming round on consecutive laps (E96).
This matches the proof's existing split: the certificates cover `S ≤ 24`, including the late events, and Case C
(`S > 24`) sits at the small-displacement end.

---

## E98 — 2026-09-27 — the repeaters perturbed

**Owner:** *"If you perturb these with cascade you will see."*

(`repeater_perturb_v1.{py,out}`; exact; 400 relays sampled from the 9,091 with a repeated setter, readings `≤ 24`;
only the repeater's reading moved, by `e ∈ [−1, 1]` in steps of `1/64`) `[VERIFIED — exact, this sample]`:
- **The repeat holds over a window of about one unit of the repeater's reading.** The interval of `e` around 0 where it
  still sets twice is most often `10/8` wide (123 of 400); nearly all lie between `5/8` and `2`.
- **Why the repeat stops at the window's ends:**

  | cause | ends |
  |---|---|
  | isolated before the repeater returns | 407 |
  | the relay reaches the repeater's next zone, but it is not in the way there | 145 |
  | the repeater never sets | 121 |
  | the edge of the scan | 127 |

- **With the repeat, the isolation lies further out; without it, at the bound:** `R` has median 2.07 (at most 5.0)
  with the repeat, and falls to median 1.04 once the repeat is gone.

**Reading.** A repeat is a timing coincidence. The fast collider comes round again just inside the relay the others
are running, and that return is what carries the isolation past the bound. Move its speed by about one unit and its
return falls after the relay has already reached isolation, at `R ≈ 1.04`. So the repeat needs the others' relay to
last exactly as long as the repeater's clear band (E67's loop), a condition about one unit wide in the repeater's
speed.

---

## E99 — 2026-09-27 — the extra R each repeat adds

(`repeat_increments_v1.{py,out}`; exact; each repeat is a setting by a runner that has already set in the relay;
increments of `R` between successive repeats) `[VERIFIED — exact]`:

| | exhaustive `≤ 24` | wide sample | longest relays (late events) |
|---|---|---|---|
| relays with a repeat | 9,091 (1 repeat: 7,021) | 1,253 (1 repeat: 1,013) | 15 (all `≥ 8` repeats) |
| second increment `<` first | 1,939 of 2,070 | 224 of 240 | 15 of 15 |
| increments shrink all along | 1,378 of 2,070 | 192 of 240 | 0 of 15 |
| largest increment by repeat index | 2.0, 1.446, 1.057, 1.024, 0.75, 0.511 | 0.707, 0.333, 0.335, 0.043, 0.015, 0.031 | 1.798, 0.845, 1.047, 0.913, 0.363, 0.523 |

- **The ceiling on each successive repeat's contribution falls** in both the exhaustive and the wide data. Individual
  relays do not always shrink step by step.
- **In the longest relays the increments stay small (about 0.1–0.9) throughout, except one jump of about 2.0–2.5.**
  That jump is the nearest runner's own zone, `R ∈ (7, 9)`, width 2 in `R`. The long relays reach `R ≈ 10–11.5` by
  many small repeats plus that one crossing.

**Reading.** A repeat by a runner of ratio `ρ` must cross its clear band, which is `6/ρ` wide in `R` (0.75 for
`ρ ≈ 8`, 0.375 for `ρ ≈ 16`). The fast colliders repeat cheaply, and only the nearest runner's own zone adds a large
step. This bounds each increment by the repeater's band plus the relay across it. It does not bound how many repeats a
relay can chain; the late events chain about 20.

---

## E100 — 2026-09-27 — the grand return in Lean; where the cascade lands among the views

**Owner:** *"for integers, there is the grand return where all runners return to 0 at the same time essentially,
which means the pattern would repeat from there"*; then *"The cascade doesn't search though, so while the grand return
provides a finite cycle, I don't actually think it needs it. So there must be a mechanism that dictates where the
isolation is pushed."*

**`LRC/Spec/GrandReturnN.lean`** (commit `436fcde`; Spec gate PASS, 1,624 declarations, axiom-clean) `[PROVED —
axiom-clean]`. `lonely_add_int`: for whole-number readings the pattern repeats after every whole instant.
`lonely_mirror`: it is lonely at `1 − s` exactly when at `s`. `exists_lonely_iff_half`: it is lonely somewhere exactly
when it is lonely in `(0, 1/2]`. This fences the window `[1/(8·d_min), 1/2]`, ending at the half lap. As the owner
says, the cascade does not use it.

**Where the cascade lands** (`cascade_vs_menu_v1.{py,out}`; exact; all 346,104 sets of readings `≤ 24`) `[VERIFIED —
exhaustive exact]`. The cascade's isolation is exactly one of the explicit views in 310,889:

| view | sets |
|---|---|
| the bound `1/(8·d_min)` | 200,736 |
| the next opening `9/(8e)` of some reading `e` (lap 1) | 63,806 |
| rung R1 `a/q ± 1/(8·min D_q)` | 37,438 |
| reverse R1 `9/(8·e_max)` | 7,847 |
| a ladder rung `a/q` | 1,062 |

In the other 35,215 it lands on a later opening of some reading (lap `≥ 2`); a later view isolates each of those too.

**Reading.** The isolation is displaced from the bound to the nearest candidate scale that has room: in 76% the bound
itself or one reading's next opening (the AP at that runner's scale `e/9`), in 11% a rung plus its multiples' own
deviation. The views are ordered by time, and the cascade lands on the first one with room.

---

## E101 — 2026-09-27 — handover v4; an owner ruling recorded

**Owner ruling, 2026-09-26 (chat), not previously logged:** asked whether a measure argument inside a single window
(not a density statement across arrangements) could be used, the owner answered *"it can be provisionally use if
completes the proof part."* None has been used.

**Handovers.** `HANDOVER_2026_09_26_v3.md` (commit `d2a8584`) was checked by `compile-diff` against v2 and E67–E100,
which found 45 losses: four figures in disagreement with their sources, hypotheses and scopes dropped, and v2's open
items and retractions missing. `HANDOVER_2026_09_26_v4.md` repairs them. v2 and v3 are kept unchanged.

---

## E102 — 2026-09-27 — Lean review; the cascade is the oracle; where the displaced isolation lands

**Lean review** (Spec gate re-run 2026-09-27: PASS, 99 modules, 1,624 declarations axiom-clean, coverage 1,624 of
1,638, OWED register unchanged). The six new modules (`ProgressionPairN`, `GridPairN`, `FlankSumN`, `GridNudgeN`,
`RungR1N`, `GrandReturnN`) state what their docstrings say. None is imported by any other module and none discharges
`CaseB8` or `CaseC8`. Docstring defects: `ProgressionPairN` asserts the surviving interval
`[a²/(8·d_a), a(8−a)/(8·d_{8−a})]`, of which only the left endpoint is proved; `SlowestSkeletonN` says Case B is
verified at `T = 22` where E66 gives `T = 24`. The fact "within `1/8` of `m/8`, `m mod 8 ∈ 2…6`, is clear" is proved three
times. Owed: reverse R1, the bound-grid lemma, `Lonely8` wrappers for the whole-number forms.

**Owner (chat, verbatim):** *"Ok I want to be sure you read the mistakes or misunderstanding the last session had, mainly
to do with trying to import previous proofs frame work instead of reasoning within this new/novel work"*; then *"Yes the
cascade is your oracle because it will instantly find the isolation points of any arrangement. What that leaves you to do
is make sure we have the mechanisim it uses and we will have proof. Most useful if you ever find an exception or counter
example is to then perturb it through cascade so you can see the mechanisim."*

**The relapse this answered.** After re-reading handover v4, the session's reply framed the proof as the cascade orbit
stopping or passing the half lap because the openings are finite (a search that must terminate), leaned on the
distinct-setter move budget (termination counting), wrote "hands the isolation", proposed hunting the arrangements
closest to the half lap, and restated the conjecture as an equivalent existence statement. The half-lap observation (a
crossing of `1/2` goes through an even reading `b` and lands at `1/2 + 1/(8b)`, which the mirror shows is not lonely)
stands as mathematics and is a check, not the frame. Memory:
`feedback_n8_cascade_is_the_oracle_2026_09_27` (place test: a draft must name where the isolation lands, checkable
against the cascade, not only that or when it stops).

**Every landing is a rung plus its own deviation** (`rung_landing_v1.{py,out}`; exact; all 346,104 sets of readings
`≤ 24`) `[VERIFIED — exhaustive exact]`. The cascade's isolation is `t* = (8K+1)/(8e) = K/e + 1/(8e)`: the rung
`a/q = K/e` in lowest terms plus the deviation forced by `e`. Loneliness forces `e` to be the least reading divisible by
`q`: 346,104 of 346,104. The session's further claim that every multiple of `q` lies in `[e, 7e]` is **false** (holds in
281,137); the condition is residues mod `8e` in `[e, 7e]`. Denominators: `q = 1` (the bound) 200,736; `q = 3…8`
36,940; `q = 2` never; `q > 8` 108,428, where `e` is the only multiple of `q` in 106,543, so there the rung reading is
just runner `e`'s own opening on lap `K` and adds nothing.

**Where the displaced isolation lands** (`landing_setter_v1.{py,out}`; the 145,368 sets not isolated at the bound)
`[VERIFIED — exhaustive exact]`: the setter is never the nearest runner (ranks 2–7: 5,527 / 16,353 / 28,652 / 34,078 /
31,528 / 29,230); its lap `K ≤ 7` (`K = 1`: 85,137); `R* < 1.5` in 108,249 and `R* < 5.67` always; the setter was in the
slot at the bound in 59,963 and clear there in 85,405. (`e < (8K+1)·d_min` in every case is `R* > 1` restated.)

**Not new.** The log-time form (every runner's blocked windows are one fixed set shifted by its log-reading) was reached
for again; it is E11 and `LogTimeN`.

---

## E103 — 2026-09-27 — E100's next step: the 35,215 sets past lap 1, perturbed through the cascade

**Owner:** *"Please remember that floating point is banned, exact only, we prefer to use cascade or the boundary set
method, we do not any runner stationary"*; asked that the last exchanges before the compaction be read in full, not
grepped, to get back to where the work was. Read: transcript lines 1225–1640 (E89 to E101). The thread resumed here is
E100's stated next step.

**What closes the lap-0/1 openings, and does one move reopen one** (`lap1_reopen_v1.{py,out}`; exact; the 35,215 sets
of readings `≤ 24` whose cascade isolation is not an explicit view) `[VERIFIED — exhaustive exact]`:
- In 8,952 a lap-0/1 opening `(8k+1)/(8e)`, `k ≤ 1`, is itself lonely, later than the cascade's instant; in 26,263
  every lap-0/1 opening at or after the bound is blocked.
- One runner is in the slot at every lap-0/1 opening in 7,612; otherwise two to six runners are needed between them
  (1: 7,612; 2: 12,996; 3: 7,944; 4: 5,059; 5: 1,525; 6: 79).
- Moving one reading by `±1` or `±2` (kept positive and distinct) brings the cascade back to a lap `≤ 1` opening in
  34,983 of 35,215; in 33,194 of those a reopening move is on a runner that lies in every minimal blocking set.

**The 232 that no single move reopens** (`lap1_stuck_v1`, `lap1_stuck_check_v1`) `[VERIFIED — exhaustive exact]`: every
one has `d_min = 1` and exactly two readings on multiples of `8·d_min` (16 and 24): two runners in the subject's own
slot at the bound, a double grid collision, which one move cannot remove. Their isolation is just past the bound, at
`R* = 17/15` (runner 15's opening on lap 2) or `25/22`, `25/23` (lap 3). This is the case the owner singled out at E89
(two runners sharing the subject's slot).

**Correction to E100's classification.** "Lap 2 or later" measured the setter's lap, not the displacement. A fast
runner's second or third opening comes just after the bound: of the 35,215, those set on lap 3 have `R* < 1.25` in 9,444
of 15,089, and every lap-`K` group has most of its mass below `R* = 1.75` (`lap1_stuck_check_v1.out`). The displacement
is `R*`, and these sets are displaced little.

---

## E104 — 2026-09-27 — the proof plan against the Lean tree; the double collisions moved off the grid

**Owner:** asked to check the proof plan (`PROOF_PLAN_ORDER8_v1.md`) is still correct and whether Cases A, B and C are
all still needed, *"as I feel some of our lean work might have lightened the load"*; and to run the continuous
perturbation of the double collisions.

**Two proved reductions, both axiom-clean (Spec gate 2026-09-27).**
1. `SlowestSkeletonN.lonelyRunnerAt8_of_cases T`: the conjecture from `CaseB8 T` and `CaseC8 T`, Case A by R1. Both
   Props quantify over **every** reading set of a slowest runner, i.e. every set of seven distinct positive whole
   numbers.
2. `OrderEightN.lonelyRunnerAt8_iff_residual` (both directions): the conjecture holds **exactly when every
   `EightResidual` set is lonely at `1/8`**. `EightResidual` keeps only sets with an odd reading, no common factor, a
   multiple of each of 5, 6, 7 and 8, `7a < b` for some pair (the `spread` field), cost `≥ 8`, and none of the proved
   openings: free flank, shifted, fast singleton, first lap or `−7` at any flank, rational openings at `N ∣ 8`, thirds,
   fifths, `N = 6, 7, 9`, any resolution `D ≤ 64`, fast pair, block split.

**What this does to the plan** `[PROVED — reading of the two Lean statements]`:
- **Case A is not needed.** The `spread` field excludes R1 sets from the residual.
- **Cases B and C are needed only on residual sets.** Plan v1 owes them on every set; route 2 owes them only where
  every proved opening has failed.
- **On all 7-subsets of `[1, 40]` the residual is empty** (`experiments/nN/eight_residual_count_v6.out`: the v5
  residual's seven sets clear at `D ≤ 5`) `[VERIFIED — exhaustive exact, finite window]`. The residual is infinite, so
  this is a window, not a proof.
- **Stale open item.** Handover v4 §5.6 lists the residual sets `(2,12,15,21,32,34,38)` and `(4,7,8,15,29,36,37)` as
  unresolved. Both lie in `[1, 40]`, so neither is in the current residual; the cascade isolates them at `R* = 34/21`
  (3 moves) and `36/29` (1 move). Both have `W/d_min ≤ 24`, Case B.
- Plan v1 also predates E56: its B/C boundary is 22 (now 24), and its Case C sub-cases (separated scales, compact
  clump) overlap residual fields that are already proved (fast pair, block split, fast singleton). A plan v2 stating the
  target as the residual statement is owed.

**The double collisions, moved continuously** (`double_collision_v1.{py,out}`; exact; four of E103's 232; readings 16
and 24 moved by `j/16`, `|j| ≤ 15`, singly and together) `[VERIFIED — these four sets]`:
- In `(1,2,3,4,15,16,24)` and `(1,2,3,10,15,16,24)` the isolation **does not move at all**: `R* = 17/15` throughout,
  opened by runner 15. At the bound (`d_min = 1`, every reading on an eighth) runner 15 sits exactly on the entering
  edge `7/8`; the colliders on residue 0 force a forward move, any forward move carries 15 into the slot, and the
  isolation is at 15's exit `(2 + 1/8)/15`. The colliders decide that the isolation moves, not where to.
- In `(1,2,3,4,16,22,24)` the landing is 22's exit (`25/22`; 22 on residue 6 is carried in by 16's exit) until 16
  moves up by `5/16`; then 16's own exit comes first and the isolation is there, `R* = 272/261`, then 24's (`25/24`).
- In `(1,2,3,4,16,23,24)` it is 23's exit (`25/23`; 23 on the entering edge), or 16's own once 16 moves below 16 far
  enough to be the last to leave (`272/241`).

So in these sets the displacement is set by the runner nearest the entering edge at the bound (residue 7, or 6), the
leaving/entering pair of the pair law, and the collider only forces the direction. This is E93's edge push, seen
exactly; the second collider plays no separate part.

---

## E105 — 2026-09-27 — proof plan v2, the residual route; its loss check

**Owner:** *"Yes"* to writing proof plan v2 on the residual route (target: every residual set is lonely; Case B within
`24·d_min` by the certificates; Case C beyond it, open).

**`docs/n8/PROOF_PLAN_ORDER8_v2.md`** (v1 kept). Checked by `compile-diff` against v1, E102–E104 and the Lean definitions
before its first commit; the draft was repaired for every item. The corrections that change content:
- **Theorem 6.15 is existential.** The draft said a residual set is lonely "only at" an opening `(8K+1)/(8e)` with
  `e > 64` and `e/gcd(K, e) ≥ 10`; the correct statement is: if lonely, then lonely at some such opening, equivalently
  every lonely opening of a reading has both properties.
- **The converse was graded too high.** The fields negate class conditions, and Lean proves class ⇒ lonely only
  (`band_of_class`, `lonely_eight_at_rationalOpening`). The converse (lonely at the instant ⇒ class condition) follows
  from `rationalOpening_reading` and `r < M`; it is now stated in the plan, graded `[PROVED — in the text]`, and owed in
  Lean (`classClear_iff_band`, WP2).
- **`not_fast` is one-sided:** no reading more than 7 times every other; the least reading may lie far below the rest,
  which is Case C territory.
- **Backward views** (rung R1 backward, nudge backward) are excluded through the mirror (`GrandReturnN.lonely_mirror`),
  to the forward instant at `q − a`; ladder rungs `a/q` for every coprime `a`.
- **Figures:** E10's 22 members have `d_max/d_min` from 7.12 to 8.83 (all Case B); landings with rung denominator
  `≥ 10` are 107,049 of 346,104 (the 108,428 above 8 include 1,379 at `q = 9`); the 63,806 next-opening landings are all
  at `e ≤ 24`, excluded by the resolution field.
- **Attribution:** the recommendation to add the views as exclusions was the session's, in chat after E104, not in E104.
- **v1 items given fates** (plan §6): C-even and `K₆` superseded (E57–E68); the Case C window reduction measured in E56
  (`case_c_map_v1`) and kept as a tool; B3 subsumed by residual fields; tight points carried as conditional; the owner's
  three gap shapes and two-runner moves carried into WP3–WP4; E102's Lean hygiene items carried as WP8.

---

## E36 — 2026-09-27 — exhibit route: does the arrangement's TYPE decide the flank?

Author: go with **exhibit** (`DoorFlank`: name a flank and a lap for every runner of every arrangement; a finite case
split with each case's `(e, j)` named is admissible, `Spec/Target.lean`). Author: the arrangement types are few, since AP
is scale invariant and grid is continuous: evenly spaced (AP), clumpy with outliers and even with outliers (AP and/or
grid). Ordering is a real constraint: a runner cannot pass its neighbour without swapping, so in `CascadeRule.reading`
the slots `⌊(v_j − base)/D⌋` are monotone in speed (one line from the definition; not yet stated as a lemma).
First-lap clearance is **not** used (author's 2026-09-25 ruling, provisional only).

**Test** (`experiments/nN/redo/type_decides_flank_v1/v2`). Type of runner `k` = its rank plus every runner's slot
residue mod 8 against the AP of gap `d_min` from `v_k`. Per runner, exact (Thm 6.14): the flank ranks that work at some
opening `j < e`, and the cascade's flank. Runners deduplicated by normalised signed differences.

| range | distinct runners | types | types with ≥ 2 members | one flank rank works for all members | cascade's flank constant |
|---|---|---|---|---|---|
| every arrangement `1 = v₁ < … < v₈ ≤ 18`, gcd 1 | 155,520 | 95,888 | 5,134 | **5,122** | 3,344 |
| 6,000 random in `[1, 400]` | 48,000 | 37,548 | 3,413 | **3,413** | 2,945 |

No runner lacked a working flank. `[EMPIRICAL]`
- **The type nearly decides a working flank; it does not decide the cascade's flank.** The cascade lands on the first
  event; the exhibit needs only some flank, and at type level one exists in all but 12 types.
- **All 12 failing types contain runners in or just under the subject's own slot** (residue 0 or 7): the slot-sharers
  of E35. Within them the working flank depends on the sharers' laps and deviations, e.g. type rank 0, residues
  `(0,1,2,3,4,5,7,0)`: `(1,2,3,4,5,6,8,9)` works at flank ranks {5,6}, `(1,3,5,7,10,12,15,17)` at {6,7},
  `(1,3,6,8,9,12,15,18)` at {2,3,4,5,7}. So the type needs refining exactly at the sharers.
- **This type is not "few".** 95,888 types from 155,520 runners; the bound is `8·8⁸`, finite but large, and ordering does
  not reduce residues (any residue sequence comes from a monotone slot sequence). The author's classes (even / clumpy /
  outliers) are far coarser; whether a coarse class decides the flank is untested.
- **Not yet examined:** the lap `j`. It is unbounded (§6.10, `k ≈ linear in S`), so a finite case split can name it
  only as a formula in the arrangement, not as a constant.

---

## E37 — 2026-09-27 — the flank is a consequence, and the cascade read move by move

**Author:** the flank is a proxy for isolation, not isolation; the cascade directs you to the event; it is not a black
box. Agreed. At the event some runner sits exactly one eighth away (Thm 6.2(d)): that runner *is* the flank, after the
fact. Choosing a flank first and checking the rest is a search (E36 and my step 5 both did it). In Lean the
cascade-directed door is `DoorArrives` (`∃ N`, the map from the runner's first reading reaches a fixed point; no cap;
`doorArrives_iff`); the move is a written-down rule (`Target.lean`). Whether it replaces `DoorFlank` as the obligation of
record is the author's call.

**The 28-move case read move by move** (`experiments/nN/redo/cascade_mechanics_v1.out`): `(27,70,107,137,159,188,344,393)`,
runner 393, differences `−366, −323, −286, −256, −234, −205` (a clump, ratio 1.79) and `−49` (the nearest runner).
- **The nearest runner is the clock.** It starts exactly one eighth behind (7.00) and drifts steadily down through the
  slots, `7.00 → 6.80 → … → 1.09` over moves 0–22, about 0.2–0.4 eighths per move. The whole relay of 23 moves happens
  inside one of its laps. At move 23 it reaches the subject's slot itself (0.98) and its own opening is a large step.
- **The clump relays.** Each move advances every runner by `g·d_y/d_x` eighths (`g` the setter's shortfall below its
  landing slot, 0.4–2.0): clump runners by 1–3 eighths, the clock by 0.1–0.4. Through moves 3–23 the clump spans an arc
  of **5.1–6.2 eighths**, so as it turns one member keeps falling into the subject's slot band `(7, 1)`; each move puts
  that member one slot ahead and another arrives.
- **It lands when the clump fits.** After the clock's lap step the clump's arc is **4.0–4.6 eighths**; five moves later
  (move 28) the bunch sits in `[2.39, 5.07]`, the setter at 7.00 and the clock at 5.74: nobody in the band.

**The mechanism, in the framework's terms** `[reasoned from one trace]`. A group that fits in an arc of at most 6
eighths is the same condition as E33's "offsets leave a gap of at least 1/4" (2 eighths). The relay is a group whose
members are spread over more than 6 eighths; its arc changes only through the group's **internal** speed differences
(relative positions move at `8·Δd` eighths per unit time), not through the moves. For a far train the common position is
free, so only the arc condition matters (E33, `SyncPeriodN`); for a near clump the common position is carried by the
clock, and landing needs the arc condition **and** the gap sitting on the subject's slot. Not yet checked beyond this
case.

---

## E38 — 2026-09-27 — the shape space, and a noted plan

**Author:** the grand-return search is not the framework. Because of mirroring and scale invariance there are only so
many valid types (clumpy with a fast outlier is slow outlier with a clump). Can the 6-dimensional shape space show the
deformations merely relocate the loneliness? "We already have half a proof."

**Mirror, in Lean.** `Arrangement.lonelyAt_const_mul` holds for every `c`, including `−1`; with `circDist` even,
reversing every speed leaves each runner lonely at the same instant.

**The shape space** `[reasoned; each step cites a proved statement]`.
- Translation and scale (proved) leave the seven consecutive gaps `g = (g₁…g₇) > 0` up to a common factor; the mirror
  reverses the sequence. A runner's readings are sums of consecutive gaps, so **linear in `g`**.
- At flank `e` and lap `j`, a reading `d` is clear iff `(8M+1)e ≤ (8j+1)d ≤ (8M+7)e` for some whole `M` (Thm 6.12). With
  `e`, `j` and each reading's `M` fixed, that is a finite set of **linear inequalities in `g`**: a polyhedral cone. So a
  runner's lonely shapes are a **union of cones**, one per `(flank, lap, band assignment)`.
- **A deformation is a path in the shape space; relocation is crossing from one cone into a neighbouring one** (the flank
  or lap changes). "Deformation merely relocates" = **the cones leave no hole**.
- **The AP is one interior point** (all gaps equal): lonely by the φ(n) law, on the boundary of its cone (tight; the
  two-pinner lemma is its local persistence).
- **The faces of the shape space are the lower orders.** A face is where some gaps vanish relative to the others: runners
  merge, fewer than eight distinct speeds, orders ≤ 7, **native and proved**, with slack (`1/7 − 1/8` and more). Each
  separated-scale lemma is one face read this way: R8 (one runner far), fast pair, block split, `lonely_of_train_collapse`
  (a tight train is a face where the train's gaps vanish), `RealEightN`'s merge.
- **Where the laps grow:** the needed lap is unbounded (§6.10) exactly as the shape approaches a face; the cones
  accumulate there, which is where the lower orders take over instead.
- **What a proof would need in this picture:** (a) around each face, a neighbourhood of explicit width in which the
  lower-order slack carries loneliness (width depends on the lower-order instant, so near corners it recurses: the scale
  tree of E30); (b) the compact remainder of the interior, away from the faces, covered by finitely many cones, each
  checked as linear inequalities. Nothing here is proved beyond the cited pieces; (a) and (b) are open.

**Noted, not run (author: note it down).** Type test: types = groups split at large gaps (72 up to mirror), each
separator near or far, each group AP-like (deviations within 1/8) or grid-like, runner position within its group. Per
type, many arrangements, every runner, exact cascade; record the mechanism (clock = near neighbour, which runners are
in the way in turn, where the event lands read as the AP at that scale) and check it is uniform per type.

**Terminology.** "Relay" (E32–E37) is my shorthand, not a framework object. In the framework it is the cascade's run of
lap-completion zones (Thm 6.2(c)): the runners in the way at successive moves.

---

## E39 — 2026-09-27 — (b) measured on two slices of the shape space; back to the proof plan

**Slices** (`experiments/nN/redo/shape_slices_v1`): the AP with gaps all 1, two gaps varied over `k/16`, `k = 1…128`,
16,384 shapes per slice, every runner, exact; each shape's cone = the cascade event's (flank rank, lap `j`, band of
every reading). Slice A = the two end gaps, slice B = the two middle gaps.

| | cones | runners next to the varied gaps | other runners | single-shape cones | largest `j` |
|---|---|---|---|---|---|
| A | 583 | 132–246 each | 6–14 each | 110 | 17 |
| B | 702 | 167–280 each | 12–20 each | 130 | 21 |

Towards the edges (cones met in each band of the smaller / larger varied gap): smaller gap `[1/16, 1/8)`: 182 (A), 220
(B); larger gap `[4, 8]`: 336 (A), 384 (B). `[EMPIRICAL]` Limits of the measurement: the cascade's cone is one cone
containing the shape, so the counts **overstate** what a minimal cover needs; the 1/16 grid can **miss** cones thinner
than a grid step, and the 110–130 single-shape cones say many are that thin. Read as it stands: **each 2-D slice needs
hundreds of cones**, with `j` rising towards the outlier edge. A cone cover of the 6-dimensional middle is not a small
object; no extrapolation to 6-D is claimed.

**Author (the proof plan).** AP is scale invariant and grid is infinite, which explains how arrangements mix and match.
The one and only hard problem is **two runners in a slot, which delays the isolation**. It has a relationship between
(i) missing grids, (ii) not being too close to a third runner (where it would become AP), and (iii) the number of
cycles until it isolates. Consistent with this session's record: every cascade move cures a runner in the subject's
slot (E35, 13,086 of 13,086); every type E36 could not decide contains such runners; the delay law of E33 is a group on
the eighth-slots.

---

## E40 — 2026-09-27 — two runners in a slot: the law, in one family

**Definition (reasoned from the grid).** Reduce by `g`, take residues mod 8. At a grid instant `p/(8g)`, `p` odd, runner
`j` sits exactly `(π_j − π_k)·p` eighths from runner `k` (Thm 4.11): clear unless the residues are equal. So what delays a
runner is **another runner in its own slot** (difference a multiple of `8g`); two *other* runners sharing a slot do no
harm. With eight runners, a doubled slot forces an empty one.

**Family** (`experiments/nN/redo/doubled_slot_v1/v2`): AP reduced speeds `0…7` (+100, all positive); the runner with
residue `r` moved to `s + 8m`: slot `s` doubled (pair `8m` apart), slot `r` empty, `c = (r − s) mod 8`. `s, r` all
distinct pairs, `m = 1…8` (to 12 for the table). 448 arrangements, 3,584 runners, exact cascade.

**Measured** `[EMPIRICAL — exact, this family]`:
1. **Only the doubled slot is delayed:** 0 of 2,688 other runners; 438 of 896 pair members.
2. **The far member of the pair is essentially never delayed** (one case per `c`, at `s = 0, m = 1`); the **home**
   member (inside the AP) carries the delay.
3. **Home member at an interior slot (`s = 1…6`): always the minimal relocation.** Event at the partner's own
   opening, lap `m`: `t* = (8m+1)/(64m)`, i.e. the grid instant `1/8` stretched by `1 + 1/(8m)`. `[reasoned proof]` at
   that instant the partner is exactly one eighth ahead, and every AP reading `a`, `1 ≤ |a| ≤ 6`, sits at
   `|a|·(1 + 1/(8m)) ≤ 6·9/8 = 6.75` eighths: clear.
4. **Home member at an end of the AP (`s = 0`, mirror `s = 7`):** it has a runner reading exactly 7 (the far end), and
   the stretch pushes it past 7. The event then depends on the **empty slot** `c` (mirror `c ↔ 8 − c`), independent of
   `m` except where `8m` is a multiple of the flank distance:

| `c` (s = 0) | event `R = 8t*` | flank | lap |
|---|---|---|---|
| 1 | not delayed | — | — |
| 2 | 25/7 | far end, `d = 7` | 3 |
| 3 | 17/7 | `d = 7` | 2 |
| 4 | 9/5 | `d = 5` | 1 |
| 5 | 3/2 (odd `m`); `(12m+1)/(8m)`, partner at lap `3m/2` (even `m`) | `d = 6` / partner | 1 / `3m/2` |
| 6 | 9/7 | `d = 7` | 1 |
| 7 (the runner reading 7 is the empty one) | the minimal relocation of item 3 | partner | `m` |

   Exceptions: `m = 7` (partner 56, a multiple of 7), `m = 5, 10` at `c = 4` (multiples of 5): the partner then sits on
   the flank's lattice and becomes the flank itself.

**This is the author's three-part relationship, in this family.** (i) *Missing grid*: the empty slot `c` sets the
delay. (ii) *Too close to a third runner*: the delay beyond the minimal relocation happens only when a third runner
reads exactly 7 (the AP's far end, pinned at 7/8), and disappears when that runner is the missing one (`c = 7`).
(iii) *Cycles until isolation*: the flank's lap, 1 to 3, fixed by `c`. The pair's separation `m` enters only through
`m mod d`, so **the family is a finite case split with a named `(flank, lap)` per case** (exhibit form), checkable by
residues. Not yet proved or formalised; one family only.

---

## E41 — 2026-09-27 — the doubled-slot family proved; general grids measured

**Step 1, proved** (`LonelyRunner/LRC/Spec/DoubledSlotN.lean`; gate `experiments/nN/spec_gate_doubled_slot.out`,
PASS 1,735/1,735). The E40 family, as an arrangement: runners indexed by slot, speed `100 + i`, the runner of slot `r`
moved to `100 + s + 8m`; every speed positive, all distinct (`dsV_injective`). `dsT` is the **written-down witness map**;
`ds_lonely`: every runner, every `s ≠ r`, every `m ≥ 1`, is lonely at its instant; `ds_exists`: with `t > 0`.
`[PROVED — axioms propext, Classical.choice, Quot.sound; no sorry, no native_decide]`
- outside the doubled slot: `1/8` (the grid: nonzero residue offsets);
- far member: `1/(8(8m + s − 7))`, every reading in `[1/8, 7/8]` when `49 ≤ 48m + 6s`; else (`s = 0, m = 1`) seven named
  instants;
- home member, interior (or at an end whose far neighbour is the missing runner): `1/8 + 1/(64m)`;
- home member at an end: `(8N+1)/(8d)` by the empty slot, plus `1/(64m)` when the partner would read whole laps.
`m` enters only through divisibility; 85 constant cases generated by `gen_doubled_slot_lean_v2.py`, each band checked
in exact arithmetic before emission and re-checked by Lean. This is the exhibit form: a finite case split, every
instant named, for an infinite family. **It is one family** (the AP with one runner moved by whole laps).

**Step 2, measured** (`doubled_slot_grid_v1/v2`): grids with one doubled slot, every runner given random extra laps up to
`Q`. `[EMPIRICAL — exact]`
- **Outside the doubled slot: never delayed** (0 of 12,000 per `Q`). That is the grid argument and holds for every grid.
- Pair members (4,000 per `Q`), three classes:

| `Q` | A: lonely by the grid instant | B: delayed, minimal relocation `1/8 + 1/(64m)` works | C: delayed, it does not |
|---|---|---|---|
| 1 | 1,406 | 1,602 | 992 |
| 3 | 2,483 | 665 | 852 |
| 10 | 3,414 | 216 | 370 |
| 50 | 3,875 | 57 | 68 |

- **What blocks the minimal relocation in C** is the author's third runner, generalised: a runner whose position the
  stretch `1 + 1/(8m)` carries across a slot boundary. With small laps it is the slot next to the doubled one on the drift
  side (offset 7 ahead / offset 1 behind); with larger laps a runner further round whose stretch `D/(8m)` is a whole
  eighth or more.
- **C's event is not a fixed table.** Its flank is one of those blocking runners in about 55% of C cases (546 of 992 at
  `Q = 1`), rarely the partner, and its lap spreads with `Q` (up to 48 at `Q = 50`). The E40 end-case table does not carry
  over as it stands.

---

## E42 — 2026-09-27 — the delayed pair members of a doubled slot, grouped

`experiments/nN/redo/doubled_slot_C_v1` (grouping) and `_v2` (across lap sizes), exact, orientation normalised so the
partner is ahead (the mirror). Class C = a pair member delayed past the grid instant whose partner's opening is blocked.
`[EMPIRICAL]`
- **The empty slot does not decide the event outside E40's family.** Grouped by (empty-slot offset, blocker signature),
  each group still spreads over several events: at `Q = 1`, e.g. empty slot at offset 6 with the offset-7 runner blocking:
  the blocker's first opening (`R = 9/7`) in 203 of 421, an offset-5 runner's (`9/5`) in 56, and others. The other runners'
  laps choose among a few candidate openings.
- **Every event is an opening of a near runner at a small lap.** At `Q = 1` the events are from a short list,
  `9/7, 17/7, 25/7, 9/5, 3/2, 17/13, 17/12, 17/14, 17/15`: `(8N + 1)/d` with `d ≤ 15`, `N ≤ 3`.
- **Mostly the first opening after the grid instant**: 2,686 of 3,060 at `Q = 1`, 2,157 of 2,492 at `Q = 3`, 891 of 1,063
  at `Q = 10`, 648 of 852 at `Q = 50`; the rest a few laps later (up to 12).
- **The delay is bounded and shrinks with laps**: `R = 8t* ≤ 25/7` at every `Q` (so `t* ≤ 25/56`, under half a grid
  cycle; `25/7` is E40's largest), max 2.46 at `Q = 10`, 1.41 at `Q = 50`.

So in the author's three parts: the *cycles until isolation* stay under half a grid cycle, and the event is a near
runner's first (or nearly first) opening after the grid instant; *which* runner is set by the arrangement's laps, not by
the empty slot alone. No law of the E40 kind yet for general grids.

---

## E43 — 2026-09-27 — deviations: on the AP they relocate the event along the spine

`experiments/nN/redo/deviations_v1/v2`, exact: base arrangements (the AP; complete grids with laps ≤ 1, ≤ 3; E40's
doubled slot; doubled slot with laps ≤ 1), every speed deviated uniformly in `[−ρ, ρ]` gap units, 250 arrangements per
cell, every runner. At the grid instant a deviation `e` moves a runner `e` eighths (Prop 2.2), so `|e| < 1` keeps it in its
own slot's band. `[EMPIRICAL]`

**The AP: deviations relocate along the spine, between the φ(8) classes.**

| `ρ` | event's spine class `p` (`t ≈ p/8`) | max `|8t* − p|/(pρ)` | flank a class-`p` circle neighbour (offset `±p`) |
|---|---|---|---|
| 1/64 | 1: 1,761; 5: 129; 3: 110 | 2.05 | **2,000 / 2,000** |
| 1/16 | 1: 1,748; 3: 155; 5: 97 | 12.78 | 1,932 / 2,000 |
| 1/8 | 1: 1,699; 3: 256; 5: 44; 7: 1 | 6.85 | 1,791 / 2,000 |
| 1/4 | 1: 1,564; 3: 418; 5: 17; 7: 1 | 3.83 | 1,472 / 2,000 |

At small deviation every runner's event is a class instant `1/8, 3/8, 5/8`, moved by at most about `2ρ` relative, with
the flank the circle neighbour of that class (Cor 4.15's neighbour rule). When the class-1 instant is blocked (a
neighbour moved inward: the AP has no slack, §4.2) the event **jumps to class 3 or 5**. That is the author's picture: the
deviation relocates the isolation along the AP's spine; it does not remove it.

**Grids with laps and doubled slots: the spine is not their reference.** Many of their base events are already before
the grid instant (E41's class A), so distance to the spine measures nothing there. Against each runner's own base event
(`deviations_v1`): median factor ≈ 1.00, but 5–10% jump by factors 1.4–5 even at `ρ = 1/64` (the same class-jump
phenomenon), and the flank is a class neighbour in only 47–71%. Beyond `ρ ≈ 1/2` runners leave their slots and the
factors spread (to about 100 at `ρ = 1`).

---

## E44 — 2026-09-27 — the reference for grids with laps is the grid's own class instants

**Reasoned.** A complete grid (every residue once) is globally isolated at all four class instants `p/8`, laps or not
(the φ(8) law; whole laps invisible, Thm 4.12), so every runner is lonely there; a runner's *first* event may be earlier,
at its own scale, which is why E43's spine reading did not fit grids with laps. At `t = p/8` a deviation `e` moves a runner
`p·e` eighths, laps or not. Author on E42: the delay under half a grid cycle fits a mirroring pattern (for whole-number
speeds, lonely at `t` iff at `1 − t`).

**Measured** (`experiments/nN/redo/reference_grid_v1`, exact): complete grids with laps up to `Q`, every speed deviated in
`[−ρ, ρ]`, 200 arrangements per cell, every runner; for each class `p` the first lonely instant at or after
`p/8 − 1/64`, and the one nearest its class instant. `[EMPIRICAL]`

| laps `≤ Q` | `ρ` | max offset/`ρ` | median | flank the class-`p` neighbour |
|---|---|---|---|---|
| 0 (AP) | 1/64 | 0.64 | 0.11 | 1,600 / 1,600 |
| 1 | 1/64 | 0.65 | 0.07 | 1,600 / 1,600 |
| 3 | 1/64 | 1.48 | 0.04 | 1,591 / 1,600 |
| 10 | 1/64 | 1.56 | 0.03 | 1,405 / 1,600 |
| 10 | 1/8 | 0.58 | 0.03 | 1,091 / 1,600 |

**Grids with laps relocate like the AP**: every deviated runner is lonely within a small multiple of `ρ` (relative) of a
class instant, the laps do not enlarge the offset (the median shrinks), and at small `ρ` the flank is the class
neighbour. All four classes carry events. The doubled slot's pair members are not covered by this reference (the partner
sits on them at every grid instant); their reference is E40/E41's law.

---

## E45 — 2026-09-27 — the AP's neighbourhood, proved

`LonelyRunner/LRC/Spec/APNeighbourhoodN.lean`; gate `experiments/nN/spec_gate_ap_nbhd.out`, PASS 1,803/1,803.
`[PROVED — axioms propext, Classical.choice, Quot.sound; no sorry, no native_decide]`

The arrangement `apV c e`: speeds `c + i + eᵢ`, `i = 0 … 7`, every `|eᵢ| ≤ 1/32` of the gap (`apV_injective`; all positive
when `c ≥ 1`, `apV_pos`). The written-down witness map `apT`; `ap_nbhd_lonely`: every runner lonely at it; `ap_nbhd_exists`:
with `t > 0`.
- **interior runner** (`k = 1…6`): `1/(8d)`, `d` the nearer speed neighbour; every other reading lies in `[d, 7d]`.
- **end runner** (`k = 0`, and `k = 7` mirrored), readings `r₁ … r₇`: `1/(8r₁)` when `r₇ ≤ 7r₁`; otherwise the class-7
  instant `49/(8r₇)`: the far end exactly one eighth away, every other reading in its class-7 slot.

So on an open set of shapes around the AP (the first proved piece of E38's middle region) the deviation only relocates
the isolation: from the class-1 instant to its mirror class 7, the flank a circle neighbour of that class. The 56
(runner, reading) cases are generated by `gen_ap_nbhd_lean_v1.py`, bands from the AP's centre values, re-checked by Lean;
verified beforehand on 26,561 deviation vectors including all `3⁸` corner/centre vectors (`ap_nbhd_named_v1.out`).

**Scope.** The radius `1/32` is what the class-7 bands allow at the end runners (the tightest reading is the
offset-6 runner, which needs `ρ ≤ 7/180`); interior runners alone would allow `1/16`. Grids with laps (E44) and the doubled
slot's deviations are not in this theorem.

---

## E46 — 2026-09-27 — every complete grid's neighbourhood, proved

`LonelyRunner/LRC/Spec/GridNeighbourhoodN.lean`; gate `experiments/nN/spec_gate_grid_nbhd.out`.
`[PROVED — axioms propext, Classical.choice, Quot.sound; no sorry, no native_decide]`

A complete grid: whole-number speeds `uᵢ` with all eight residues mod 8 distinct (the AP with any whole laps), every
speed deviated by `|eᵢ| ≤ ρ`, `W` a bound for the whole-number differences. `grid_nbhd_exists`: if
`2ρ(14W + 21) ≤ 1`, every runner is lonely at a named positive instant.
- **The instant** (`gridT`): the runner's class-1 circle neighbours `A`, `B` (differences `≡ 1`, `≡ 7 (mod 8)`) sit one
  eighth away at their own openings `t_A = D_A/(8δ_A)`, `t_B = D_B/(8δ_B)`, both within `O(ρ)` of `1/8`. Each is clear on
  one side of its opening, fixed by its sign: `(+,−)` → `max`, `(−,+)` → `min`, `(+,+)` → `t_A` if `t_A ≤ t_B` else the
  class-7 instant `7t_B`, `(−,−)` → `t_B` if `t_B ≤ t_A` else `7t_A`. For the AP this is E45's rule.
- **Every other runner** keeps its residue `2…6` slot: the relocation moves it at most `c·|δ|·2ρ` eighths (`expand`).
- **The two neighbours exist** in every complete grid (`exists_nbrs`: the eight residues are all of `0…7`).
- **Scope.** The radius shrinks with the laps (`~1/(28W)`): each complete grid carries its own open neighbourhood; E44
  measured far larger offsets are tolerated in practice. With E45 this makes the neighbourhoods of all complete grids
  (every AP with every assignment of whole laps) proved regions of the shape space.

---

## E47 — 2026-09-27 — the doubled slot under deviation

`experiments/nN/redo/doubled_deviation_v1/v2`, exact: E40's family and one-doubled grids with laps ≤ 1, every speed
deviated in `[−ρ, ρ]`, 300 arrangements per cell, every runner, by role. `[EMPIRICAL]`
- **Runners outside the pair relocate along the spine**, like a complete grid (E44): the lonely instant nearest a class
  instant `p/8` is within at most `1.91ρ` (relative) of it, every runner, both families, `ρ = 1/256, 1/64, 1/16`
  (medians 0.06–0.13ρ). This holds for the runners **beside** the doubled slot too (two runners one slot away at the grid
  instant): max 0.71ρ. Against their own undeviated event (`1/8`, no slack) 5–25% jump to another class instant: the
  class jump of E43, not a loss.
- **The pair members relocate near their own delayed event** (the partner's opening, E40): E40 family, `|factor − 1|` at
  most `0.7ρ` with no jumps for `ρ ≤ 1/64`; 4 jumps of 300 at `ρ = 1/16`. With laps ≤ 1: medians `≈ 0.1ρ`, but 0–3 jumps
  per 300 and outliers to `413ρ` at `ρ = 1/256`; those are pair members whose delayed event has no slack (E41's class C).
  Not yet examined individually.

---

## E48 — 2026-09-27 — the doubled-slot family's neighbourhood, proved

`LonelyRunner/LRC/Spec/DoubledNbhdN.lean` (`dd_exists`), with `GridClassN`, `DoubledNbhdCoreN`, `DoubledNbhdCasesN`
(generated by `experiments/nN/redo/gen_doubled_nbhd_lean_v2.py`); gate `experiments/nN/spec_gate_doubled_nbhd.out`,
PASS 1,855/1,855. `[PROVED — axioms propext, Classical.choice, Quot.sound; no sorry, no native_decide]`

Every runner of the doubled-slot family (E40/E41), every speed deviated by `|eᵢ| ≤ 1/(512(m + 1))`, is lonely at a named
positive instant. The instant is always a named flank's **actual** opening: the undeviated instant `t₀` relocated to
`t₀·D_X/δ_X` (`reloc`: every other reading moves by at most `t₀(2η + 2ηK)`).
- **outside the pair**: E46's rule at class 1, or at class 3 (mirror 5) when the doubled slot is a class-1 neighbour slot
  (`readings_clear_p`); one neighbour when the other neighbour slot is the empty one (`readings_clear_single`);
- **far member**: the ratio condition at its nearest runner (`far_role`), or its seven `s = 0, m = 1` exceptions, each the
  opening of the one runner pinning the undeviated instant;
- **home member**: the partner's opening at an interior slot (`home_role`); at an end, the far-end runner's opening
  (unshifted; the partner then reads a fraction of denominator `dd`, `partner_lip`) or the partner's (shifted), per the
  empty slot, generated.

**Units, not primes** (author's check, 2026-09-27): the only coprimality used is `partner_lip`'s `Nat.Coprime P' dd`,
the partner's numerator a unit mod `dd` (φ), and the classes 1, 3 are units of `ℤ/8`. No primality anywhere.

**A tooling note.** Lean's `omega` is incomplete on some mod-8 lattice problems (it omits the dark and grey shadows); a
true residue claim failed there. The residue table is now `rest_p`, checked residue by residue, with `omega` used only for
the simple non-equalities feeding it.

**Proved regions of the shape space so far** (each with every runner's instant named): every complete grid's
neighbourhood (E46; E45 for the AP), the doubled-slot family (E41) and its neighbourhood (E48).

---

## E106 — 2026-09-27 — log numbering; handover v5

**Numbering collision.** Two sessions appended to this log on 2026-09-27. The entries up to E105 are one series; after
E105 the file continues with a second series whose headings read E36–E48 (from the heading "E36 — exhibit route: does the
arrangement's TYPE decide the flank?"). The file is append-only, so the headings are not changed. **Cite the second
series as E36b–E48b.** New entries continue from E106.

**Handover v5** (`docs/n8/HANDOVER_2026_09_26_v5.md`, v4 kept): carries v4 in full; adds §0, the corrections a fresh
session needs (frame, owner-right moments, session-right moments, measurement mistakes, Lean tooling); E102–E105; the
second series' results and Lean modules (§6) and how they sit against plan v2's residual route. `compile-diff` run
before promotion (below or in the next entry).

---

## E107 — 2026-09-27 — handover v5 loss check; v6; the residue-pattern count

**`compile-diff` on v5** (against v4, E102–E105, E36b–E48b, E106): nothing of v4 lost (line diff: v4 carried verbatim).
17 losses from the log summaries: open items (the ordering lemma not stated; a coarse class untested; E38b's noted type
test), caveats and scopes (E104 "these four sets", E40b "in this family", proved radii, E37b "reasoned from one trace",
E39b's overstate/miss caveats, E47b's jumps and `413ρ` outliers), grade tags dropped on E102–E104, "confirmed exactly"
over `[EMPIRICAL]` results, and one figure (E47b's `1.91ρ` given as "about `1.6ρ`"). **`HANDOVER_2026_09_26_v6.md`**
repairs every item; v5 kept.

**Residue patterns** (`LonelyRunner/experiments/nN/redo/residue_patterns_v1.{py,out}`, exact enumeration): occupancy
patterns of eight whole-number speeds in the 8 residue slots: 6,435; up to translation and mirror 440; also up to odd
rescaling (units of `ℤ/8` permute the slots) **264**, of which the complete grid is 1 and one doubled slot with one empty
is 3 (by empty slots: 0: 1, 1: 3, 2: 28, 3: 73, 4: 98, 5: 48, 6: 12, 7: 1). This counts residue patterns only; laps and
deviations are not in it.

---

## E108 — 2026-09-27 — handover v6 loss check; owner-directed review; v7

**`compile-diff` on v6** (against v5, v4, E102–E107, E36b–E48b): nothing from v4 or v5 lost; every E107 category
repaired; no retraction re-claimed. Thirteen log items missing or weakened (v5 had already dropped them): the
"relay" terminology note (E38b); E38b's recursion caveat, its "faces" (v5/v6 said "edges") and its grade
`[reasoned; each step cites a proved statement]`; E44b's `ρ = 1/64` scope and 1,091/1,600 at `ρ = 1/8`; E47b's
"(relative)"; E37b's pending decision (DoorArrives vs DoorFlank), which read as settled; E105's corrected Theorem 6.15
statement; E102's half-lap content and place test; E104's `[VERIFIED — exhaustive exact, finite window]` tag; E36b's
"Not yet examined: the lap `j`"; E102's note that the six first-series modules are imported by none. About eight
v5-origin statements had no log source and no mark. All repaired in **`HANDOVER_2026_09_26_v7.md`** (v6 kept).

**Owner-directed review of v6** (owner: *"review the handover document and especially look at training default
assumptions that are not true"*; then *"the proof does not look like other proofs because it is novel and new … reason
within the framework"*). Read: paper v9.1 in full, MANUSCRIPT_v21 §0 and §17, plan v2, `Target.lean`, `Doors.lean`,
`EndRunnerN`, `OrderEightCasesN`. Corrections carried into v7:
- v6 §0.16 listed "the proved neighbourhood radii shrink with the laps" as a negative about the object. It is a fact
  about the proved bound `2ρ(14W + 21) ≤ 1`; the actual tolerance is unmeasured (the suppression pattern: a limit of the
  proof read as a limit of the thing).
- Missing from §0: translating vs adjoining a runner (memory `feedback_count_the_runners_given_2026_09_12`); the
  Rosenfeld preprint is not the task (memory `project_n8_rosenfeld_2026_09_07`); "hard case" means the one delaying
  mechanism, not a case the cascade struggles with; the list of foreign proof shapes.
- **The neighbourhood theorems are not off the residual path** `[reasoned from the Lean statements; unchecked]`:
  `residual_of_lonelyRunnerAt8` reads a residual set as the slowest runner's readings of `(1, 1 + r₁, …, 1 + r₇)`, where
  the reading set is the arrangement up to translation, so the arrangement-level neighbourhood theorems discharge any
  residual set lying, rescaled, within a proved radius. Whether any does is untested (v7 §5.11).
- The Lean is ahead of v21: `EightResidual` has 21 fields (`no_fast_pair`, `no_block_split` added after v21's 19).

---

## E109 — 2026-09-27 — assumptions overturned (running register); handover versions stopped

Owner: *"note any assumption that gets overturned as this will help any future handover"*; *"the handover document is
repeating, we can probably stop that."* Handover versions stop at v7; the `compile-diff` run on v7 was stopped before
it reported (v7 is therefore not loss-checked). From here, overturned assumptions are logged as numbered items **O1,
O2, …** in dated entries like this one, for the next handover to collect.

- **O1. "The cascade gives the first lonely instant."** I summarised the cascade as giving *the first* lonely instant.
  Owner: it gives *a* lonely instant, which is what the conjecture asks (*"at some time"*); the first instant was never
  guaranteed by the owner and is not required. Check run: `LRC/Cascade/Iteration.lean:213` `first_isolation_of_fixed`
  does state that the fixed point is `≤` every lonely `s` (paper v9.1 Thm 11(b)), so the fact is in the tree; but it is a
  by-product of the construction, not what the cascade is for, and no proof here may lean on "first" as an obligation.
  Correct frame: the cascade arrives at a lonely instant exactly when the runner is lonely (`doors_agree`).

---

## E110 — 2026-09-27 — the lattice ladder against the cascade; its exceptions are edge pushes and slot collisions

Owner: *"when we have an exception or counter example for the proxy … use cascade to figure out what is happening …
permutating counter examples or exceptions always finds and refines the mechanism."* Proxy tested: the ladder of E4–E6
(PROOF_REQUIREMENTS_v2 §7), read in the owner's picture. At lattice `D` the instants `(8j+1)/(8D) = j/D + 1/(8D)` are a
rung plus a deviation; the readings that are multiples of `D` form a grid read by residues mod 8 and never block on a
live lattice; a reading `≡ 0 (mod 8D)` is a runner in the subject's slot, which kills the lattice. `L0` = least live
`D`. Every set of 7 distinct readings in `1..24` (slowest runner of `(c, c + d₁, …)`), exact
(`LonelyRunner/experiments/nN/redo/lattice_vs_cascade_v1`, `lattice_exceptions_v1/v2`, `lattice_then_cascade_v1`)
`[VERIFIED — exhaustive exact, readings ≤ 24]`:
- `L0 ∈ {1, 2, 3, 4}`; the first live lattice clears in 249,454 of 346,104; the least clearing lattice `D* ≤ 14`.
- The cascade's instant is a lattice instant of `D*` in only 74,684; the ladder and the cascade generally name
  different instants.
- **The 96,650 exceptions** (`L0` fails): in 96,441 one runner moved by `±1, ±2` makes the first live lattice clear,
  and the runner moved is a sole blocker of some `L0` numerator in 93,491: **an edge push by one runner**.
- **The 209 no single move rescues:** 201 have two readings `≡ 0 (mod 8)` (169 with `d_min = 1`), `L0 = 3` in 165:
  **two runners in the subject's slot at the bound**, the double collision of E103 and the owner's one hard case.
- Starting the cascade at the `L0` instants does not shorten it (1 move in 59,153 of the exceptions, up to 17). Recorded
  as a measurement only: a move count is a foreign shape (v21 §0), not pursued.

**Reading** `[my reading of the above; not a proof]`: read at the arrangement's own least live scale, the ways
isolation fails are the two the owner named: one runner at the edge of a clear slot, and runners in the subject's
slot. Each has a proved lemma in one setting: the grid nudge (`GridNudgeN`, every reading on an eighth) and the
doubled slot (`DoubledSlotN`, `DoubledNbhdN`, the AP family). What is owed is their form at a general live lattice `D`
with off-lattice readings. No overturned assumption this entry.

---

## E111 — 2026-09-27 — the offending runners moved through the cascade; the entering-edge proxy

Owner: *"The cascade is a perfect oracle … What is off is our understanding of how the oracle works … understanding
exactly the proxy seems to be our work."* Offender paths (`LonelyRunner/experiments/nN/redo/offender_paths_v1/v2`,
`edge_runner_rule_v1`), exact; offender moved by `s = i/32`, `|i| ≤ 32`; cascade from the bound at every step:
- **Double collisions** (the 201 of E110; offenders = the two readings `≡ 0 mod 8`): moving a collider over `±1` does
  not change the landing on 314 of 402 paths. The landing's setter at the bound: slot 7 in 101 (97 of them on lap 1,
  `t* = 9/(8e)`), slot 6 in 28 (27 on lap 2), a collider itself in 33. `t* = 9/(8e)` in 113 of 201. **The colliders
  decide that the isolation leaves the bound, not where it goes; the runner at the entering edge (slot 7, often exactly
  on `7/8` and so clear at the bound) sets it at its next opening** `[VERIFIED — these 201 sets]`. This is E104's law
  on 201 sets instead of 4.
- **The 8 others:** the setter at the bound is in slot 6 or 7 in all 8. Moving the slowest runner towards zero sends
  the landing's lap up (to 56): the shape approaching a face, as E38b predicts.
- **Edge pushes** (300 sampled): 315 of 549 paths keep one landing; moving the sole blocker makes it the setter on 562
  segments.
- **Proxy tested, and it fails:** "the next opening of the runner with the largest fractional reading at the bound" is
  lonely in 43,694 of the 145,368 sets whose bound is blocked (the cascade lands there in 33,392). Exceptions: one
  blocker in 66,215, most often a slot-6 runner at the bound. **Diagnosis:** the proxy picks the runner nearest the
  entering edge whether or not it is in the way; the cascade moves only on runners in the way, and the entering-edge
  runner matters only after the colliders force time forward. The proxy is wrong, not the cascade.

---

## E112 — 2026-09-27 — owner on tools; O2: the deformation argument was already the owner's, in Lean

**Owner (2026-09-27), on tools.** *"We have been wary of density, coverage, counting and other means because they have
not been natively acquired. They tend to be imports of you trying to relate what we are doing to other proofs instead
of reasoning. Now that doesn't mean we can't use any of them as tools but they must arrive organically and not just be
a this works for another frame."* This refines the 2026-09-15 ruling (*"tools are fine, targets and statements are
what must stay native"*): a tool is admissible when the framework's own reasoning arrives at it, not when it is carried
in because it works in another proof.

- **O2. The open/closed framing was presented as mine and a ruling was asked for that already existed.** In E111's
  reply I restated the owner's claim as general topology (a connected shape space; the lonely set open and closed) and
  asked whether a local bound on the instant is admissible. Check run: the argument is the owner's own (E52, from
  E18/E19: *"any arrangement moves the isolation"*), proved in Lean as `DeformationN.lonely_along_path` (2026-09-26):
  along a path of speeds from the AP, isolation that is locally stable and stays in a window `[c, T]` is present at the
  end. The window is the owner's *"bounded by the speeds of the arrangement"* (E52), so it arrived natively. The
  "connected space" wrapper was the import; the native form is **the path from the AP**. Lesson: read the log's
  treatment of a route before re-framing it (the source-first rule, applied to our own log).
- **Standing, from the Lean statement:** the path route owes exactly `lonely_along_path`'s two hypotheses along every
  path from the AP: (1) local stability, proved where the instant has margin (`lonelyAt_of_close`) and needing
  relocation where it has none (the two-pinner lemma; proved in three families: `APNeighbourhoodN`,
  `GridNeighbourhoodN`, `DoubledNbhdN`); (2) the window, bounded by the speeds, supplied so far by the box
  certificates where `d_max ≤ 15·d_min` (E52) and measured by E72 (`8·d_min·t ≤ 15`, `[VERIFIED]` for `S ≤ 24`).

---

## E113 — 2026-09-27 — the wall lemma at a simple pinch is the mirror; what the path route then owes

Owner: *"what is next with extending the reduction of proof … AP/Grid relocates the isolation point in a predictable
way that does not cannot destroy it. Two runners at one speed would destroy the isolation … two runners sharing the same
slot takes a bit of time to sort out but in a very predictable and forced way."* Source read first: E52, E69–E75
(the reduction to the wall lemma (L)), `DeformationN`, `GrandReturnN`.

**Derivation** `[reasoned in the text; pieces cited are proved; not in Lean as a whole]`:
1. **Walls are hyperplanes through the origin in the readings.** A pinch (runner `a` leaving at `+1/8` on lap `k`
   exactly as `b` enters at `−1/8` on lap `m`) is `d_b(8k + 1) = d_a(8m − 1)` (E75 item 3, in readings not ratios).
2. **The path.** Readings of the slowest runner along the straight line from the AP to a whole-number target (every
   speed positive, order kept; whole numbers suffice by `RealEightN`, the slowest runner by `EndRunnerN`). A line with
   rational ends meets a wall at a rational parameter or lies inside it. So every pinch met on the path is at a
   rational arrangement, where `GrandReturnN.lonely_mirror` holds.
3. **The mirror swaps the roles.** At a simple pinch `t0` (one runner on each edge, the rest strictly clear) of a
   whole-number set, the mirror `1 − t0` is lonely, the same two runners pinch it with roles swapped (`a` entering, `b`
   leaving), and so it lies on the same wall. `t0` opens where `d_b(8k + 1) < d_a(8m − 1)`; the mirror opens on the other
   side. So a line crossing the wall opens `t0` on one side and `1 − t0` on the other; a line inside the wall keeps the
   pinch. **At a simple pinch the wall lemma (L) is the mirror.** At the progression this is the pair law: `(1/8, 7/8)`
   and `(3/8, 5/8)` are mirror pairs (E69, `ProgressionPairN.pair_law`).
4. **Openness along the path** then holds at every lonely point of the path except where **every** lonely instant is a
   **multi pinch** (two or more runners on one edge: two runners at one place at `t0`). With margin:
   `lonelyAt_of_close`; simple pinch: item 3; at irrational parameters no wall is met except one containing the line.
5. **Closedness** is the window: if lonely then lonely at some `t ≤ T`, uniform along the path (the owner's *"bounded by
   the speeds"*, E52; measured as E72's `8·d_min·t ≤ 15`). With it the lonely parameters are open, equal to the
   window-lonely parameters, which are closed (`lonelyAt_of_limit`), and contain `s = 0`; so the whole path is lonely.

**So the path route owes two statements about single whole-number arrangements:**
- **(A)** a lonely whole-number arrangement has a lonely instant with margin or a simple pinch (not multi pinches only);
- **(B)** the window: some lonely instant is bounded by the speeds.

**Checks** (`LonelyRunner/experiments/nN/redo/pinch_types_v1`, `mirror_opening_v1`), exact:
- `[VERIFIED — exhaustive exact, readings ≤ 24]` Of 346,104 sets, **6 have no lonely interval** in `(0, 1/2]`: the three
  tight instances and three rescalings (`2·(1…7)`, `2·(1,2,3,4,5,7,12)`, `3·(1…7)`). Every one has a simple pinch.
  **Multi pinches only: 0 sets.** Controls: `1…7` and `(1,2,3,4,5,7,12)` give 2 simple pinches each, as expected.
- `[VERIFIED — 19 simple pinches × 200 integer directions × both signs]` The mirror is the same pair with roles swapped
  at all 19. On each side exactly one of `t0`, `1 − t0` opens, swapping with the sign (1,895 and 1,839 each way); the 132
  cases where neither opens as an interval are exactly the directions inside the wall (normal · direction `= 0`, 132 of
  132), where the pinch persists.

**Reading, owner's terms:** the only local way to lose the isolation along the path is two runners at one place at every
lonely instant: the owner's two-in-a-slot, at the slot edge. Two runners at one *speed* is excluded outright (a face;
injectivity). No overturned assumption this entry.

---

## E114 — 2026-09-27 — O3; PinchOpenN in Lean; openness needs no window, and the path can avoid multi pinches

**Owner:** *"Yes do this. But remember because scale is invariant and because grids are infinite expanding number will
ultimately just be repeating what is already known."* Recorded verbatim. Boundary recorded beside it (memory-drafter
found these on disk): larger ranges have turned up things smaller ones did not (the cascade length `2k+1` on
`(1, 5k−2, 5k, 10k−2)`; "lattice gap ≤ 3" withdrawn at gap 6; the `53/462` floor held to 40 only). Sets up to 24 do
repeat under rescaling (E113: three of its six fragile sets are rescalings). Taken here as: settle (A) by reasoning, not
by a larger search.

- **O3. E113's "the wall lemma at a simple pinch is the mirror" was already proved.** `Spec/TwoPinnerN.lean`
  (2026-09-25) has the mirror argument, roles swapped, for the two pinners. Check that would have caught it: grep the Lean
  tree for the route before deriving (the pre-use check's step 0, the O2 lesson again). E113's measurements stand; its
  item 3 is `TwoPinnerN`, not new.

**New in Lean: `LRC/Spec/PinchOpenN.lean`** (`LonelyRunner/` commit below; Spec gate PASS, **1,863** declarations,
axiom-clean, `experiments/nN/spec_gate_pinch_open.out`) `[PROVED — axiom-clean]`:
- `opens_at_leaving`: at a simple pinch (runner `a` on `+1/8`, `b` on `−1/8`, every other runner clear with margin
  `ε > 0`), in any direction `w` with `(w_b − w_k)(v_a − v_k) ≤ (w_a − w_k)(v_b − v_k)`, for small `r ≥ 0` the subject is
  lonely at the leaving runner's own opening `(Na + 1/8)/((v_a − v_k) + r(w_a − w_k))`. The condition does not depend
  on `r`.
- `mirror_pinch`, `right_side`, **`pinch_eventually_lonely`**: for whole-number readings, the mirror `M − t0` is a
  simple pinch with roles swapped and the others equally clear, so the other sign is covered there; with `−w` for
  `r ≤ 0`, the subject is lonely at every `r` near `0`, **both sides, any direction**. This is
  `DeformationN.lonely_along_path`'s `hopen` at a simple pinch, with the other runners' room carried (the part
  `TwoPinnerN` left set-specific).

**The path route, restructured** `[reasoned in the text; the pieces named are proved; the assembly is not in Lean]`:
1. **Openness needs no window.** With margin: `eventually_lonely_of_margin`. At a simple pinch: `pinch_eventually_lonely`
   (the mirror may lie far outside any window; openness does not care). E75 stated (L) inside the window, which is why
   the mirror did not settle it there.
2. **Closedness is the window, and only there.** `lonely_along_path`'s `hbound`: some lonely instant in `[c, T]`.
3. **Multi pinches can be avoided by the choice of path, given the window.** With every lonely instant `≤ T` and speeds
   bounded on the path, only walls with laps `≤ d_max·T` matter: finitely many. A multi pinch lies on two of them at
   once (two independent linear conditions: codimension 2 in the readings). Route the path from the AP through a
   rational point `M` in the open cone of increasing positive readings that avoids the finitely many hyperplanes
   `span(AP, W)` and `span(W, target)`: a finite union of hyperplanes does not cover an open cone. Then no interior point
   of the path is a multi pinch at an instant `≤ T`; the target itself is reached by closedness, not openness. Rational
   ends keep every wall crossing rational, so the mirror applies.
4. **So (A) is not a separate obligation; the path route owes only (B), the window:** a lonely arrangement is lonely at
   some instant bounded by its speeds, uniformly on a bounded set of arrangements with `d_min` bounded below.

Owed in Lean for the assembly: isolated lonely instant ⇒ pinch (one leaving, one entering); the finite-wall avoidance of
item 3; the path through `M`; `lonely_along_path` with `hopen` from margin or `pinch_eventually_lonely`. **(B) stays the
open content** (the owner's *"bounded by the speeds"*, E52; E72's `8·d_min·t ≤ 15`, `[VERIFIED]` for `S ≤ 24`).

---

## E115 — 2026-09-27 — `LonelyRunnerAt8` from the window, in Lean; O4

**Owner:** *"Ok so we need to do this in lean"* (the path route of E113–E114). Plan: `docs/n8/PATH_ROUTE_LEAN_PLAN_v1.md`.

**Proved** (`LonelyRunner/` commit below; Spec gate PASS, **1,892** declarations, axiom-clean,
`experiments/nN/spec_gate_path_window.out`) `[PROVED — axiom-clean, one OWED hypothesis]`:

> **`LRC.PathWindow.lonelyRunnerAt8_of_window : WindowBound → LRC.Spec.LonelyRunnerAt8`**, axioms
> `[propext, Classical.choice, Quot.sound]`.

`WindowBound` (registered **OWED** in `scripts/nN/spec_gate.sh`) is the owner's *"bounded by the speeds of the
arrangement"* (E52): for every `c > 0` and `C` there is `T` such that every arrangement whose subject readings all lie in
`[c, C]`, if lonely, is lonely at some `t ∈ (0, T]`. It quantifies over all such arrangements, including ones where two
non-subject runners share a speed (the chain below passes through such points; no lemma needs distinct speeds).

**The proof** (`Spec/PathRouteN.lean`, `Spec/PathWindowN.lean`):
- `margin_or_pinch`: at a lonely instant (positive readings) some instant has a margin, or the instant is a pinch
  (a runner on `+1/8`, a different one on `−1/8`).
- `move_one_strict`, `move_one_period`: **move one runner, the others fixed.** At a lonely instant `t1` only the moving
  runner changes position. Strictly clear: it stays clear. On an edge: one sign of the change moves it inward at `t1`;
  for the other sign, at the mirror `P − t1` (a common period `P > t1`) it is on the opposite edge and the same change
  moves it inward. Every other runner is as clear at `P − t1` as at `t1`.
- `segment_lonely`: along a segment moving runner `i`, with the other readings rational, a margin gives openness
  (`eventually_lonely_of_margin`); otherwise at a pinch a fixed runner is on an edge, so `t1` is rational, so the moving
  reading is rational, so every reading is, so a common period exists (`common_period`) and `move_one_period` applies.
  Closedness is the window. `DeformationN.lonely_along_path` carries lonely-at-start to lonely-at-end.
- `slowest_of_window`: from the AP (subject speed `v 0`, runner `j` at `v 0 + j/8`, lonely at `t = 1`) move runners
  `1, …, 7` in turn to their whole-number speeds. Readings stay in `[1/8, C]`, `C = 1 + Σ readings`. Then
  `EndRunnerN.lonelyRunnerAt8_of_slowest`.

- **O4. Walls, simple versus multi pinches, and the path-avoidance argument (E113 item 4, E114 item 3, plan P2 and P4)
  are not needed.** I carried over E75's frame, in which all runners move at once along a general path, where multi
  pinches really can close on both sides. Moving one runner at a time (the owner's *"runners are always bound by their
  neighbours"*, E71) makes every pinch benign: only the moving runner's position changes. `line_pinch_cases` (P2) is
  proved and unused by the final theorem. (A) of E113 is therefore not owed at all, not even through a choice of
  path.

**What remains for the conjecture at eight runners: `WindowBound`, and only it.** It is the statement E52 named
(*"the relocated isolation cannot escape to infinity"*), now the single hypothesis of a proved theorem. Evidence so far
is E72's `8·d_min·t ≤ 15` (`[VERIFIED]` for `S ≤ 24`, `[EMPIRICAL]` beyond), which would give `T = 15/(8c)`. Not proved.

**What `WindowBound` contains** `[reasoned in the text; not in Lean]`, recorded so the theorem is not over-read:
- It implies `LonelyRunnerAt8` (the theorem above), so it is at least as strong as the conjecture at eight runners.
- Conversely it would follow from the conjecture plus local stability at every arrangement of a box: if lonely
  arrangements `y_n` of a box had first lonely times `→ ∞`, a limit `y*` (compact box) that is lonely with a margin, or
  at a simple pinch with a common period (`pinch_eventually_lonely`), keeps its nearby arrangements lonely at bounded
  times. What could break it is a `y*` whose every lonely instant closes in the approach direction: a multi pinch
  (E113's (A) returns here, as a condition for the window, not for the reduction), or a simple pinch with no common
  period (the mirror needs one; irrational `y*`).
- The chain passes through arrangements where two runners share a speed. Those have at most seven distinct readings,
  and native order seven makes them lonely at `1/7`, strictly clear of `1/8`: a margin, so the window holds near them
  by `eventually_lonely_of_margin`-type stability `[reasoned]`.
- So the theorem puts the whole content of the conjecture into one statement, the owner's E52 *"the relocated
  isolation cannot escape to infinity"*, with the deformation argument itself now formal. The cascade's resting
  point is the earliest lonely instant (`first_isolation_of_fixed`), so `WindowBound` says exactly that the cascade
  rests by a time bounded by the speeds on each box. This uses the first-instant property as a tool for the window, not
  as an obligation of the conjecture (O1 stands).

---

## E116 — 2026-09-27 — what one move contains: the continuum is settled by order seven; the window is the whole-number points; O5

**Owner:** *"now the only thing to do is for you to actually do the work, encounter the problems and see realise if
there are any default assumptions you still have to work through."* Starting point: E115 and its addendum; a review of
the Lean (this session) observed that `slowest_of_window` applies the window only along its seven moves, each with six
readings fixed and rational (whole numbers or `j/8`) and one reading varying.

**Proved** (`LonelyRunner/LonelyRunner/LRC/Spec/OneFreeN.lean`, axiom-clean, `lake env lean` clean; Spec gate below)
`[PROVED — axiom-clean]`:

> **`LRC.OneFree.lonely_of_one_free_eight`.** Six readings `v j − v k` (`j ≠ i`) with a common period `P > 0`
> (every `(v j − v k)·P` whole), all readings positive, and the seventh **off the lattice** (`(v i − v k)·P` not whole):
> the subject is lonely, at `t₇ + m·P`, where native order seven clears the six at `1/7` at `t₇`
> (`existenceAtN_seven`) and `m` is written down (`exists_far_multiple`: one step if `‖α‖ ≥ 1/4`, else
> `⌈1/(4‖α‖)⌉` steps, `α = (v i − v k)·P`). No density, no measure.

This is R7's mechanism (paper v9.1 §10.6, `IrrationalN.lonely_of_one_free`, which there needs at most three other
readings) at order eight, with order seven supplying the six.

**Checks** (`LonelyRunner/experiments/nN/redo/move_window_v1.{py,out}`, exact):
- `[VERIFIED — 2,587 random cases]` the lemma's instant `t₇ + mP`, `m ≤ ⌈1/(4‖α‖)⌉`, is lonely: 0 failures.
- `[VERIFIED — one family, exact]` **the escape, with a positive control.** Reading 7 of `(1,…,7)` moved to `7 + ε`: at
  threshold `1/8` (the endpoint lonely) the first lonely time is `3/8` for every `ε = 10⁻¹…10⁻⁴`; at threshold
  `1/8 + 1/1000` (the endpoint **not** lonely) it is `0.874, 0.874, 8.87, 80.9`, growing like `1/ε`.

**What a move contains** `[reasoned in the text; the pieces cited are proved]`:
1. Along a move, every arrangement off the lattice `x ∈ (1/P)ℤ` of the moving reading is lonely (the lemma). What is
   left are the **lattice points**, where every reading is a whole multiple of `1/P`: whole-number arrangements after
   rescaling. On moves 1–6 they are hybrids (whole-number runners `8·D_j`, AP runners `j`, the mover at `8x`); on move 7
   the lattice is `gℤ`, `g` the gcd of the six fixed readings, and **the target itself is a lattice point**.
2. At a lattice point `X`: if `X` is lonely, nearby points are lonely at bounded times (`move_one_strict`,
   `move_one_period`, `eventually_lonely_of_margin`, all at `X`'s own instant or its mirror). If `X` is not lonely,
   nearby points are lonely only at times that escape to infinity (`lonelyAt_of_limit`, contrapositive; the control
   above shows the `1/ε` rate). **So the window at a lattice point is exactly that point's loneliness.**
3. Hence, move by move: the window along the move ⇔ every lattice point on it is lonely (⇒: `segment_lonely` on the
   sub-segment `[0, s]`; ⇐: every point then lonely, locally bounded, and finitely many neighbourhoods cover `[0, 1]`;
   not in Lean). The failure modes E115's addendum named for `WindowBound` (a multi pinch only; a pinch with no common
   period) do not arise on a move: at a pinch one pinner is fixed, so the instant is rational and a period exists
   (`segment_lonely`, as proved).
4. **So the path route owes exactly the whole-number conjecture at the lattice points of its moves, the target among
   them.** That is the statement plan v2 already reduces to (`lonelyRunnerAt8_iff_residual`): the path route and the
   residual route owe the same thing. What the path route adds is a native, one-runner proof that everything between
   whole-number points is lonely.

**Consequences for earlier entries.**
- E115's "What remains … `WindowBound`, and only it" holds, and `WindowBound` restricted to the moves is equivalent to
  the whole-number conjecture; it is not a separate analytic fact about escape. E52's *"the relocated isolation cannot
  escape to infinity"* is, on a move, exactly *"no whole-number arrangement on it fails"*.
- The §6 neighbourhood theorems return to the path in whole-number form: they discharge lattice points near an AP,
  grid or doubled-slot shape at some scale. With zero deviation, `grid_nbhd_exists` is a case of R6 at `q = 8` (a
  complete residue system mod 8 is lonely at `1/8`). R6 at `q = 8` settles more: every lattice point whose subject
  readings avoid `0 mod 8`. So a lattice point not settled at `1/8` has a runner in the subject's own class mod 8
  (`EightResidual`'s `eight` field; handover v7 §0.11, the one mechanism that delays the isolation).
- The discrete form of the deformation is **one runner moved by one lattice unit** between whole-number arrangements,
  which is what E103, E110 and E111 did with the cascade (moves of `±1, ±2`). A unit step moves the runner's position
  at `X`'s instant `t*` by `t*/P`, small against a slot exactly when the scale (`d_min`) is large: the owner's
  *"deviation forced by d_min"*.

- **O5. "The deformation carries isolation to the target through the continuum."** E113–E115 treated the path from the
  AP as doing work between whole-number arrangements, with the window as the one thing owed about it. Check run (this
  entry): on every move the continuum is lonely by order seven plus one free reading, and the window is exactly
  loneliness at the whole-number points, the target included. The continuum carries nothing across a whole-number
  point: arriving at a non-lonely one, the instants escape like `1/ε`. Where the work is: the whole-number arrangements,
  as in plan v2.

---

## E117 — 2026-09-27 — the owed sets read as AP/grid plus deviation; one free reading as a case; O6

**Owner:** *"go ahead with the whole-number slot points through the cascade. Remember our target is to prove n=8 or
reduce the proof that is required."* Then, mid-run: *"AP and grid provide global isolation, such that any arrangement
can be viewed in relation to this global isolation. Every arrangement is actually a smaller set than it looks because of
the ordering and the fact AP is scale invariant and grid positions are infinite. Once the arrangements are categorised,
you find that any of these arrangements provides from AP/grid plus a deviation. Meaning any arrangement just relocates
the isolation event. For isolation not to occur you have to break the conjecture about every speed being different. What
I think we will find is that as we start to compile these different arrangements that the rules actually simplify, but
we need to get to a position where the reduced real different arrangements are proved first. AP scale invariance
subsumes a lot and the fact any multiple of 8 outside of AP is still captured by grid means there is no escape for
arrangements."*

- **O6. `OneFreeN.exists_clear_step` duplicated `Flanks.exists_clear_step`** (the mover ladder's rung `m = 1`, v21
  §6.11). The pre-use grep (O2, O3) was skipped again. What E116's theorem adds is only that order seven clears the six
  fixed readings, in place of divisibility at a flank. The whole-number module below uses the existing lemma.

**Proved** (`LonelyRunner/` commit below; Spec gate PASS **1,899**, `experiments/nN/spec_gate_one_free_field.out`)
`[PROVED — axiom-clean]`: `OneFreeEightN.lonely_eight_of_one_free`: six readings sharing a factor `g ≥ 2` that the
seventh lacks are lonely (order seven on the six at `t₇`, then `t₇ + k/g`, one step by `Flanks.exists_clear_step`).
It generalises halving. **`EightResidual` gains a 22nd field, `no_one_free`**, with its case in
`lonely_eight_or_residual`; `lonelyRunnerAt8_iff_residual` is unchanged. Reach `[VERIFIED — exhaustive exact,
[1,30]]` (`one_free_reach_v1.out`): among the 200,952 sets passing the arithmetic fields, it settles 16,047 (`g = 2`
15,273, `g = 3` 760, `g = 4` 14). No `[1,30]` set is residual in any case; this is an infinite family closed by one
lemma, not a count of progress.

**The owed sets, through the cascade** (`experiments/nN/residual_members_v5.{py,out}`, v4's construction with the three
newer fields added; exact) `[VERIFIED — these 47 constructed members]`:
- Members with **all 22 fields** exist: 47 of 400 constructions. The largest reading is a multiple of `8·lcm(1…64)`, so
  it sits exactly on the subject at every instant of every lattice `D ≤ 64`; the least live lattice is `L0 = 67`. Their
  spread is 7.1–8.9, which excludes `FastPair8` (needs `9c ≤ a`) and `BlockSplit8` (needs `g ≥ 28c`) outright.
- **Read at `L0`** the grid part (multiples of 67) is empty in 42 of 47: the lattice reading is all deviation and names
  no structure. `L0` clears at 4–14 of its 67 instants.
- **Read at their own AP scale `d_min`** they are one category: the largest runner lapped once into the subject's slot at
  the bound (47 of 47). The cascade relocates the isolation to a **middle reading's second opening** `9/(8e)` in 44, and
  to lap 2 in 3 (flank the largest in 2), `R* ≤ 2.13`, 1–5 moves.

**The category, exhaustively** (`experiments/nN/redo/collision_band_v1.{py,out}`) `[VERIFIED — exhaustive exact,
readings ≤ 40]`: every 7-set with `7·d_min < d_max < 9·d_min` (1,717,540 sets). The bound is blocked in all (the largest
sits in `(7/8, 9/8)` there). The least lap `K` with some reading's opening `(8K+1)/(8e)` lonely: 1 in 1,644,119;
2 in 71,233; 3 in 2,101; 4 in 85; 5 in 1; 6 in 1. The cascade lands at that least lap or later.

**Reading, in the owner's terms** `[my reading; not a proof]`:
- The owner's "any multiple of 8 outside of AP is still captured by grid" is, in lattice terms, the least live lattice:
  no reading is `≡ 0 (mod 8D)` for every `D`, so the subject's slot is empty at some least `D`. The constructed members
  are the extreme case (in the slot at every lattice up to 64).
- But the categorisation that simplifies is the AP scale, not `L0`: every owed set known is the AP at scale `d_min`
  with its fastest runner lapped into the subject's slot, and its isolation relocates to the first later runner-scale
  with room. That is Case B's first band; handover v7 §3 step 6 grades Case B `[VERIFIED — exact certificates, event by
  R = 15; positive control covers S ≤ 9]`, Lean owed.
- No Case C residual member is known (plan v2 §4). **Next:** attempt Case C residual members by construction (a slow core
  below a six-reading cluster with no common factor, no fast pair, no block split, no one free reading). If none exists,
  the structural reason is the next case; if they exist, their cascade is the next category.

---

## E118 — 2026-09-27 — Case C has owed sets; both known categories relocate within the first window

**Case C residual members exist** (`LonelyRunner/experiments/nN/residual_members_C_v1.{py,out}`; the field predicates
factored into `residual_fields_v1.py`; exact) `[VERIFIED — these constructed members, all 22 fields]`. Plan v2 §4 said
none was known. With a collider `L·u` (`L = 8·lcm(1…64)`) as the least reading and six readings hill-climbed in
`[25·d_min, 175·d_min]`: 297 of 300 constructions pass every field. With the collider inside the fast cluster: 250 of
300. Shape: **one slow runner below a six-reading cluster** (the cluster's own spread `≤ 7` in 492 of 547; four have a
2/5 split).

**Through the cascade:** every one is isolated with `R* ≤ 1.377`, inside the slow runner's first window
(`8·d_min·t ≤ 7`), the flank a cluster member in 546 of 547.

**The adversarial shape tested** (`experiments/nN/redo/cluster_drift_v1.{py,out}`) `[VERIFIED — these 4,110 sets]`: a
near-lattice cluster `c·(1…6)` with one member moved by `±1, ±2, 3` (grid plus deviation), a slow runner below with
spread `> 24`, `c = 40, 120, 400`. `R* > 7`: 0; the largest `R* = 1.463`. My expectation that the drifting member would
block the cluster for long stretches was wrong: read as an AP at its own scale, the cluster has `φ(8)` global instants
per period, and one deviating member does not block all of them (the owner's *"AP scale invariance subsumes a lot"*).

**The two categories of owed sets now known, at the AP scale** `[my reading; each backed by the measurements named]`:
- **B1:** the AP at scale `d_min` with the fastest runner lapped once into the subject's slot (spread 7–9). Relocates to
  a middle reading's second opening `9/(8e)` (E117: 44 of 47; exhaustive to 40, least lap 1 in 95.7%, at most 6).
- **C1:** a slow runner below a fast cluster, the cluster an R1 group at its own scale. Relocates within the slow runner's
  first window (`R* ≤ 1.46` on 4,657 sets here; E73's adversarial climbs `R ≤ 6.42`).

What a proof of C1 needs, in the framework's own terms: the fast cluster's instants (the flank openings of an R1 group,
or its `φ(8)` class instants when it is near an AP) meet the slow runner's first window. `FastPair8` (a pair: every
window of length `3/(4a)` holds a joint clear point) and `BlockSplit8` (a common factor `g`) are the two cases of this
already proved; C1 is the same statement for a group of up to six with no common factor. Not proved.

---

## E119 — 2026-09-27 — the two systems as one comb; the band 7–9 derived to a remainder; block rules in Lean

**Owner** (in sequence): *"We enumerated Case B to something like 24 but it is actually unnecessary. Because it's trying
to enumerate scale invariance rather than logically deriving the two systems at play, AP which is scale invariant and
Grid which is infinite."* — *"Please remember to think and reason this through, not just look for similar looking
answers."* — *"If you have an unanswered question, cascade provides the answer."* — *"Please prove as much as possible in
lean right away."* — *"Are you trying to fit it into another frame rather than reason?"* (answered: yes, the plan to add
the rule as a 23rd `EightResidual` field was the plan-v2 reflex; not done) — *"We have the case b enumerated up to 24.
So we know that is true, we just need to provide that analytically so you don't need thousands of certificates."*

**The frame** `[reasoned]`: in log coordinates `x = log d`, `ρ = log(8t)`, reading `d` is clear iff `x + ρ` lies in
`F = [0, log 7] ∪ ⋃_{k≥1} [log(8k+1), log(8k+7)]`, the logarithm of the grid's clear set `[1,7] + 8ℤ`. Changing the
instant is a rigid shift (the AP's scale invariance); `F`'s gaps `G_k = (log(8k−1), log(8k+1))`, widths `log(9/7)`,
`log(17/15)`, `log(25/23)`, …, are the subject's slot on every lap (the grid is infinite). So the slowest runner is
lonely iff its seven ordered log-readings can be shifted into `F`, and **the cascade is this comb sliding**: each move
pushes the points inside a window past its upper edge; its landing is the least shift.

**Proved** (`LonelyRunner/LonelyRunner/LRC/Spec/TwoBlockN.lean`, commit `0e1eaf9`, Spec gate PASS **1,904**,
`experiments/nN/spec_gate_two_block.out`) `[PROVED — axiom-clean]`:
- `lonely_eight_of_blocks`: at the scale `e/(8K+1)`, if every reading's position `(8K+1)d/e` lies in a block
  `[8k+1, 8k+7]`, lonely at `(8K+1)/(8e)`; `e` need not be a reading. `lonely_eight_of_two_block` (`K = 1`, blocks 0, 1)
  and `lonely_eight_of_three_block` (`K = 2`, blocks 0, 1, 2) are its cases.
- `exists_big_gap`: seven readings spanning more than a factor 7 have a consecutive ratio at least `9/7` (`(9/7)⁶ < 7`).
- `b1_remainder`: in the band `7·d₁ < d₇ < 9·d₁` (the fastest runner lapped into the subject's slot at the AP scale), if
  no reading carries a two-block instant, the top four readings are dense (consecutive ratios below `9/7`).

**Checks** (exact): the two-block rule is sound on every band set to 30 (`b1_gap_rule_check_v1.out`: 167,864 of
182,104 covered, 0 unsound). The remainder through the cascade (`b1_remainder_cascade_v1.out`, 128,741 sets to 40):
the lap-1 window walks down the dense top block one reading per move, stops at the big gap, and the lap-2 window then
reaches the top reading, which lands at its lap-2 opening (position 17): the most common landing is lap blocks
`0011112` with the flank at lap 2. **Fixed-rank rules do not cover the band** (`b1_rule_cover_v1.out`): a greedy cover by
`(rank, lap)` needs 13 pairs and leaves 989 of 1,717,540 sets; the flank must be chosen by gap structure, as the cascade
does.

**What the analytic proof of Case B is, stated this way** `[reasoned; open]`: for spread at most 24, the comb's windows
can be brought to rest in gaps of the readings simultaneously. In the band 7–9 the first node is proved (two-block, or a
dense top four with a big gap below); the next is the remainder, where `W₁` rests in the big gap and `W₂` (width
`log(17/15)`) must rest in a gap of the dense top block.

---

## E120 — 2026-09-27 — loneliness is pairwise in the laps; the band's categories are grid placements

**Owner:** *"I think we can prove this if we try. go ahead, prove the remainder in lean."* — *"Remember the flank is a
proxy for what the cascade actually does. The cascade points directly to the isolation point … if the flank fails or any
other parts fail the cascade still shows the isolation point, which means the description of the proxy is wrong because
the cascade ALWAYS works."* — commit locally, no push needed.

**Proved** (`TwoBlockN.lonely_eight_of_pairwise_laps`, commit `69d0933`, Spec gate PASS **1,905**,
`experiments/nN/spec_gate_pairwise_laps.out`) `[PROVED — axiom-clean]`: give each reading `d` a lap `k d`; its clear
interval of `R = 8t` is `[(8k+1)/d, (8k+7)/d]`. If every two meet, all meet (one-dimensional Helly), at the largest left
end: lonely there. **No flank is chosen**: the reading attaining the largest left end is the flank after the fact. The
cascade's landing is exactly this largest left end for its lap assignment.

**Measured** (exact; `experiments/nN/redo/`):
- `b1_remainder_extremes_v1`: the band remainder's longest cascades (18 moves) push each reading at most once per lap,
  window after window; the slowest runner never leaves its first block.
- `b1_lap_vectors_v1`: landing lap assignments across all 1,717,540 band sets to 40: **52**, all monotone, `k₀ = 0`,
  `R* ≤ 6.447`. `b1_late_probe_v1`: no band cascade passes `R = 7` (20,000 random sets, `d₁ ≤ 400`; hill-climb max 6.025).
- `b1_lap_vector_growth_v1`: lap assignments to 20, 24, 30, 36, 40: 20, 37, 43, 49, 52; 40,000 random finer shapes
  (`d₁` up to 2,000) add **0**. `[VERIFIED — these populations; saturation not proved]`

**Reading** `[reasoned]`: the owner's categorisation of arrangements, in the band, is by **lap assignment** (the grid
placement of the ordered readings): about 52 categories, each settled by one pairwise lemma (a handful of linear
inequalities on ratios). **What remains for the band is that the categories exhaust it**: some monotone lap assignment
with `k₀ = 0` is pairwise compatible, equivalently some `R ∈ [1, 7]` is clear. Not proved. Routes considered and why
each stalls, recorded so they are not re-derived: a single-interval survival invariant (adding readings slowest-first)
loses a factor per reading and needs consecutive ratios near 3; counting blocked measure exceeds the window (each reading
blocks about a quarter); fixed-flank families fail on dense top blocks (a reading close to the top blocks runs of the
top's openings). The one that follows the cascade itself: its pushes form a finite state machine over monotone lap
assignments (laps ≤ 7 while `R < 7`), each transition a linear condition; exhausting the band is then that every path
ends in a compatible assignment before `k₀` moves.

---

## E121 — 2026-09-27 — O7: the band's cascade does pass 7; the supremum and its anatomy; enumerative routes measured

**Owner:** *"use the cascade to find why the pushes stop before 7 … This is eminently answerable … work autonomously …
remember we have an oracle that perfectly isolates every arrangement, all we need to do is figure out the mechanism."*
(Owner away for a few hours; work below is autonomous.)

- **O7. "In the band the slowest runner never leaves its first block" was range-forced.** E120 took it from readings
  `≤ 40` (`R* ≤ 6.447`), 20,000 random sets with `d₁ ≤ 400`, and a weak hill-climb (6.03). A local search on fine shapes
  (`band_extremal_v1/v2`, `d₁ = 2520, 27720`) finds `R* = 11.966`, confirmed by an independent scan of every opening
  (`band_late_trace_v1.out`). The trap handover v7 §4.6 records (E93/E94), again. The target for the band is therefore
  lonely at some `R ∈ [1, 7] ∪ [9, 15]`, not `[1, 7]`.

**The supremum** `[EMPIRICAL — 64 climbs, fine scale]` (`band_extremal_v2.out`): all climbs converge to `R* ≈ 11.966`
at one shape, readings/`d₁ ≈ (1, 2.35, 3.24, 4.1886, 5.2223, 5.7871, 7.4378)`, readings 4–7 pinned, 2–3 free. None
exceeds 15, consistent with Case B's certificates (event by `R = 15`, handover v7 §3 step 6).

**Anatomy** (`band_sup_anatomy_v1.out`, exact): at the rounded supremum shape the lonely set in `[1, 16]` is
`{6.3191} ∪ [11.966, 12.033] ∪ [12.650, 12.773] ∪ [13.042, 13.131] ∪ [14.117, 14.501]`: the first lonely instant is a
**single point**, a simple pinch (reading 4 on the leaving edge at 1.0, reading 6 on the entering edge at 7.0). Moving
one reading by `±0.005` either opens it (`R*` → 1.21 or 5.24) or kills it (`R*` → 9, or ≈ 12). **A late event is the far
side of a wall**: in the owner's terms, class 7's relocated isolation (the AP's global instant `R = 7`, pinch pair
{1, 7} for the undeviated AP, here displaced to 6.32 with other pinchers) dies at a pinch, and the isolation jumps to the
next class that survives (near 11–13, the {3, 5} pair's classes on the slowest runner's second lap).

**Enumerative routes measured, and why they are not the proof** (exact):
- The AP's own class instants, readings matched to AP positions by rank (`band_ap_classes_v1.out`): compatible for
  311,198 of 1,717,540 band sets (classes 3, 5, 7) and for none of the late extremal shapes. The reference must be chosen
  per arrangement (a grid at the arrangement's own scale and laps), which is what a landing lap assignment is.
- Distinct cascade push sequences in the band (`band_push_paths_v1.out`): 454, 1,242, 2,141 to 24, 32, 40, still
  growing; 19 new in 20,000 fine shapes. Following the cascade path by path reproduces the certificate count.

**What the mechanism must be, stated precisely** `[reasoned]`: not a list of paths or cells but an invariant of the
relocation: when a class's isolation dies at a pinch (a wall), some other class's isolation exists within the slowest
runner's first two blocks. The pinch-level facts proved so far (`PinchOpenN`: both sides open at a simple pinch, one
side by the mirror) put the other side at the mirror `P − t₀`, which is far; the band's data put it within `R ≤ 12`.
What bounds the jump is the open question, now located at a single wall.

---

## E122 — 2026-09-27 — the cascade read literally: a walk through the union of windows; the band as two copies

**Owner** (mid-run): *"I wonder if you are treating the mechanism as if it exists in a recognisable shape and then finding
it doesn't and then trying to change the shape, rather than let the cascade teach how it works and actually follow … The
training data is what muddles the water."* Recorded; the reading below starts from the cascade's definition only.

**What the cascade is, literally** `[reasoned from the definition]`: every reading `s` blocks the open windows
`((8k−1)/s, (8k+1)/s)` of `R = 8·d_min·t`, width `2/s`, period `8/s`. A move goes to the right end of the latest-ending
window containing the current `R`. So the cascade walks right from `R = 1` through the **union of all windows** and stops
at its first uncovered point. Everything about where isolation lands is the structure of that union: a chain of
overlapping windows, broken for the first time at the landing.

**In the band** (`7 < s₇ < 9` in units of `d_min`): the slowest runner's own window `(7, 9)` splits the range; the other
six readings' windows must cover **copy 0** `[1, 7]` entirely, and then **copy 1** `[9, 15]` entirely, for the landing to
pass 15. From copy 0 to copy 1 every runner's window lattice slides by the fraction `{sᵢ}` of its own period
(`R + 8` shifts runner `i` by `8sᵢ ≡ 8{sᵢ}`); the slowest runner does not slide.

**Tested, exact** (`experiments/nN/redo/band_two_copies_v1.out`, `band_top_gaps_v1.out`):
- Every band set to 40 has an uncovered point in copy 0 (1,717,540 of 1,717,540); the late fine shapes need copy 1.
- The top's deviation `ε = s₇ − 7` opens `G_m = [7(8m−1)/s₇, 8m−1]` just before the slowest runner's windows (length
  `(8m−1)ε/s₇`); at the supremum shape the copy-1 component starts exactly at `105/s₇`. **But the other readings cover
  both `G₁` and `G₂` in 69,479 band sets to 40 and 1,821 of 20,000 fine shapes**, which are isolated elsewhere: the
  top's gaps are one source of gaps, not the mechanism.

**The question the cascade poses** `[open]`: why a cover of copy 0 by the six readings' window lattices cannot survive the
slides `{sᵢ}` into a cover of copy 1. The measure of the windows does not forbid it (about `1.5` per reading on a length
of 6), so the obstruction is in the arithmetic of the slides. An isolated agent was given the bare statement (lonely at
some `R ∈ [1, 15]` in the band) at the same time; its report is recorded when it arrives.

---

## E123 — 2026-09-27 — the band 7–9 settled by an exact certificate; walls, not boxes, are its natural cells

**Isolated agent** (given only the bare statement, the proved facts and the test shapes; none of this session's framing)
returned a computer-assisted proof. Files moved from scratch to `LonelyRunner/experiments/nN/band_cert_v1/`.

> **Band theorem.** For `1 = s₀ ≤ s₁ ≤ … ≤ s₆` with `7 ≤ s₆ ≤ 9` (readings in units of `d_min`), some
> `R ∈ [1, 7] ∪ [9, 15]` has `(sᵢ·R) mod 8 ∈ [1, 7]` for every `i`. `[VERIFIED — computer-assisted, exact]`

- **Method:** a nested tiling of `(s₂, …, s₆)` into closed boxes (64 top cells, 279,871 cells, 223,719 leaves). Down each
  chain the set of `R` clear for every speed in every box is carried (box robustness: `R ∈ [(8k+1)/a, (8k+7)/b]` is clear
  for all `x ∈ [a, b]`); at each leaf an exact interval rule settles `s₁`. No measure or density argument.
- **Checks:** the agent's `verify.py` re-run by the main session: ALL VERIFIED (`verify_rerun_main_session.out`);
  corrupted certificates (upper end 9, upper end 14, a deleted cell, a collapsed node) rejected. **Independent
  re-implementation owed by the report, discharged here**: `verify_independent_v1.py` (no shared code; checks that the
  good set of `s₁` covers `[1, b₂]` instead of that the bad set is empty) PASSED on the same 279,871 cells and rejects the
  `R ≤ 14` corruption at the same leaf. SHA-256 of `cert15.pkl`: `2732d5b3…dffdb27` (`SHA256SUMS`).
- **Shape checks** (exact): 1,717,540 integer band sets to 40, 50,000 random fine shapes, 2,008 extremal and perturbed
  shapes, 300 adversarial climbs: every certificate witness clear, every least clear `R ≤ 15`.
- **The constant:** an exact shape has least clear `R = 89/s₆ ≈ 11.9659`, so the band's constant lies in
  `[11.9659, 15]`. Boxes cannot reach `R ≤ 14` at the widths tried: they fail along the walls
  `(8k+7)/sᵢ = (8k'+1)/sⱼ`, where the working instant shrinks to a point.

**Standing** `[my reading]`: this is the kind of certificate the owner said should not be needed (E119: *"provide that
analytically so you don't need thousands of certificates"*). It closes the band as a verified statement, independent of
Case B's earlier certificates, and it is not the analytic proof. What it teaches for the analytic route: the natural cells
are bounded by the walls `(8k+7)/sᵢ = (8k'+1)/sⱼ`, which are exactly the pairwise conditions of
`TwoBlockN.lonely_eight_of_pairwise_laps`. Cells cut along walls are the lap-assignment categories (E120: about 52 in the
band to 40), not boxes; axis-aligned boxes straddle walls and pay for it in count.

---

## E124 — 2026-09-27 — the band covered by 105 categories, cut only along walls, with certificates

Following E123's lesson (the natural cells are bounded by the walls `(8k+7)/sᵢ = (8k'+1)/sⱼ`, the pairwise conditions of
`lonely_eight_of_pairwise_laps`), the band was covered by **lap-assignment cones** instead of boxes. A cone `C(k)` is
`{(8kᵢ+1)·sⱼ ≤ (8kⱼ+7)·sᵢ for all i ≠ j}` (`s₀ = 1`); every shape in it is lonely at `R = maxᵢ (8kᵢ+1)/sᵢ`, inside the
slowest runner's block `k₀`.

**Result** `[VERIFIED — exact, certified, independently checked]` (`LonelyRunner/experiments/nN/redo/`):
> Every `1 = s₀ ≤ s₁ ≤ … ≤ s₆` with `7 ≤ s₆ ≤ 9` lies in one of **105** cones `C(k)` with `k₀ ∈ {0, 1}`; hence lonely at
> some `R ∈ [1, 7] ∪ [9, 15]`.
- **Method:** recursive subtraction from the band polytope, **cut only along cone walls** (never along axes); each piece
  ends inside a cone or empty. 7,019 nodes: 3,121 cuts, 2,766 cone leaves, 1,132 empty leaves
  (`band_cover_gen_v3.{py,out}`, tree `band_cover_tree_v3.json.gz`, SHA-256 in `band_cover_tree_v3.SHA256`).
- **Certificates:** every wall left uncut at a node carries Farkas multipliers showing it holds on the piece; every empty
  leaf carries an emptiness certificate (strict walls handled by a common slack). Produced by an exact dictionary simplex
  (`exact_lp.py`; cross-checked against HiGHS on 2,000 random LPs, 0 mismatches; `sympy`'s `lpmax` was found to return
  infeasible points on 2 of 300 and is not used).
- **Independent check:** `band_cover_check_v3.py` imports no LP or generator code, rebuilds every piece from the root and
  verifies every certificate by exact arithmetic: **CHECK PASSED**, 7,019 of 7,019 nodes. Negative controls (a deleted
  leaf, a cone lap changed by one, a halved multiplier, an empty leaf relabelled as a cone leaf): all rejected.
- **A first version did not terminate** (`band_cone_cover_exact_v1`, 93,169 cuts and growing): reversed walls taken
  closed left flat slabs on the walls themselves (`band_cone_cover_diag_v1.out`: 327 of 600 frontier pieces with no
  interior), re-cut forever. Taking the reversed wall strict (points on a wall belong to the closed cone) fixed it.

**Standing** `[my reading]`: the band is now settled twice by exact computation, independently: boxes (E123, 279,871
cells) and walls (here, 7,019 nodes). The wall version is organised by the owner's categories: **105 grid placements**,
each one linear rule proved in Lean. That the 105 exhaust the band is still shown by computation, not by an argument;
the categories are the rules, and the tree is the bookkeeping of their exhaustion. Lean: each leaf is either membership in
a cone (the pairwise theorem) or linear infeasibility (a linear combination with the recorded multipliers), so the tree
translates mechanically; not yet done (size: about 7,000 nodes of certificate arithmetic).

---

## E125 — 2026-09-27 — why the categories exhaust: what the cascade's chain says, and what it does not yet say

**Owner:** *"use the cascade to find why the categories exhaust, not enumeration."* The strip runs (E124's method on
spread 9–13) were stopped. Recorded before stopping: strips `[9,10]`, `[10,11]`, `[11,12]` covered and independently
checked (131, 168, 255 categories; 6,611, 8,171, 13,194 nodes), `[12,13]` generated (308 categories), not checked. The
category count grows with the spread (fast readings wrap more laps).

**The cascade as a chain** `[reasoned from the definition]`: the landing fails to occur before `R` exactly when the open
windows `((8k−1)/sᵢ, (8k+1)/sᵢ)` chain across `[1, R]`: each window overlaps the next. A junction from runner `a`'s window
`k` to runner `b`'s window `l` requires `s_b/s_a > (8l−1)/(8k+1)`. Multiplying along the chain between two consecutive
windows of one runner `a` (laps `k`, `k+1`): `(8k+7)/(8k+1) < ∏ (8lₜ+1)/(8lₜ−1)` over the windows bridging it, i.e. in
log `R` the bridging windows' log-widths `log((8l+1)/(8l−1)) ≈ 1/(4l)` must exceed the gap's log-length, with overlaps.
This is E119's comb, now derived from the cascade itself. A budget count does not forbid a cover: each runner supplies
roughly 0.7–1.0 of log-measure over `[1, 15]` against about 2.7. The obstruction lives in the junction conditions (the
overlaps), not in the totals.

**Tested, and not the mechanism by themselves** (exact):
- **Mirror orientation of the breaking pair** (`chain_junctions_v1.out`, 250 late shapes): the pair breaking the chain at
  the landing had passed the chain in the opposite orientation in 101, both orientations in 57, the same in 21, never in
  71. The pair law's contradiction needs the two thresholds to come from one resonance (the AP's exact mirror laps); at
  other laps the orientations are independent conditions.
- **The cover's refutations** (`cover_certificate_anatomy_v1.out`, `cover_certificate_cycles_v1.out`): the 1,132 empty
  pieces are refuted by combinations of 2–7 rows, mostly walls spread over all runner pairs; 297 are cycles among runners
  1–6, 164 cycles or paths through the fixed runner or the range of `s₇`, 671 branch. The certificates are basic LP
  solutions depending on the arbitrary cutting order, so their shape is not canonical and is not read as the mechanism.

**What is established, and what is not** `[my reading]`: the band is exhausted by 105 categories (E124, exact); the reason
has the form of junction conditions around the chain, each a ratio bound, whose conjunction across both copies is
inconsistent; for the AP the conjunction is exactly tight (windows touch) and the pair law is its two-runner case. A
short argument for the inconsistency in general has not been found; stated as the open step: *no set of ratio bounds of
junction type can chain both copies `[1, 7]` and `[9, 15]` when the spread is below 9*.

---

## E126 — 2026-09-27 — nested blocks: a derivation for separated readings; what Case B's derivation must add

**Owner:** *"We can enumerate stuff but honestly it often is needed if we think and reason about it. We have for case B
up to 24 and nothing escapes. But we can replace those certs by deriving why that always happens."*

**Proved** (`Spec/NestedBlocksN.lean`, commits `c46405e`, `8822784`; Spec gate PASS **1,910**,
`experiments/nN/spec_gate_nested_blocks.out`) `[PROVED — axiom-clean]`:
- `exists_block_in`: an interval of time of length `L` with `8d·L ≥ 14` contains a whole clear block of reading `d`
  (one period and one block).
- `nested_clear`: readings with each at least `7/3` of the one before have a common clear instant: nest blocks from the
  slowest runner up; the last block is clear for all. A derivation, no search.
- Process note: the first gate run FAILED on the OWED register (`InBlock`, a Prop-valued def, unregistered) after the
  module had been committed with "axiom-clean" in its message; `InBlock` was then registered as ROUTE
  (`clear_of_inBlock` proves it sufficient) and the gate re-run: PASS. The commit message preceded the gate; recorded
  so the order is fixed next time (gate, then commit).

**The worst-phase version, reasoned (not yet in Lean):** an interval of length `ℓ` meeting at most one window of `d'`
leaves a piece of length at least `min(6u', (ℓ − 2u')/2)` inside one block (`u' = 1/(8d')`); if it meets two windows it
contains the block between them. In units `λ = ℓ/u`: `λ' = min(6, (λρ − 2)/2)` for a ratio step `ρ`, from `λ₀ = 6`.
With every consecutive ratio at least 2 the pieces survive all six steps (`6, 5, 4, 3, 2, 1, 0`). Dense readings kill
the worst-phase bound within two steps: **Case B cannot be derived phase-free**; its derivation has to use the actual
phases, which is what the cascade's junction conditions (E125) carry.

**Where the derivation of Case B has to act** `[reasoned]`: separated readings nest (above). Dense readings share
windows at low laps (the cascade pushes them together; E92's crowds); a crowd of spread `ρ` has common clear blocks
exactly on laps `k` with `ρ ≤ (8k+7)/(8k+1)`, of length `((8k+7) − (8k+1)ρ)/(8M)`. So the derivation's objects are
crowds (effective runners, valid up to a lap set by their spread) nested by gaps: the owner's *"smaller set than it
looks because of the ordering"*, made quantitative. Not done: the case where a crowd's common blocks run out before the
nesting reaches it.

---

## E127–E128 — 2026-09-27 — crowds run out; the owner's reference taken literally: a grid through a reading, at 1/m scale, plus a class

**Owner:** *"use the cascade to see what happens when the crowd runs out"*; *"keep attacking the proof, convert to lean
and keep reducing this proof. use the cascade to find why the gaps line up by 15."* Strip runs restarted at the
owner's request (E124's method, `[13,14]` onwards).

**E127, crowds** (`crowd_runout_v1/v2.out`, exact): adjacent readings of ratio `ρ` share clear blocks on laps
`k ≤ ⌊(7 − ρ)/(8(ρ − 1))⌋` (run-out at `R = (8K+7)/s_{i+1}`). Every late band landing (183 of 183) comes after the first
run-out; Case B to 24: 135,310 after, 75,025 before. After a run-out the cascade pushes the members on different laps:
the crowd is split at an internal gap with a window resting in it (two-block inside the crowd). Reading `[mine]`: at lap
`k` a window's relative width is about `1 + 1/(4k)`, so as laps grow any gap between distinct readings admits a window;
only equal speeds (gap ratio 1) can never be separated, the owner's *"for isolation not to occur you have to break every
speed being different"*. Simultaneity (all crowds at one instant) is not derived.

**E128, the transfer between copies** (`copy_transfer_v1.out`, 639 late shapes): covering copy 0 does not force the
top's gap `G₂` open (148 miss it); copy 1's first clear point is exactly `R = 9` in 300 of 639.

**E128, the reference grid** `[VERIFIED — exhaustive exact, finite windows; the family is a finding, not a proof]`: at
the AP scale write each reading `sᵢ = nᵢ + δᵢ` (grid position plus deviation; doubled slots and a reading captured at 8
allowed); candidate instants the classes `R = c` (odd `c ≤ 15`), relocated, with lap `⌊c·nᵢ/8⌋` (a captured reading on
the lap before or at), decided exactly by the pairwise theorem (`grid_class_v1.out`): covers 325,486 of 328,614 band sets
to 32 but only 118 of 272 late shapes. Allowing the reference grid through any reading `sⱼ` at scale `sⱼ/m`
(`grid_class_v2/v3`, `grid_class_exceptions_v1.out`):
- late band shapes: all 272 with `m ≤ 2`;
- the band to 32 (spread 7–9): all 365,287 with `m ≤ 2`;
- Case B to readings `≤ 24` (spread 7–24): 210,120 with `m ≤ 2`, the other 215 (spread mostly 21–24) with `m = 3` (210)
  or `m = 4` (5); every one covered with `m ≤ 4`.

**Reading** `[mine]`: the cascade's categories reorganise into the owner's two systems: **a grid through one of the
arrangement's own readings, at `1/m` of its scale (`m` small, growing with the spread), and one of the grid's classes
(`c` odd, a unit mod 8), relocated**. What decides a class is linear in the deviations: interior readings (`c·nᵢ ≡ 2…6`)
need `|c·δᵢ| ≤ 1` up to relocation; the edge readings (`c·nᵢ ≡ ±1`) need a sign; mirror classes (`c` and `−c`) swap the
edge roles, which is the pair law when each edge holds one reading. It fails in exactly two ways, both named by the owner:
a slot doubled at an edge (two readings with `c·nᵢ ≡ 1`), and deviations too large for the class (answered by a finer
grid, larger `m`). Not derived: that some `(j, m ≤ f(S), c)` always works.

---

## E129–E130 — 2026-09-27 — the pair law for any grid in Lean; the φ(8) classes suffice; the m = 2 exceptions; handover v8

**Owner:** *"keep going"*; *"The exception and counterexamples are important, they help you refine and clarify the
mechanism. You take the exception and perturb them through cascade"*; *"Just checking we are using a stationary runner,
as there are 8 runners so 8 gaps as this system is a circle and runner 1 is a neighbour to runner 8 as well as runner
7"* (answered: no runner at rest; the subject is the slowest runner, enough by `EndRunnerN`; seven positive readings;
lonely ⇔ both flanking gaps ≥ 1/8; see O8 below); *"we need to update the handover document so the context can be
compacted"*.

**Proved** (`Spec/GridPairLawN.lean`, commits `e12c237` and below; Spec gate PASS **1,915**,
`experiments/nN/spec_gate_grid_class_clear.out`) `[PROVED — axiom-clean]`:
- `grid_pair_law`: a grid (readings `x i`, grid points `n i`), classes `c` and mirror `c'` with the two edge readings
  swapped, all others interior under both; if every deviation after rescaling by `n a/x a` and by `n b/x b` is at most
  `1/C`, lonely at `c·n a/x a` or `c'·n b/x b`. The AP instance (classes 1 and 7) allows deviations up to `1/7`.
- `grid_class_clear`: one class, any number of readings per edge, small-deviation conditions.

**Measured** (`experiments/nN/redo/`, exact):
- `grid_pair_law_reach_v1`: the proved pair law alone settles 5,441 of 42,811 band sets to 24; obstruction mostly an
  edge empty or doubled.
- `grid_class_criterion_v1`: the single-class small-deviation criterion settles 38,517 of 42,811 (90%).
- `grid_class_unsettled_v1`: **the claim "the unsettled are captured readings" was false**: all 4,294 have a
  capture-free grid that still fails (the small-deviation bound is conservative against the exact block).
- `grid_class_control_v1` **(the control against tautology):** with the class unrestricted any flank opening counts as a
  class instant; restricted to **`c ≤ 7` (the four `φ(8)` classes), all 42,811 band sets to 24 are still covered with
  `m ≤ 2`.** The coverage is content.
- `grid_class_m2_exceptions_v1` (E130): 73 band sets to 24 need `m = 2`; they are grids at half the nearest runner's
  scale (half-integer shapes; the AP with one position moved); `±1` moves restore `m = 1` (60–95 per rank).

- **O8. A label slip in E121–E128:** `s₀ = 1` in the band notation is the reading of the runner nearest the subject in
  speed (`d_min`), not the subject; "the slowest runner's window `(7, 9)`" there means the nearest runner's window. The
  subject is the slowest runner and is never among the readings. Mathematics unaffected.

**Handover v8** written (`docs/n8/HANDOVER_2026_09_27_v8.md`, v7 kept): v7's §0 stands; adds items 28–31 (setup and
O8, O1–O7, the checks that caught errors, the owner's rulings), the proof state, the case structure, the mechanism, the
open step stated exactly. `compile-diff` loss check run next (recorded below when it reports).

---

## E131 — 2026-09-27 — handover v8 loss check (compile-diff): v8 not promoted; v9 repairs; items v8 had with no log entry

**`compile-diff` on v8** (against v7 and E109–E130; agent report, isolated context). Mechanical items all correct on disk
(8 of 8 modules, every theorem and gate count, every figure checked against the log or `.out`). **Losses found**, each
repaired in `HANDOVER_2026_09_27_v9.md` (v8 kept, not promoted):
- Global caveats: v7 was never loss-checked (E109); E114's recorded limit that larger ranges have turned up things smaller
  ones did not (applies to v8 §4's `m ≤ 4`, measured on readings `≤ 24`, where spread above 12 forces `d_min = 1`).
- Open items dropped: E110 (the two failure modes at a general live lattice `D`); E118 (what C1 needs); E121 (what bounds
  the jump at a wall); E122 (why a cover of copy 0 cannot survive the slides); E124 (Lean translation of the wall tree);
  E125 (the junction open step); E127 (simultaneity of crowds).
- Routes-not-to-re-derive dropped: E111's entering-edge proxy; E120's survival invariant, blocked-measure count and
  finite-state-machine route; E125's mirror orientation of the breaking pair.
- Scope or grade dropped (G1–G8, G12, G14, G15): among them the `1/ε` escape is one family; the supremum shape is
  `[EMPIRICAL — 64 climbs]`; late landings after run-out is 183 of 183 (Case B to 24: 135,310 after, 75,025 before);
  `pinch_eventually_lonely` needs a common period; `R* ≤ 1.377` is the 547 constructed C members (1.463 the 4,110
  cluster-drift sets, E73's climbs to 6.42); **the band to 32 and the late shapes (`m ≤ 2`) were measured with `c`
  unrestricted**; only the band to 24 has the `c ≤ 7` control.
- The open step in v8 §4 was stated with `c ∈ {1,3,5,7}` and `m ≤ 4` on Case B, where only `c` unrestricted was measured.
  The re-check is running (`experiments/nN/redo/grid_class_caseB_c7_v1.{py,out}`, `m ≤ 6`), recorded below when done.
- Notation: v8 §2's `89/s₇` should be `89/s₆` (band notation `s₀…s₆`).
- v8 §5 said "carried from v7 §5.10, unchanged" but added a decision and dropped v7's lap-`j` sentence.
- v8 items with no log entry, now given one here:
  - the landing's effective places: positions within `1/7` merged, **7 distinct in 186,869 of 328,614** band sets to 32
    (`experiments/nN/redo/band_effective_order_v1.{py,out}`, commit `9af4203`): the landing is not a disguised
    order-seven configuration;
  - strips (E124's method, `redo/strips_progress_v1.txt`, each tree independently checked, CHECK PASSED): `[12,13]` 308,
    `[13,14]` 337, `[14,15]` 399, `[15,16]` 754, `[16,17]` 762 categories (check of `[16,17]` running at writing);
    `[VERIFIED — computer-assisted, independently checked]` per strip;
  - owner, 2026-09-27 (chat): *"Please prove as much as possible in lean right away. It's the backbone and it tends to cut
    through any context rot/compaction."*
  - "`m = 2` is a knife-edge" and "the finer grid is the arrangement's own natural unit": my readings of E130, graded so.
- Consistency with v7, now stated in v9: the wall lemma (L) of v7 §3 step 2 and §5.1 is off the path (O4: the path route
  moves one runner at a time; `PathWindowN` needs no wall lemma); v7 §0.2's "the event exists by the deformation of the
  AP's global isolation" holds between whole-number points (order seven plus one free reading, `OneFreeN`) and carries
  nothing across them (O5); tools: E112 refines the 2026-09-15 ruling, and v7 §1.5's 2026-09-26 ruling (a measure
  argument inside one window, provisionally, if it completes a proof part) is not withdrawn.

---

## E132 — 2026-09-27 — the owner's reference with the φ(8) classes holds on Case B to 24; handover v9 loss check; v10

**The owed re-check** (`experiments/nN/redo/grid_class_caseB_c7_v1.{py,out}`) `[VERIFIED — exhaustive exact, readings
≤ 24]`: every Case B set (spread in `(7, 24]`, 210,335 sets) is lonely at a relocated class instant with the class
restricted to the **`φ(8)` classes `c ∈ {1, 3, 5, 7}`**, reference grid through one of its own readings at scale `sⱼ/m`:
least `m` = 1 in 201,698; 2 in 8,422; 3 in 210; 4 in 5; **uncovered 0**. So E128's Case B figure survives the tautology
control of E129: the owner's *"AP/grid plus a deviation"*, with the reference taken at the arrangement's own scale, is
exact on the whole of Case B in this window. Scope: E114's caveat (spread above 12 forces `d_min = 1` here).

**`compile-diff` on v9**: every loss E131 named is repaired. Still lost (all dating from before v8): E115's `WindowBound`
evidence (E72's `8·d_min·t ≤ 15`, `[VERIFIED]` for `S ≤ 24`, `[EMPIRICAL]` beyond, `T = 15/(8c)`) and its "what
`WindowBound` contains" caveat; E126's worst-phase nesting (every consecutive ratio at least 2 survives six steps,
`[reasoned]`, not in Lean); E124's tool caveats (`sympy` `lpmax` returned infeasible points on 2 of 300, not used; the
non-terminating first cover); E129's evidence (all 4,294 unsettled have a capture-free grid that still fails); the
`EightResidual` pending decision narrowed without source (v7: "the obligation or a sufficient route (v21 §17B)"). Also
flagged: the `c ≤ 7` result was on disk and unlogged (logged above); strip `[16,17]`'s check was still running.
Repaired in `HANDOVER_2026_09_27_v10.md` (v9 kept, not promoted).

---

## E133 — 2026-09-27 — handover versions stopped at v10

**Owner:** *"I'm worried the update document is recursively getting updated with no end."* Each `compile-diff` pass
compares the handover against the whole log, which is far more detailed than a handover, so every pass finds more to
carry (v8 → v9 → v10; the v9 pass's six losses all dated from before v8). Second time the owner has stopped this (E109).
**Rule from here:** `HANDOVER_2026_09_27_v10.md` is the handover. The v10 loss check's findings, if any, are recorded
here in the log only; no v11. The running log is the record; the handover points into it and does not repeat it.

---

## E134 — 2026-09-27 — handover v10 loss check (log only, per E133); read v10 with these corrections

`compile-diff` on v10: no open item, retraction or pending decision lost; every E132 repair present. Corrections to
read into v10 (no v11):
- **Strip `[16,17]`: CHECK PASSED** (762 categories; `redo/strips_progress_v1.txt`, committed in `LonelyRunner/`
  `d939fee`). v10's "check running" is stale. `[VERIFIED — computer-assisted, independently checked]`.
- **v10 §4 open step:** `m ≤ 4` is a measurement on readings `≤ 24` (E132), not part of the statement to be derived; the
  statement is E128's `(j, m ≤ f(S), c)` with `c ∈ φ(8)`. The `c ≤ 7` restriction is checked on integer readings `≤ 24`
  only; **not yet checked on the 272 late fine shapes** (their `m ≤ 2` figure used `c` unrestricted).
- **v10 §1, `WindowBound`:** E115's grade is `[reasoned in the text; not in Lean]`; the multi-pinch / no-common-period
  failure points belong to the converse argument (conjecture plus local stability ⇒ window), not to `WindowBound` itself.
  Also from E115, not in v10: near an arrangement with two runners at one speed, order seven gives loneliness at `1/7`,
  a margin, so the window holds there `[reasoned]`.
- **v10 §1, `NestedBlocksN` row:** E126's units are `u = 1/(8d)` (half a window), and the result is "not yet in Lean"
  (an observation, not a registered obligation).
- v10's "where v9 is silent" means where v10 is silent.

---

## E135 — 2026-09-27 — the doubled edge read from the cascade: not a case; it folds into the junction step

**Owner:** *"Brute force? … we should be using either BSM or cascade."* The first two scripts
(`redo/doubled_edge_v1.py`, stopped; `doubled_edge_v2.{py,out}`) searched references and lap assignments. Recorded fact
from v2 `[VERIFIED — exhaustive exact, band sets to 24]`: a working `φ(8)` class with at most one reading per edge
exists for 42,806 of 42,811; the other 5 need a captured reading; **no set needs a doubled edge**. (The v2 example list
prints sets with key `(0,0)` by a selection bug; the counts are correct.)

**The cascade itself** (`redo/doubled_slot_cascade_v1.{py,out}`, exact, every move of every band set to 24): moves with
1, 2, 3, 4 readings in the subject's window (open zone): 72,368; 24,073; 2,395; 32. At a move with several in the
window the cascade goes to the latest exit; every other member is then already past its own leaving edge (22,616 of
28,959 less than one eighth past, 6,002 less than two, 341 further), none still in the window.

**Reading** `[reasoned from the definition; the pieces are proved]`: a move goes to the maximum of the leaving points, so
any number of readings on the leaving side are at or past their edge there: the largest-left-end form of
`lonely_eight_of_pairwise_laps`, which never counts edge multiplicity. A doubled leaving edge is therefore never the
obstruction; the walk continues only when a reading **enters** before the last leaver clears. In grid-class terms that
is the interleaving (an entering reading's `n/x` between two leaving readings'), i.e. E125's junction again. **Open step
(i) of v10 §4 (doubled edges) folds into the junction step**: the doubled slot is the same event as one runner in the
way. Owner's *"the rules actually simplify"* (E117), here.

**Next** `[proposed]`: the `φ(8)` pairs are complementary: the edges of `(1,7)` (grid residues 1, 7) are interior
under `(3,5)` with slack, and conversely. So a crossing that continues the walk from a `(1,7)` instant is interior for
`(3,5)`. Test with the cascade: when the walk from a class instant is continued by a crossing, does it break at or
before the neighbouring class instant.

---

## E136 — 2026-09-27 — the AP reference's two mirror pairs against the cascade; pure crossing edges relocate to the two-block instant

(`LonelyRunner/experiments/nN/redo/ap_pairs_vs_late_v1.{py,out}`, `ap_edges_cross_v1.{py,out}`, exact.) At the AP
scale (grid `n = round(s)`), each `φ(8)` class decided exactly with relocation.
- **Forced, no content:** every late fine shape fails both pairs (5,400 of 5,400). At all four AP instants reading 0
  confines the relocated instant to `[1, 7]`, so any working AP class gives `R* ≤ 7`; the statement is its
  contrapositive. Recorded so it is not cited as a finding.
- **Content:** 6,021 band sets to 24 fail both pairs yet land in copy 0: the isolation relocates to a lap assignment the
  AP does not name. Reasons: capture 4,222; edges cross plus an interior deviation 1,650; **edges cross only 149** (the
  pure doubled edge: interleaved lags, no capture, interiors within slack).
- **The 149 through the cascade** `[VERIFIED — these 149 sets]`: both pairs doubled (residue patterns such as
  `(1,1,2,3,3,5,7)`: a companion near the nearest runner and a doubled 3); landing `R* ∈ [1, 2)` in 144, `[3, 4)` in 5;
  the flank a fast reading on its lap-1 leaving edge (the second opening `9/(8e)`); landing laps `0…0 1…1` in 144:
  **the two-block instant** (`TwoBlockN.lonely_eight_of_two_block`, proved). Reading `[mine]`: when a crowd at the bottom
  defeats both AP pairs by crossing edges, the isolation relocates to the fast group's next opening, where the readings
  split into two clear blocks. Next: perturb these through the cascade; derive "crossing edges at the AP ⇒ a two-block
  split exists", and read the 5 at `R ∈ [3, 4)`.

---

## E137 — 2026-09-27 — the band to 24 by the AP classes and the block instants; what is and is not content

(`LonelyRunner/experiments/nN/redo/proved_union_band_v1.{py,out}`, `proved_union_rem_cascade_v1.{py,out}`, exact,
band sets to 24, 42,811.)
- AP `φ(8)` classes (relocated, exact; instances of `lonely_eight_of_pairwise_laps`) ∪ two-block ∪ three-block
  (`lonely_eight_of_blocks`, `K = 1, 2`) settle all but **42**. The 149 pure crossing-edge sets of E136: two-block 144,
  three-block 5.
- The 42: `d_min = 3` in 40, `2` in 2 (grids in thirds or halves of `d_min`); AP failure capture 32, crossing plus
  interior 10; cascade `R* ∈ [3, 6)`; **every one lonely at a `K = 3` block instant `25/(8e)`**.
- **Grade of this** `[VERIFIED — these windows; not a derivation]`: the exact block condition at `(8K+1)/(8e)` *is*
  loneliness at that instant, and every cascade landing is some reading's opening `(8K+1)/(8e)` (its flank's). So
  "AP classes ∪ blocks with `K ≤ 3`" says: every band set to 24 is lonely at an AP class instant or at an opening on lap
  `≤ 3`. The content is the lap bound `K ≤ 3` in this window (E117 to 40: least lap up to 6), not the family. A derived
  rule has the form of E119's gap rule (a reading `e ≥ 9·d_max/15` with no reading in `(7e/9, e)` forces the two-block
  instant). **The derivation owed for the band is the analogue for each level `K`**: a checkable condition on the
  readings (gaps, in the owner's grid-at-scale-`e/(8K+1)` view) forcing the block instant, with the AP classes, and
  a proof that the conditions exhaust the band.

---

## E138 — 2026-09-27 — owner: regimes, not one rule; the four-block regime is a knife-edge at exact finer grids

**Owner:** *"I dislike treating the cascade as an algorithm that is search … it directs you to the isolation point
which is deterministically forced."* — *"I feel like sometimes you are looking for a rule that always works, but the
arrangement of speeds means different things apply at different times."* Taken as the frame: the proof is a partition
of arrangements by **regime** (AP class instant; two-block; three-block; four-block; …), each with its forced, proved
instant, plus the condition on the speeds that selects the regime; the owed content is those conditions and their
covering. E137's "not a derivation" grade stands for the union as a statement; the regimes are the objects.

**What switches a regime** (`LonelyRunner/experiments/nN/redo/regime_switch_v1.{py,out}`, exact): the 42 band sets to 24
whose isolation is at a four-block instant (E137), each reading moved in steps of `d_min/12` up and down until the
landing's laps change. Every reading, both directions, switches it (36–42 of 42 per rank and sign); the first step
almost always suffices. Switches drop the top lap (4 → 1, 2, 3; 3 → 1, 2) in 360 of 504, stay or rise in the rest (to 5
or 6 in 20). `[VERIFIED — these 42 sets]` Reading `[mine]`: the four-block regime sits only at exact grid points of a
finer grid (`d_min/3`, `d_min/2`); moving off the point relocates the isolation to an earlier, simpler regime (often
two-block, `R ≈ 1.3`). Same pattern as E130's `m = 2` exceptions.

---

## E139 — 2026-09-27 — the chain by multiplicity: crowds end it; long chains are single-runner relays

**Owner:** *"use the cascade to follow that chain"*; *"I think it's here we need to examine what the conjecture forces. I
firmly believe there aren't that many arrangements. AP scale invariance means it doesn't matter if it is 1…8 or
1m…8m, and grid means if it isn't 8m and it is 8 million and 7 that d_max or d_min finds the location point. Runners …
can pass the speed of their neighbour … if r2 speeds past r3 then it is r3. The cascade works because it understands
that no arrangement escapes it. We just need to logically show speed arrangements may be continuous but they are not
infinite. Cluster of speeds and some outliers is AP with some grid. The only hard problem in this is two runners in one
slot, but that is resolved. You can't even [have] three runners involved or it starts to apply AP again."*

**Measured** (`LonelyRunner/experiments/nN/redo/chain_multiplicity_v1.{py,out}`, exact; every move of every chain;
band to 24, Case B to 24, late fine band shapes), by `w` = runners in the subject's window at the move:
- `w = 4`: last move in 26 of 32 (band), 125 of 165 (Case B), 46 of 47 (late).
- `w = 3`: at most one move left in 2,148 of 2,395 (band), 6,483 of 7,600 (Case B), 1,866 of 2,669 (late; 601 with
  four or more left).
- `w = 1`: carries the long chains: in the late shapes 72,339 of 85,365 single-runner moves have four or more left.
`[VERIFIED — these populations]` Reading `[mine]`: a crowd of three or four in the window ends the chain almost
always (consistent with the owner's "three runners … apply AP again"); the long relays are one runner leaving as the
next arrives, two runners bracketing the subject's slot. Next: at each single-runner move, where the next runner sits
when the current one exits; trace the 601 late `w = 3` exceptions; count arrangement types with fast outliers taken
by their fraction (the category counts of E124 and the strips grow with the lap labels of fast readings, which the
owner's grid reading says are not types).

---

## E140 — 2026-09-27 — relays use every runner; the owner's near pair: delayed, forced, and already proved

**Relays** (`LonelyRunner/experiments/nN/redo/relay_setters_v1.{py,out}`, exact) `[VERIFIED — these populations]`: long
relays are not a pair taking turns. Chains of four or more moves (band and Case B to 24) use 4–6 distinct setters, the
top two setters under 75% of moves in nearly all; every late shape uses all seven. At a single-runner move the next
runner has just entered past `7/8` in 186,044 of 211,873.

**Owner:** *"So if you have 1, 2, 2.01, 3…8, all that does is delay the isolation point and it delays in a predictable
and forced manner."* Tested (`redo/near_pair_delay_v1.{py,out}`, exact), speeds `1, 2, 2+ε, 3, …, 7`, every runner as
subject, `ε = 1/100, 1/1000, 1/10000` `[VERIFIED — this family, these ε]`:
- runners outside the pair: isolated at `t = 1/8` (runner 3 at `1/(8(1−ε))`, beside it);
- the pair: the partner's reading is `ε`, so isolation waits for its first exit `1/(8ε)`; the cascade lands at the first
  instant after it where the other six are clear (runner 2: `12.5625, 125.125, 1250.125`; runner `2+ε`: exactly
  `1/(8ε)`), matching the forced location in all six cases. The delay is `1/(8ε)` plus less than one period of the six.
- **Already proved for every `ε`**: scaled to whole numbers the six other readings share a factor the partner's reading
  lacks: `OneFreeEightN.lonely_eight_of_one_free` (order seven on the six, then a written number of steps of their
  period). Only `ε = 0`, two runners at one speed, breaks it (the owner's statement).

---

## E141 — 2026-09-27 — the relay is a descending wave, repeated lap after lap

**Owner:** *"Most configurations that are considered unique are just reformations of the same pattern at different
parts of the circle. But because it is a circle that means if you prove cluster with outliers works at one point you
prove it for all."*

**Measured** (`LonelyRunner/experiments/nN/redo/relay_order_v1.{py,out}`, exact; setter rank.lap per move, rank 0 = the
nearest runner): the longest band-24 chains and the late shapes read
`6.1 5.1 4.1 3.1 2.1 1.1 | 5.2 4.2 3.2 2.2 1.2 | …`, with the fast runners entering the later sweeps at their own later
laps (`6.3`, `6.4`); late chains end `… 1.2 0.1`, the sweep reaching the nearest runner, whose exit of `(7, 9)` at
`R = 9` is the landing (many late `R* = 9.000`). Consecutive setter steps in late chains: to a slower runner 59,042, to a
faster 42,430. `[VERIFIED — these chains; the sweep decomposition not yet checked on all chains]`

**Reading** `[mine, in the owner's terms]`: the isolation is passed down the arrangement in speed order, one lap per
sweep; each sweep is the same pattern one lap further on (the owner's "same pattern at different parts of the circle").
If exact, the argument's form is: one sweep either lands or hands over to a lap-shifted copy of itself; scale invariance
carries the step to every sweep. Next: check that every chain decomposes into descending sweeps, and what ends a sweep.

---

## E142 — 2026-09-27 — the chain has three move types, forced by ordering: sweep down, bridge up, bridge down

(`LonelyRunner/experiments/nN/redo/sweep_bridge_v1.{py,out}`, exact.) Consecutive setters `a → b` with exit laps:
| population | sweep step (slower, same lap) | bridge up (faster, higher lap) | bridge down (slower, lower lap) |
|---|---|---|---|
| band to 24 | 52,656 | 3,701 | 498 |
| Case B to 24 | 51,127 | 51,443 | 22,625 |
| late fine band shapes | 24,384 | 42,373 | 34,578 |
No other type occurs; the sweep-step ratio condition `s_a(8k−1) < s_b(8k+1)` holds on all 128,167.

**Why** `[reasoned; one line from ordering]`: at `a`'s exit `R = (8k+1)/s_a`, a runner `b` in its window
`(8l−1) < s_b·R < (8l+1)`; if `s_b > s_a` then `s_b·R > 8k+1`, so `l > k`; if `s_b < s_a` then `s_b·R < 8k+1`, so
`l ≤ k`. Laps at any instant are ordered as the speeds are (the owner's *"if r2 speeds past r3 then it is r3"*).
A sweep on lap `k` passes down through consecutive ratios below `ρ_k = (8k+1)/(8k−1)` (9/7, 17/15, 25/23, … → 1), so a
gap that stops a sweep on lap `k` stops it on every later lap; only equal speeds pass every lap.

**Reading in the owner's terms** `[mine]`: clusters sweep (the AP at the cluster's own scale), outliers bridge (the
grid: a fast runner's window, width `2/s`, only nudges the instant; the owner's "8 million and 7"); the landing is where
a sweep reaches a gap no outlier covers. The band is sweep-dominated; late shapes are bridge-dominated. Next: the
bridges in late shapes, who bridges and across which gaps.

**E142 addendum — in Lean** (`LonelyRunner/LonelyRunner/LRC/Spec/SweepBridgeN.lean`; Spec gate PASS **1,920**,
`experiments/nN/spec_gate_sweep_bridge.out`) `[PROVED — axiom-clean]`: `lap_lt_of_faster` (bridge up),
`lap_le_of_slower` (sweep step or bridge down), `sweep_ratio` (a sweep step needs `s_a(8k−1) < s_b(8k+1)`),
`sweep_ratio_mono`, `sweep_stop_persists` (a ratio that stops a lap-`k` sweep stops the lap-`k+1` sweep).

---

## E143 — 2026-09-27 — the landing is a cluster bottom's exit (forced); the question as rotations of the circle

(`LonelyRunner/experiments/nN/redo/landing_cluster_v1.{py,out}`, exact.) Clusters on lap `k` = maximal runs with
consecutive ratio below `ρ_k`. Every landing with its flank on lap `k ≥ 1` is the exit of the slowest member of its
lap-`k` cluster: band to 24 42,013 of 42,013; Case B to 24 103,355 of 103,355; late 5,400 of 5,400 (2,311 of them the
nearest runner's `R = 9`). The rest land at the bound (lap 0). **Grade: forced, not a finding** `[reasoned; one line]`:
at a lonely exit `(8k+1)/s_f`, a slower neighbour within ratio `ρ_k` would sit in its own window (`sweep_ratio` read
backwards); at `k = 1` this is E119's gap rule (no reading in `(7e/9, e)`).

**The question in the owner's circle terms** `[reasoned]`: fix a cluster bottom `e`; its exits are `(8k+1)/(8e)`,
`k = 1, 2, …`; between consecutive exits every other runner `i` advances by the fixed fraction `s_i/e` of a lap: a
rotation of the circle. A cluster rotates coherently while its spread allows (E127's run-out); an outlier is one
rotation. The landing is the first exit of some cluster bottom at which every rotated runner is out of the subject's
slot. The owner's *"prove cluster with outliers works at one point … you prove it for all"* reads here as: the
configuration at exit `k+1` is the configuration at exit `k` rotated, so a statement proved for one exit in a form
invariant under the rotation holds for all.

- **O9. E143's rotation form is Theorem 6.15** (`ScaleCandidates.lonely_iff_exists_candidate_scale`, proved; the
  obligation of record since 2026-09-20): lonely iff some candidate `e/(8k+1)` is clear. Caught by the pre-use grep
  before anything was built on it. What E143 adds is only the derived restriction: a candidate `e` on lap `k` must be a
  cluster bottom (no slower reading within ratio `ρ_k`).

---

## E144 — 2026-09-27 — landing types with laps dropped: the exact eighth-slot description keeps growing (scoped)

(`LonelyRunner/experiments/nN/redo/landing_types_v1.{py,out}`, exact.) Type = per rank the eighth-slot of the position at
the landing (flank marked), laps dropped. Distinct types, all spreads, readings `≤ N`: `N = 12` 521; 16 5,064; 20
22,199; 24 57,802 (Case B dominates: 55,329 at 24). **Scope of the null**: this description separates landings that differ
by a deviation crossing an eighth line, which the owner's picture counts as one pattern relocated; it says nothing
about types modulo relocation (like E36b's 95,888 slot-residue types, too fine). Not a test of the owner's finiteness
claim at the owner's level. A test at that level needs types taken up to relocation (the pattern and its relocations as
one class), not yet defined operationally.

---

## E145 — 2026-09-27 — the owner's types, counted; what the count can and cannot test

**Owner** (confirming the definition): *"yes I think that matches, use it and test with the cascade. Because we are
comparing to global isolation, the specific arrangement works anywhere along the line and around the circle."* Type =
cluster composition (runs below `ρ_k`, `k` the landing lap, lap 0 read as `ρ₁`), the landing cluster (bottom = flank),
each outlier's eighth-slot at the landing; laps and in-slot deviations dropped (scale and lap-rotation invariant).

(`LonelyRunner/experiments/nN/redo/owner_types_v1.{py,out}`, exact, spread `≤ 24`.) Distinct types for readings `≤ N`:
12: 543; 16: 5,482; 20: 24,238; 24: 75,941; 28: 93,126 (new per step 4,939 → 18,756 → 51,703 → 17,185). Cluster
compositions 64 of 64 by `N = 24`; (composition, landing cluster) 175 at 24 and at 28.

**Grade** `[reasoned]`: an outlier in slot 1–6 is clear, so membership of a type already includes loneliness at its
instant; types are finite by construction (`≤ 64 · 7 · 6⁶`) and "every arrangement has a type" is the conjecture. The
count is therefore not the test. The owner's "works anywhere along the line and around the circle" is tested instead by
**predictability**: whether the landing cluster is determined by the lap-1 cluster structure (read from the speeds
before any landing), leaving the outliers' clearance (the grid) as the proof obligation. Next entry.

---

## E146–E147 — 2026-09-27 — d_min or d_max; the landing is the fast group's own point (the recursion)

**Owner:** *"the conjecture itself is a limitation to the arrangements that can happen; once you add scale invariance and
infinity to it, plus mirror effect and circle effect that just displaces the arrangement, you are not left with a whole
lot."*

**E146** (`LonelyRunner/experiments/nN/redo/landing_predict_v1`, `dmin_dmax_v1/v2`, exact, spread `(7, 24]`, readings
`≤ 24`): the lap-1 cluster composition alone predicts the landing cluster in at most 55.17% (so composition is not the
decider). With clusters cut at the landing lap's `ρ_k` (the confirmed type definition): band: bottom of the fastest
cluster 41,272, at the bound 798, other 741; spread above 9: bound 64,169, fastest-cluster bottom 54,129, other 49,226,
and in every frequent "other" description the flank lies above the largest gap.

**E147, the recursion** (`redo/fast_group_v1.{py,out}`) `[VERIFIED — these windows]`: split at the largest consecutive
gap into a slow group and a fast group `G`; for every landing not at the bound, run the cascade on `G` alone from the
same start `1/(8 d_min)`:
- band: the full landing **is** `G`'s own landing in 42,013 of 42,013;
- spread above 9: 102,652 of 103,355; the other 703 are delayed by the slow group (one blocker at `G`'s landing in
  676, two in 27), which pushes the isolation to `G`'s next point (the near-pair's forced delay, E140); flank in the slow
  group in 429.

**Reading** `[mine, in the owner's terms]`: the arrangement splits at its largest gap; the isolation is either d_min's
(the bound) or the fast group's own point. `G` has at most six readings: a lower order, native and proved (orders 3–7),
lonely with margin `1/(|G|+1) ≥ 1/7`. The one condition left is that the slow group is clear at one of `G`'s lonely
instants: **E118's C1 statement, now the mechanism of Case B as well as Case C**; `FastPair8`, `BlockSplit8`,
`OneFreeEightN` are its proved cases. Next: C1 through the cascade (how `G`'s lonely instants sit against the slow
group's windows; the 703 delays perturbed).

---

## E148 — 2026-09-27 — Case B's mechanism in two regimes: d_min's bound, or the fast group inside the slow group's first block

(`LonelyRunner/experiments/nN/redo/c1_block_v1.{py,out}`, exact, spread `(7, 24]`, readings `≤ 24`)
`[VERIFIED — this window]`. Split at the largest consecutive gap into slow group `S` (top `s_top`) and fast group `G`.
From `t₀ = 1/(8 d_min)` every slow reading has cleared its first window, and if `S`'s spread is at most 7 the whole of
`S` stays clear until `7/(8 s_top)` (`S` is an R1 group at `d_min`'s scale). Of the landings not at the bound:
- band: `G`'s own landing lies in `S`'s first clear block in **42,013 of 42,013** (gap `≥ 15/7` in 25,841; in
  `[9/7, 15/7)` in 16,172);
- spread above 9: in `S`'s first block 102,583; in a later block of `S` 69; delayed by `S` (not `G`'s own landing) 703.

**So on Case B to 24 the mechanism is two regimes** `[my reading of the above]`: (1) d_min: the bound is clear; (2)
d_max: `S` is R1 at `d_min`'s scale and `G` (at most six readings) reaches its own isolation inside `S`'s first block
`[1/(8 d_min), 7/(8 s_top)]`. Exceptions to study by perturbation: the 703 delays and 69 later-block landings (772 of
210,335). **Owed, now precisely:** a statement about `G` alone: `G` is lonely at some instant in the window
`[1/(8 d_min), 7/(8 s_top)]`, i.e. in `G`'s coordinates `R_G = 8 g₁ t ∈ [g₁/d_min, 7 g₁/s_top]`, a multiplicative window of
ratio `7 d_min/s_top`. Next: the reduction in Lean (slow group clear on its first block; `G` clear there ⇒ lonely).

---

## E149 — 2026-09-27 — the fast group at its landing: one crowd, or its clusters on consecutive laps

(`LonelyRunner/experiments/nN/redo/fast_group_shape_v1.{py,out}`, exact, the d_max landings of E148.) The fast group `G`
at its own landing inside the slow group's first block is either on one lap (a common block of `G`: band 6,018 of
42,013, most often for `|G| ≤ 4`) or split over 2–6 laps; the first split falls at `G`'s largest gap in roughly 60–70%.
`[reasoned]` A split between `gᵢ` and `gᵢ₊₁` across lap `m` needs only `gᵢ₊₁/gᵢ ≥ ρ_m`, so any gap above the lap's
threshold can carry it: `G` at its landing is its clusters at the landing's lap thresholds, each on one lap: the block
rule (`lonely_eight_of_blocks`) inside `G`, consistent with E143. Note: the largest gap often sits just above the nearest
runner (`|G| = 6`), so the split into `S` and `G` is frequently "the nearest runner and the rest".

**Where the proof stands on Case B** `[my reading]`: regime (1) the bound; regime (2) the slow group R1 on its first block
(`SlowBlockN`, below) and the fast group lonely there at a block-rule instant. The owed statement is that such an
instant exists in the window `R ∈ [1, 7/s_top]` (units `d_min = 1`): a statement about at most six readings, native
lower order supplying their loneliness but not its position in the window.

**E149 addendum — in Lean** (`LonelyRunner/LonelyRunner/LRC/Spec/SlowBlockN.lean`, commit `8e67a47`; Spec gate PASS
**1,922**, `experiments/nN/spec_gate_slow_block.out`) `[PROVED — axiom-clean]`: `slow_clear` (a reading in
`[d_min, s_top]` is clear at every instant with `d_min·t ≥ 1/8` and `s_top·t ≤ 7/8`); `lonely_of_fast_in_slow_block`
(on that block, if every fast reading is clear, every reading is): the d_max regime reduced to the fast group.

---

## E150 — 2026-09-27 — the 772 exceptions through the cascade: the roles swap, the grid nudge, forced delays

**Owner:** *"yes use the cascade on the 772 exceptions"*; then *"keep going, prove the reduction in lean"*.

(`LonelyRunner/experiments/nN/redo/exceptions772_v1/v2/v3.{py,out}`, exact.) The 772 Case B sets (readings `≤ 24`) not
settled by the two regimes of E148 (703 delayed, 69 later-block). v1: the blocker of the fast group's first point is
the slow group's top (or next-to-top), on lap 0 or 1; the slow group spans more than 7 in 472 of 703 (it is itself a
band arrangement, e.g. `(1,2,3,4,5,8)`) with one far outlier above (16–24). (v1's "landing = the first `G`-point with
`S` clear" holds by definition and is not cited; v2 was capped at 400 sets and is superseded; a first v3 hung on a
`10⁻⁹` stepping loop and was replaced by the flank test.)
**v3, all 772** `[VERIFIED — these 772]`:
| mechanism | count |
|---|---|
| the slow group leads: the landing is `S`'s own first point, the fast group clear there | 260 |
| grid nudge: the far outlier is the only reading `≡ 0 (mod 8 d_min)` (captured at the bound), landing `t₀ + 1/(8 d_max)` (`GridNudgeN`, proved) | 51 |
| the slow group's next point (flank slow; `G` blocked its earlier points) | 169 |
| the fast group's next point (flank fast; `S` blocked its earlier points) | 292 |
The last two rows' split by the flank's group is forced (every landing is some reading's exit); their content is the
forced delay (E150 v1: one to three points skipped), the near pair's behaviour (E140).

**So on Case B to 24** `[VERIFIED — this window; my reading of the mechanisms]`: every set is settled by the bound;
the fast group inside the slow group's first block (E148, `SlowBlockN`); the slow group leading (roles swapped); the grid
nudge (`GridNudgeN`); or a forced delay of one to three points of one group. The owner's "a multiple of 8 outside the
AP is still captured by the grid" is the 51 nudge cases literally.

**E150 addendum — owner:** *"Why only whole numbers? At any scale AP it is just a deviation. Example 100…800 and if the
second runner is 201, that is just fraction and d_min works?"* The reduction theorems `lonely_of_fast_in_slow_block`,
`block_iff_fast`, `exists_block_iff_fast` are stated for any real readings; the `Finset ℕ` form
(`lonely_eight_of_fast_in_slow_block`, `lonely_eight_of_regimes`) only matches the residual target, which is on whole
numbers because `RealEightN` reduces real speeds to them. The example, exact: speeds `100, 201, 300, …, 800`, every runner
as subject, is lonely exactly at its own bound `1/(8 d_min)` (`d_min` 101 for runner 100, 99 for runners 201 and 300,
100 otherwise): the deviation moves `d_min`, and the isolation sits at the relocated bound (R1, proved for all real
speeds).

---

## E151 — 2026-09-27 — the band followed with the cascade: the slow group on one lap, the fast group's own point

**Owner:** *"This is easy, it's not a problem. Use the cascade on the band to see why."* Then, on my summary's last
sentence: *"are you sure you aren't doing that thing which says, I need to offer one more thing to do?"*

(`LonelyRunner/experiments/nN/redo/band_ladder_v1/v2.{py,out}`, exact; band to 24 in units of `d_min`, and the late
fine band shapes.)
- **Derived and confirmed:** split at the largest gap (at least `9/7` in the band, `exists_big_gap`); every lap-1 exit
  `9/g` of a fast reading lies in the slow group's first block `[1, 7/s_top]` (0 violations in 42,811 and 5,400).
- **"Inside the slow group's first block" was range-forced (O7 again):** it holds on the integer band to 24 but on none
  of the 5,400 late fine shapes, which land at `R ≥ 9`.
- **The regime, corrected** `[VERIFIED — these two populations]`: at the landing the slow group is on one lap and the
  landing is the fast group's own first point from the start of that lap's block: band to 24 **42,811 of 42,811**
  (lap 0); late shapes **5,400 of 5,400** (the slow group is the nearest runner alone, lap 1, `R = 9`).
- When block level 1 fails the top four are dense: 1,968 of 1,968 (band), 3,089 of 3,089 (late) (`b1_remainder`,
  proved). Least block level: band 1–4, late 1–6; landing laps up to 9.
- **Retracted from my summary:** "if no reading qualifies … the same argument runs one lap later with threshold `17/15`
  … it goes on the same way until `ρ_k` falls below some gap, which always happens". **Not established**: "top dense ⇒ a
  three-block instant" is not derived; `SweepBridgeN` gives that gaps eventually stop sweeps, not that a block rule then
  holds (outliers can still bridge); the late shapes need levels up to 6. The owner caught it: a tidy continuation
  offered in place of the stopping point.
- **Owed, the one statement:** the fast group has its own point before the slow group's common block (on its lap) ends.

**E151 addendum — in Lean** (`SlowBlockN`, `LonelyRunner/` commit `75d35d0`; Spec gate PASS **1,926**,
`experiments/nN/spec_gate_regimes.out`) `[PROVED — axiom-clean]`: `block_iff_fast` and `exists_block_iff_fast` (real
readings: on the slow group's first block, the whole question is exactly the fast group's);
`lonely_eight_of_fast_in_slow_block` and `lonely_eight_of_regimes` (whole-number form: the bound, or the fast group clear
somewhere in the slow group's first block). Not yet in Lean: the same on the slow group's common block on lap `k`
(needed for the late shapes, E151).

---

## E152 — 2026-09-27 — Case C through the cascade; a correction to E148/E151's second clause; the six-reading window

**Owner:** *"use the cascade on case C … Please do autonomously."*

**Correction (forced by definition, found before relying on it):** once the slow group is on one lap at the landing it
is clear throughout that lap's common block, so any clear point of the fast group inside the block is clear for all,
and the cascade lands at the first. "The landing is the fast group's own first point from the block start" therefore
**follows** whenever the slow group is on one lap: E151's 42,811/42,811 and 5,400/5,400 for that clause, and E148's
"`G`'s own landing" once the landing is inside the slow group's first block, are not evidence. **The content** is only:
the slow group is on one lap at the landing, i.e. the landing lies inside the slow group's common block (E148: the
landing is inside `[1/(8 d_min), 7/(8 s_top)]`).

**Case C** (`LonelyRunner/experiments/nN/redo/casec_regime_v1`, `casec_groups_v1`, exact): P1 = every set with
`d_min = 1`, readings `≤ 32`, spread `> 24` (635,334); P2 = 19,625 random wide (spread 25–2,000); P3 = the 547 constructed
residual C members. Not at the bound: P1 378,084; P2 14,273; P3 547. The slow group (below the largest gap) is on one lap
at the landing (lap 0) in P1 370,387 (98.0%), P2 7,200 (50.4%), P3 547 (the slow group is the nearest runner alone in
292,211 of P1 and all of P3). Room used inside the block mostly under a quarter. **Recursive splitting into R1 groups is
the wrong cut** (scoped negative): at the landing some R1 group is split over laps in most sets (an R1 group of spread up
to 7 shares a lap block only on lap 0; E127's run-out).

**The dominant shape's lemma** (`redo/six_window_v1.{py,out}`): with the slow group the nearest runner alone, its block is
`R ∈ [1, 7]`, a window of ratio 7, and the fast group starts past its own bound. Needed: *`m ≤ 6` readings, from any start
`A ≥ 1` in their own bound units, are clear at `1/8` within ratio `ρ` of `A`*. Worst `ρ`, exact, readings `≤ 20`:
`m = 4`: 19/7 ≈ 2.71; `m = 5`: 25/7 ≈ 3.57; `m = 6`: **33/5 = 6.6** (`(6, 8, 10, 11, 13, 14)`: from just after `R = 3`,
next lonely at `99/5`). Close to 7 on a finite window (the O7 caution applies); pushed further next.

**Lean** (`SlowBlockN`, commit `f21edb2`; Spec gate PASS **1,929**, `experiments/nN/spec_gate_regimes_lap.out`)
`[PROVED — axiom-clean]`: `slow_clear_lap`, `exists_block_iff_fast_lap`, `lonely_eight_of_fast_in_slow_block_lap`: the
reduction on the slow group's common block on any lap `k`.

---

## E153 — 2026-09-27 — the six-reading window: factor 7 fails on fine shapes (ρ reaches 9); the blocks form; run protections

(`LonelyRunner/experiments/nN/redo/six_window_climb_v1.{py,out}`, exact.) E152's candidate lemma "six readings, from any
start `A ≥ 1` in their own bound units, are clear within ratio 7" is **false on fine shapes**: hill-climbs reach
`ρ = 9.0000` (e.g. `(1, 1.3746, 1.7628, 2.2539, 2.5123, 3.23)`), `8.9998`, `8.72`, `8.43`, `7.52`. The integer value 6.6
(readings `≤ 20`) was range-forced (O7's pattern, caught before use). Mechanism `[my reading]`: a dense six-crowd is
lonely in its first block, runs out of shared blocks (E127), and waits for a late alignment.

**The form that matches the cascade** `[reasoned]`: with the slow group the nearest runner alone its blocks are
`A·([1,7] ∪ [9,15] ∪ …)` in the fast group's units; the late band shapes land in the second (`R = 9`). So the question is
how many of the slow runner's blocks the worst start needs. This is Case C's own statement (slow runner plus the six)
with a lap count attached, the same form as the band theorem (the nearest runner's first two blocks); its content is
whether a small fixed count always suffices.

**Process** (owner: *"If you're going to start a slow run you should caffeinate and put protections around it"*): the
first scan (`six_blocks_v1`) was started bare inside a foreground wait, against v7 §1.12; stopped. `six_blocks_v2` runs
under `caffeinate` with a progress file, a resumable checkpoint, early flags for sets needing more than two blocks, and a
positive control. The first control was wrong (the rounded E121 supremum shape keeps its single isolated point
`R ≈ 6.319` in the first block, so one block suffices for it); replaced by a late shape from the E121/E128 walk verified
by the cascade (`R* = 9.0`), whose six from their own start need the second block: control PASS. Result recorded below
when the scan ends.

---

## E154 — 2026-09-27 — the six-reading crowd through the cascade: the slow runner carries it to its second block

**Owner:** *"Are you using the cascade in these climbs?"* No: `six_blocks_v2` computes the six-group's whole lonely set
and searches starts (same numbers as the cascade from each start, but no chain read). Switched to the cascade for the
mechanism; the integer scan keeps running for its counts.

(`LonelyRunner/experiments/nN/redo/six_blocks_cascade_v1.{py,out,progress}`, exact, under `caffeinate`, control passed.)
A slow runner alone (reading `1/A` in the group's units; its blocks `A·[8k+1, 8k+7]`) below the four extremal fine
six-crowds of E153; starts at the end of the crowd's first block, just after it, and a grid in `[1.7, 12]`: 102 of 112
starts land in the slow runner's first block, 10 in its second, none later. In all 10 the chain is the same
`[VERIFIED — these 10]`: the crowd runs out of shared blocks and its windows chain (setters at laps 2–9); once past `7A`
the slow runner is inside its own window `(7A, 9A)` and **sets one move itself, its exit at `9A`**; the crowd then lands
after 1–5 more moves at `R ∈ [9.0, 10.6]` (slow runner's units), inside `[9, 15]`. The late band shapes' `R = 9` landing
(E151) is the same event. Integer six-sets (least `≤ 20`, readings `≤ 20`, starts `A ∈ [1, 12]`): the chunks finished so
far need only the first block.

---

## E155 — 2026-09-27 — owner: stop searching, use the cascade; the wide Case C sets land at the bound (scale separation)

**Owner:** *"You have an oracle that tells you exactly the answer and you fool around with a hill climb that tells you
nothing … We had a process where you test with the cascade and perturb if you need."* The hill climbs (E153) and the
worst-start scan (`six_blocks_v2`, stopped) were searches for extremes; they explain nothing. Process restored: case →
cascade chain → perturb the deciding runner.

(`LonelyRunner/experiments/nN/redo/casec_split_cascade_v1.{py,out}`, exact.) Twelve random wide Case C sets (spread 400–
2,000) whose slow group (below the largest gap) is split over laps at the landing (E152's 50% of P2): **every one lands
within 1–3 moves of the bound, `R* ∈ [1.001, 1.33]`**; perturbing the off-lap slow readings by `d_min/4` moves the
landing by at most `0.4` and in most cases not at all. `[VERIFIED — these 12]` Reading `[mine]`: these sets are several
scales well apart (neighbour ratios such as 6.1, 3.5, 8.1); splitting at the single largest gap leaves a "slow group"
spanning several scales, so its readings sit on different laps — an artefact of the split, not a hard case. The cascade
lands at the nearest runner's bound and a fast runner in the subject's slot moves it by a nudge the width of its narrow
window (the owner's "8 million and 7"). The structure is **clusters at well-separated scales, nested**: `nested_clear`
(proved) is the case of single readings with ratios `≥ 7/3`. Next: state the nested-clusters rule, test it with the
cascade on the Case C populations, perturb the exceptions.

---

## E156–E158 — 2026-09-28 — the regime skeleton in Lean; the coverings checked before stating; one mechanism

**Owner:** *"Ok please look at the lean and the proof we are trying to construct"*; then *"yes build it in lean"*; *"As the
gaps get bigger, they just fall into larger grid positions; we shouldn't need thousands of certificates, we can already
prove grids globally isolate and then it's just a deviation from grid"*; *"It will be because there are two runners in
the same slot, which just means it delays the isolation event because the runners need to separate from each other"*;
*"It's the same mechanism over and over. Can't you see that."*

**Review of the Lean (E156):** `LonelyRunnerAt8 ⇔` every `EightResidual` set lonely (proved); `⇐ CaseB8 T ∧ CaseC8 T`
(Case A inside, proved; B and C OWED); `⇐ WindowBound` (OWED). Of this session's modules only `OneFreeEightN` fed the
target (as the residual field `no_one_free`); `TwoBlockN`, `NestedBlocksN`, `GridPairLawN`, `SweepBridgeN`, `SlowBlockN`,
`OneFreeN` were imported by nothing. The three Case B agents died with the previous process (exploration scripts only).

**Coverings checked before stating (E157)** (`LonelyRunner/experiments/nN/redo/regime_cover_v1/v2`,
`casec_gridclass_v1`, `casec_composed_v1`, `casec_leftover_cascade_v1`, exact, protected runs):
- An ad hoc regime list (bound, first opening, low blocks, slow block at the largest gap) left 14 Case B sets and
  hundreds of Case C sets uncovered; allowing the slow block with the nearest runner alone would make the covering the
  E72 neighbour bound (the regimes then do no work). Not used.
- **The grid-class regime** (grid through reading `e` at scale `e/mm`, class `c ∈ φ(8)`, laps from the grid point,
  decided by 1-D Helly): Case B to 24, 0 uncovered with `mm ≤ 4` (E132); Case C: all 635,334 sets with least reading 1
  and readings `≤ 32` with `mm ≤ 4` (least `mm` 1/2/3/4 = 557,732/73,903/3,513/186); 19,610 of 19,625 random wide sets
  (`mm` up to 7); all 547 constructed residual C members (`mm ≤ 5`). The owner's "they just fall into larger grid
  positions" holds on these populations `[VERIFIED — these populations]`.
- The 15 random-wide leftovers: each has a middle reading on a multiple of `8 d_min` (captured at every rational class
  instant of the nearest runner's grid; never the largest, so `GridNudgeN` does not apply); the cascade releases it by
  its own exit and one to three fast nudges, landing at `R ∈ [1.009, 1.09]`. The composed regime (slow block plus a
  fast-group grid class) covers none of them.

**One mechanism (E158, owner):** the capture is two runners in one slot (the captured runner and the subject); the
isolation waits for them to separate, the captured runner's exit. The near pair (`1/(8ε)`, E140), the grid nudge, the
doubled edge (E135) and the late band's carry to `R = 9` (E151, E154) are the same event, and it is exactly one move of
the cascade (a runner in the subject's slot; go to its separation). The proof therefore has one mechanism and one
question: separation is forced whenever speeds differ; what must be shown is that separating one pair cannot keep
putting another runner into the slot for ever.

**In Lean** (`LonelyRunner/LonelyRunner/LRC/Spec/RegimeSkeletonN.lean`): regimes `BoundClear8`, `GridClass8`,
`WithinTwoBlocks8` (a placeholder for the separation regime; Case C only), `RegimeB8`, `RegimeC8`, each with a proved
sufficiency (`lonely_of_gridClass8` via `lonely_eight_of_pairwise_laps`); **`CoverB8`, `CoverC8` registered OWED**;
`caseB8_of_cover : CoverB8 → CaseB8 24`, `caseC8_of_cover : CoverC8 → CaseC8 24`,
**`lonelyRunnerAt8_of_covers : CoverB8 → CoverC8 → LonelyRunnerAt8`**. Gate result below.
Gate: **PASS 1,944** declarations, axiom-clean (`experiments/nN/spec_gate_regime_skeleton.out`); `CoverB8`, `CoverC8`
on the OWED register beside `WindowBound`, `CaseB8`, `CaseC8`.

---

## E159 — 2026-09-28 — are we proving the wrong thing? CoverB8 holds on fine shapes; the separation regime; the cell form

**Owner:** *"yes state the separation regime in lean … Yes but make sure we aren't trying to prove the wrong thing
because we termed the problem wrong."* With a pasted reframing (source not stated): the objects should be finitely many
combinatorial cells of normalised arrangements (AP/grid residue class, ordering of openings/walls, slot occupancy, which
pair is separating), each with a uniform isolation rule; continuous parameters move inside a cell until a wall; the
obligation is a finite transition/termination argument on cells, not a quantifier over all finite sets.

**Check 1, is `CoverB8` true beyond readings ≤ 24?** (`LonelyRunner/experiments/nN/redo/coverB_fine_v1.{py,out,progress}`,
exact, protected, control passed.) `CoverB8` quantifies over all whole-number sets at all scales. Bound or grid class
with `mm ≤ 4`, `c ∈ φ(8)`: the 5,400 verified late band shapes: least `mm` 2 (5,363) or 3 (37); 5,000 random fine band
shapes: `mm = 1`; 5,000 random fine shapes with spread 9–24: bound 1,347, `mm = 1` 3,649, `mm = 2` 4. None needs `mm > 3`.
`[VERIFIED — these populations]` Closes the E134 flag (late shapes with `c ≤ 7`).

**Check 2, the separation regime** (`LonelyRunner/LonelyRunner/LRC/Spec/SeparationN.lean`) `[PROVED — gate below]`: a
reading `c` exactly in the subject's slot at `t₀` (`c·t₀ ∈ ℤ`) separates at `t₀ + 1/(8c)`; every other reading `d` moves by
`d/(8c)` of a lap; if each keeps its band, all are clear there (`lonely_of_separation`; the mirror
`lonely_of_separation_back`). Generalises `GridNudgeN` to a captured reading of any rank. **What this shows about the
formulation:** the 15 Case C leftovers (E157) need two to four successive separations; repeated separation from an
instant is the cascade itself, so "the separations come to rest" is not a regime (it renames the conjecture for that
set). `CoverC8`'s `WithinTwoBlocks8` disjunct stays, documented as the place of the Case C transition argument.

**The cell form, assessed** `[reasoned]`: the pasted reframing is right about the form and is not a different statement.
A `GridClass8` instance is a lap assignment decided by a pairwise interval test; with the reference `(e, mm, c)`, each
reading's residue `c·n mod 8`, and the order of the fourteen interval endpoints, the data is finite and the rule inside
the cell is uniform (the largest left end); the walls between cells are endpoint coincidences (E124's walls). So
`CoverB8` says "the good cells cover the normalised shapes"; stated over all finite sets of readings it hides that the
data is finite. The obligation should be restated as: (a) the finite cell list with uniform rules (Lean: each is a
`GridClass8` or a separation instance); (b) either a covering of normalised shapes by good cells or a transition argument
in which a separation moves an arrangement from a cell to another and cannot cycle for ever. The proved ingredient for
(b): `SweepBridgeN.sweep_stop_persists` (windows narrow each lap, so a pair that has separated stays separated; only
equal speeds never separate).

---

## E160 — 2026-09-28 — the pasted spine tested with the cascade; a concurrent session in the Lean tree

**Owner:** *"AP is scale invariant meaning 1…8 and 1m…8m are the same thing. Likewise grid is infinite so 1…7,16 is the
same as 1…7,16m; we don't need a thousand iterations."* And a pasted proof spine (source not stated): choose the
arrangement's AP/grid reference and a clear class; reduce a failed class to one unresolved pair; take the captured
runner's forced exit; prove a **transport** statement ("after a pair exit that does not isolate, the new obstruction is a
relocated copy of the same grid arrangement, with a determined next pair/slot"; the relocated state keeps AP/grid
positions, edge directions and the captured pair, not scale or lap labels); prove **no return** (perpetual hand-off would
return to the same pair in the same relative slot state and force equal speeds). Stop proving `CoverB8`/`CoverC8`
directly.

**Scale and grid** `[reasoned]`: agreed; cells are normalised by scale and by grid position (residues). The continuous
data re-enters at one place: at a separation every other reading moves by `d/(8c)` of a lap; for the captured reading
the largest (`1…7,16`, `…,16m`) this is under an eighth and `GridNudgeN` applies; for a middle captured reading the
faster readings move more than a lap and where they land depends on `d/c`.

**The spine through the cascade** (`LonelyRunner/experiments/nN/redo/transport_v1.{py,out}`, exact, every move of every
Case B chain to readings `≤ 24`) `[VERIFIED — this window]`:
- **Residues alone do not determine the transport.** State normalised by scale and grid (each reading's eighth-slot,
  the separating runner, which readings are faster than it): 81,202 states, 11,419 (14.1%) with more than one next
  obstruction, almost all "lands" vs "one reading enters", decided by the position *within* the eighth. The transport
  state must carry the **order of the edge crossings (walls)**; with it the next state is determined by construction
  (the cascade is deterministic on that order). The pasted cell definition includes "ordering of the relevant
  openings/walls", consistent.
- **"One unresolved pair" is false as stated.** After a non-isolating separation the next obstruction is one reading in
  135,934 moves, two in 41,276, three in 4,675, four in 164, five in 1. The cascade still resolves it deterministically
  (latest exit; several on the leaving side are harmless, E135), so the transport lemma must allow a set in the slot.
- `move_eq_separation` (added to `SeparationN` by another session, read here): a separation whose other readings keep
  their bands is exactly the cascade's next move, `move 8 ds t₀ = t₀ + 1/(8c)`. First half of the spine's capture-exit
  step.

**Concurrent session.** Another session is editing `LRC/Spec` and running its own Spec gate
(`/tmp/spec_gate_capture_transport.out`), apparently on the capture-transport lemma. This session's gate for
`SeparationN` + the `RegimeSkeletonN` docstring failed its tree-stability check (`tree CHANGED during this run`) because of
that edit; nothing wrong with the Lean. `SeparationN.lean` (with the other session's `move_eq_separation`) and the
`RegimeSkeletonN` docstring edit are **uncommitted**; this session holds Lean edits and gate runs until the owner decides
which session owns the tree.

---

## E161 — 2026-09-28 — separation and transport, off-tree; no return for sweep steps; the no-return claim narrowed to bridges

**Owner:** *"Can you copy the earlier version not changed by the other session and see what you can do."* With a pasted
outline (source not stated): any arrangement is globally isolated by its AP/grid unless it has one captured pair; the
pair has a forced separation; at that event the cascade has transported the same global arrangement; if still blocked,
the blocker is again one captured pair; a sequence of hand-offs is constrained by the ordered runners and fixed grid
positions and cannot evade indefinitely.

**Work kept off the Lean tree** (another session is editing `LRC/Spec`): this session's version of `SeparationN` (without
the other session's `move_eq_separation` and `Cascade.Iteration` import) copied to the scratchpad, extended, and compiled
with `lake env lean` against the tree's built modules (no tree change; not gated). Copy kept at
`docs/n8/SeparationN_transport_draft_v1.lean.txt`. `[PROVED — compiles clean, no sorry; not yet gated]`:
- `crossed_entering_edge`: a reading clear at `t₀` that is in the slot after the separation crossed its entering edge
  during the shift `d/(8c)`.
- `slower_shift_lt`, `slower_obstruction_is_edge_push`: a slower reading moves less than an eighth of a lap, so an
  obstructing slower reading was within an eighth of its entering edge at `t₀` (an edge push, E93/E110).
- **`transport`**: after a separation (captured reading `c` exactly in the slot at `t₀`, the others clear at `t₀`), the
  captured reading is clear, and every reading in the slot crossed its entering edge during the shift; a slower one was
  an edge push. The next obstruction is made only of readings the shift carried over an entering edge.
- **`sweep_lap_bound`, `sweep_lap_lt`**: a sweep step from `a` down to `b` on lap `k` forces
  `8k·(s_a − s_b) < s_a + s_b`, i.e. `k < (s_a + s_b)/(8(s_a − s_b))`: a pair of distinct speeds hands the isolation
  down by a sweep step on finitely many laps; only equal speeds could on every lap.

**The outline's no-return step, checked** `[reasoned; E141 as evidence]`: "a perpetual hand-off would return to the same
pair in the same relative slot state and force equal speeds" cannot be derived from recurrence alone: the same pair in
the same slot state recurs in ordinary lonely sets (E141's relays repeat setters in order one lap later), and for
whole-number readings the full state recurs exactly after one period. The recurrence is not exact because windows
narrow each lap: that gives the finiteness above **for sweep steps**. Bridges (a faster runner on a later lap, a slower
one on an earlier lap) have no per-pair lap bound: at `a`'s exit on lap `k` the faster `b` is in a window iff
`‖(8k+1)·s_b/(8 s_a)‖ < 1/8`, which for a rational ratio recurs periodically. **The open core narrows to: bridges
cannot sustain the chain for ever.**

---

## E162 — 2026-09-28 — picking up the parallel session; O10: mistaking one general mechanism for many small ones

**Owner:** *"Have a look at the other session's progress … They have run out of tokens so you need to pick it up and
finish this proof."* The parallel session's plan: `DoubledSlotN` (the one-doubled-slot AP family), `DoubledNbhd*` (its
neighbourhoods) and `move_eq_separation` are the pieces; show any non-clear grid placement is carried into one of those
neighbourhoods at its own scale. Its tree changes: only `move_eq_separation` (+ the `Cascade.Iteration` import) in
`SeparationN`; its own gate (`/tmp/spec_gate_capture_transport.out`) never reached a verdict.

**Tree made whole:** `SeparationN` = this session's separation lemmas + the parallel session's `move_eq_separation` +
this session's `transport`, `crossed_entering_edge`, `slower_obstruction_is_edge_push`, `sweep_lap_bound`,
`sweep_lap_lt` (E161). Spec gate **PASS 1,957** (`experiments/nN/spec_gate_separation_merged.out`), committed
`LonelyRunner/` `261ccec`.

**The reach of the formalised family** (`LonelyRunner/experiments/nN/redo/doubled_family_reach_v1.{py,out}`, exact, Case B
to readings `≤ 24`): at the nearest runner's scale, 123 of 210,335 arrangements are in the `DoubledSlotN` family (the AP
with exactly one runner lapped); 14,583 have one doubled slot with several runners lapped; 85,972 two or more doubled
slots; 735 a complete residue system; 108,922 are off the nearest runner's grid. **Scope:** this measures the narrowness
of one parametrised Lean instance, not a failure of the mechanism; it also counted doubled slots anywhere on the circle,
when only the subject's own slot matters (a doubled slot elsewhere is harmless, E89). Owner: *"That is weird … because the
cascade never fails."* Correct: every cascade move is a runner in the subject's slot separating.

- **O10. Mistaking general mechanisms for small distinct ones.** Owner: *"Do you see you have been mistaking
  generalisable mechanisms as small distinct ones?"* Yes. The near pair, the capture, the grid nudge, the doubled edge,
  the carry to `R = 9`, the 772 exceptions and the 15 Case C leftovers were measured and named separately; they are one
  event (a runner in the subject's slot; the isolation waits for it to separate). The regime lists (bound, first opening,
  block level, slow block, grid nudge) are instances of one principle (the arrangement's own grid, read at an instant,
  with deviation), and were extended item by item whenever something leaked. The reach measurement above compared
  arrangements with one parametrised instance and read its narrowness as a property of the mechanism.

**The general mechanism, already in the tree:** (1) `GridPairLawN.grid_class_clear`: any grid through the arrangement's
own reading, any scale, any laps, any number of readings per slot: every runner clear except those in the subject's slot;
(2) `SeparationN.lonely_of_separation` / `move_eq_separation`: those separate, any rank, exactly the cascade's next move;
`transport`: the next obstruction is only readings the shift carried over an entering edge. `DoubledSlotN`,
`DoubledNbhdN`, `GridNeighbourhoodN`, `APNeighbourhoodN`, `GridNudgeN` and the one-free lemma are special cases of (1)
and (2). **The one open statement:** repeated separation cannot continue for ever; proved part: a pair of distinct speeds
hands over by a sweep step on finitely many laps (`sweep_lap_bound`).

---

## E163 — 2026-09-28 — bridges through the cascade; why "no return" is the conjecture itself; what is left

**Owner:** *"yes use the cascade on the bridges and bring this proof home."*

(`LonelyRunner/experiments/nN/redo/bridge_recur_v1.{py,out}`, exact.) Bridge pairs (a hand-over to a faster runner on a
later lap, or a slower one on an earlier lap) recur within one chain: 26 times in Case B to 24, 4,298 in the late fine
band shapes, at gaps of 1–3 laps. Unlike sweep steps (`sweep_lap_bound`), bridges carry no per-pair lap bound: at `a`'s
exit on lap `k` the faster `b` is in a window iff `(8k+1)·b/a` is within 1 of a multiple of 8, which recurs. Chains end
after a bridge in 41,798 Case B chains and after a sweep in 48,928; every late shape ends after a bridge. (The "every `r`
laps" gloss in my message was loose: the condition can hold on consecutive laps.)

**Why "repeated separation cannot continue for ever" is not a smaller lemma** `[reasoned]`: for whole-number readings
(`RealEightN` reduces to them) every position repeats exactly after one period; a chain that runs a full period without a
gap never ends. So the statement is exactly "the windows cannot cover a whole period", LRC(8) for that arrangement. The
separation / transport lemmas describe each step exactly; the finishing step is global: `CoverB8`, `CoverC8` (the gap sits
at a grid-class instant of the arrangement's own grid).

**What is left, stated plainly:** Case B (spread 7–24): normalised shapes form a bounded region cut into finitely many
grid-class cells with uniform rules; `CoverB8` is a finite check; the wall-cut strips are generated and checked from 7 to
20 (strip `[19,20]`: 1,224 categories), 20–24 to run; a Lean translation of the strip certificates would give a complete
computer-assisted Case B; a derivation replacing them is still owed. Case C (spread above 24): not bounded; far fast
outliers are settled (`not_fast`, proved); what remains is slow runners far below a cluster, measured to be lonely within
the slow runner's first two blocks (E153–E154): the one piece of new mathematics still needed, the same shape as the band
theorem. Asked the owner which to put first.

---

## E164–E166 — 2026-09-28 — spread is irrelevant (owner); one spread-free covering `Cover8`; the retirement

**Owner:** *"No, don't you see that because of scale invariance and infinite grid the spread of 7–24 is irrelevant. Maybe
the condition that requires it is set up wrong."* It was: the Case B/C split at 24 came from the range of the old
certificates. Normalised by the grid (a reading's own scale, residues mod 8, deviations in `[−1/2, 1/2]`) the data is
spread-free: at the exact class instant reading `i` is clear iff `c·δᵢ ∈ [1 − rᵢ, 7 − rᵢ]`, independent of its lap and of
the spread. Magnitude re-enters only through relocation (a reading at a large grid point tolerates a relocation of about
`1/(c·n)`): the capture/separation mechanism.

**E164** (`LonelyRunner/experiments/nN/redo/m_vs_spread_v1/v2`, `capture_reference_v1`, exact): the needed grid fineness
`m` does not grow with spread: `m ≤ 3` at every spread 7–400; at 400–2,000 mostly 1–2 with a tail. The 19 sets needing
`m > 8` (up to 37) all have a captured runner (a multiple of `8 d_min`), and their working reference is the captured
runner's own grid (13 of 19) or the reading just above `d_min`, with `m` ≈ the captured runner's lap count at the bound
plus 2–5; their grid step is `≈ 5.6–7 d_min` (coarser than `d_min`).

**E165** (`redo/cover8_step_v1.{py,out,progress}`, exact, protected) `[VERIFIED — these populations]`: the spread-free
covering with the grid step at least `d_min/M`: Case B to 24 (210,335) all with step `≥ d_min`; Case C P1 every tenth set
(63,533) all `≥ d_min`; constructed residual C members (547) all `≥ d_min`; random wide spread to 2,000 (24,000) all
`≥ d_min`; random fine (10,000) all `≥ d_min`; late band shapes (5,400) all `≥ d_min/2` (they land in the nearest
runner's second block, which a step `≥ d_min` cannot reach: with the step at least `d_min` the nearest runner sits at grid
point 1, lap 0). **`Cover8 2`: none uncovered.**

**E166, in Lean** (`RegimeSkeletonN`, `LonelyRunner/` commit `1807df7`; Spec gate PASS **1,950**,
`experiments/nN/spec_gate_retire.out`): `GridStep8 S m M` (bound, or `GridClass8` through a reading `e` with
`mm·m ≤ M·e`); **`Cover8 M`** (registered OWED); **`lonelyRunnerAt8_of_cover8 : Cover8 M → LonelyRunnerAt8`**, every `M`,
no case split. **Retired:** `CoverB8`, `CoverC8`, `RegimeB8`, `RegimeC8`, `WithinTwoBlocks8` and their theorems (git
history before `1807df7`); `SlowestSkeletonN.CaseB8`/`CaseC8` marked off the path (still registered OWED for the record).
`Cover8` is the single owed statement of this route.

---

## E170 — 2026-09-29 — Lean review; `Cover8` card bound committed; band cover built; quantity tests before formalising

**Record gap.** `BandCover*N.lean`, `gen_band_lean_v{1,2}*.py`, `g1_cascade_v1.py` and `pair_sep_general_v1.py` cite
E167–E169; this log has no such entries. This entry does not fill them.

**Owner:** *"Can you please review the lean work for n=8"*; then *"Go ahead with both and do the tests for quantity before
formalising"* (both = commit the `Cover8` correction separately, then run the full Spec gate).

**Review findings** (`LonelyRunner/` source read-only until the commit below):
- **`Cover8` as committed at `1807df7` was false for every `M`**: it quantified over every `Finset ℕ`, and `{1,…,8}` has
  no instant at threshold `1/8` (of the nine points `0, t, …, 8t` two lie within `1/9`; their difference is `jt` for a
  reading `j` in `1..8`). `lonelyRunnerAt8_of_cover8` was never wrong; its hypothesis was unsatisfiable. The E166 entry
  and the 1,950 gate PASS (`spec_gate_retire.out`) certified that version; a gate cannot see a false `Prop` (the
  `DoorFirstLap` pattern). **Fixed: `LonelyRunner/` commit `3ea9feb`** (`S.card ≤ 7`; the fix only — the staged file was
  compiled off-tree first; `gridStep8_two_bounded` and `TwoBlock.exists_in_assigned_blocks` stay uncommitted).
- **What `Cover8 M` asserts** `[reasoned; exact check]`. Write NB(X) for "every set of at most seven positive whole
  numbers is lonely at some `t` with `8·d_min·t ≤ X`". Then **NB(M − ½) ⇒ `Cover8 M` ⇒ NB(8⌊7M/8⌋ + 7)**. Left: with
  `e = max S`, `mm = ⌊8et + ½⌋`, class `c = 1`, laps `⌊dt⌋`, every lonely instant with `8mt ≤ M − ½` is a `GridClass8`
  instance (0 failures in about 353,000 lonely instants; scratchpad `cover8_sandwich_v{1,2}`). Right, at `M = 2`: Lean,
  `gridStep8_two_bounded` (uncommitted). **Not an equivalence**: whether `Cover8 2 ⇔ NB(15)` is open; no tested set
  separates them. Below `R = M − ½` the grid and class clauses constrain nothing.
- **The band cover compiles.** Built one module at a time (about 53 min; the one earlier build log stops at 8251/8258,
  and the smallest module alone peaks at 7.9 GB). `LRC.BandCover.band_lonely`: seven real readings `1 ≤ s₁ ≤ … ≤ s₆`,
  `7 ≤ s₆ ≤ 9`, are lonely. **`[PROVED — Lean]`**: 289 of 289 declarations `[propext, Classical.choice, Quot.sound]`.
  Untracked; imported by nothing on a route to `LonelyRunnerAt8` (it settles the 7–9 part of `CaseB8`, off the path).
- The parallel session's commits `1526de6` (`PinchTransportN`), `33e1b5f` (`LapDeadlineN`), `f93fdd6`
  (`MixedLapOverlapN`) were axiom-checked independently here (33 and 13 declarations, all standard; no new `Prop`; they
  import only tracked modules).

**Two facts recorded for the termination question** `[reasoned from the definitions]`: (1) for whole-number readings
well-foundedness is automatic — every move lands on an opening `(k + 1/8)/d` (`Iteration.lean:37`), there are `Σd` per
unit of time, iterates strictly increase, and positions repeat after `t = 1`; so a non-isolating chain is exactly one that
runs a full period, and the free rank (`Σd`) is not scale-free. (2) For whole-number readings every pair's capture state
recurs with period `1/gcd(a, b)` (`HandoffDriftN.zero_drift_iff` with `(r, s) = (a/g, b/g)`), so a quantity of one pair's
state cannot decrease across a period. `lonely_iff_run_ends` (`Iteration.lean:770`) already proves termination ⇔
isolation (parallel session's correction: "remaining global step" is not a reduction).

**Quantity tests before formalising** (`LonelyRunner/experiments/nN/redo/quantity_tests_v1.{py,out}`,
`quantity_tests_v1b.{py,out}`, `quantity_tests_v1c.{py,out}`, commits `0b9e646`, `51e1214`; exact; spec fixed in the script's docstring before any data). A
candidate survives only if strictly monotone on every chain, well-founded, scale-free (`S` vs `3S`) and joint.
Candidates: Q1 readings in the way; Q2 lap groups; Q3 setter rank; Q4 setter lap; Q6 wait; Q7 total depth; Q8 horizon
of the clear readings; Q9 `MixedLapOverlapN` width deficit; Q11 openings left in the period (control).
- **Controls pass**: Q11 strictly decreases on every chain of every population and differs under scaling on 2,085 of
  2,085; the Lean consistency check (criterion certifies ⇒ `t_N ≤ P`; every chain ends within a period) has 0 violations.
- **No candidate survives** `[VERIFIED — these populations]`. Chains with at least two moves: Case B to 24 90,726; Case C
  sample (20,000 sets, readings ≤ 200) 8,358; late band shapes 5,400. Strictly monotone chains, Case B: Q1 9,985 (dec);
  Q2 5,015 (dec); Q3 47,047 (dec; 55,144 increasing transitions, the bridges); Q4 14,361 (inc); Q6 21,794 dec / 29,687
  inc; Q7 39,605 (dec); Q8 59,410 (inc); Q9 undefined (three or more unprotected clear readings) somewhere in 82,777.
  **Late band shapes: none of Q1–Q9 is strictly monotone on any of the 5,400 chains.** All of Q1–Q9 are scale-free (0 of
  2,085 differ). First violations are listed individually in the `.out`.
- **Chain lengths** (moves): Case B max 19 (`(1, 19, …, 24)`, a descending relay); Case C sample max 11; late shapes 17–25.
  Max `R*`: 5.667, 2.558, 10.835.
- **Pair recurrence** `[VERIFIED — these populations; the zero is forced]`: the same hand-off pair `(a, b)` recurs within
  a chain in 802 of 90,726 Case B chains and 4,882 of 5,400 late chains (E163); pair plus depth
  (`HandoffDriftN.depth8`) recurs in none. **That zero is forced by chain length** (`quantity_tests_v1c`, commit `51e1214`):
  all 977 Case B returns and all 8,909 late-shape returns come sooner than `1/gcd(a, b)`, and a zero-drift return needs
  `s·a = r·b` with `r ≥ 1`, so `r ≥ a/g` and the elapsed time is at least `1/g`. Every return is the nonzero-drift case.
  What stays open: a joint rank built from `repeated_capture_bounds_drift` (finitely many repeats of one lap-advance
  pattern with nonzero drift) across changing patterns and pairs; not tested here.
- **`MixedLapOverlapN` reach**: certifies somewhere in 16,057 of 90,726 Case B chains (at the last move in 9,765; two or
  more moves early in 186); late shapes 1,121 of 5,400 (last move 1,109; early 0).
- **Correction to E114's boundary note**: the `2k+1` cascade length on `(1, 5k−2, 5k, 10k−2)` is an **order-five** fact
  (threshold `1/5`: moves `2k+1` for even `k`, `2k+2` for odd `k` in this implementation's count; at `1/8` the same sets
  take 0–3 moves). No order-eight family with unbounded chain length is known from these runs.

**Gate.** Full Spec gate **PASS 2,338** declarations, axiom-clean, 87 `Prop`s all registered, tree stable (digest
`eaf210fdfe84`), 735 s (`LonelyRunner/experiments/nN/spec_gate_cover8_card.out`, commit `bc0ae6d`). **Scope:** the gate reads
the working tree, so it covers the untracked modules (band cover, `CascadeGridN`, `CascadeTransportN`, `HandoffDriftN`,
`HandoffResonanceN`, `ArrangementShapeN`) and the uncommitted `gridStep8_two_bounded` / `exists_in_assigned_blocks`.
HEAD's `RegimeSkeletonN` (fix only) was compiled separately off-tree, not gated as such. `Cover8` stays OWED.


---

## E171 — 2026-09-29 — the oracle's isolation incidents, and waves; cascade-checked; no density

**Owner:** *"yes run the wave-level test. Make sure it is backed up by cascade and [check you are not] trying to find a
density or something else creeping."* Then: *"Think about what we are trying to prove not what others have tried. It is
about boundaries, isolation incidents that we have an oracle for that works exactly and perfectly."*

(`LonelyRunner/experiments/nN/redo/wave_incident_v1.{py,out}`, `wave_incident_v1b.{py,out}`, commit `39c76d0`; exact;
checks fixed in the docstring before any data.) Populations as E170: Case B to 24 (210,335), Case C sample (20,000),
late band shapes (5,400).

- **The oracle, checked** `[VERIFIED — these populations]`: C1, the cascade's landing equals the first lonely instant
  computed without the cascade (linear-merge intersection of closed clear intervals): **0 violations** in all three
  populations. C2, every move type agrees with `SweepBridgeN` (faster next setter on a later lap, slower on the same or an
  earlier lap): **0 violations**.
- **No density.** Every quantity is read at a cascade state or at an incident (who opens, who closes, laps, readings in
  the slot, deadlines). Total depth and openings-left were dropped from E170's panel.
- **Waves** (chain cut at every bridge up; within a wave the setter's rank strictly falls, at most seven moves): **no
  wave-level candidate is strictly monotone on every chain** (readings in the way, start rank, end rank, wave length,
  opening setter's lap, horizon, lap jump). Waves per chain: Case B 1–9, Case C 1–7, late shapes 7–12. So neither a
  per-move nor a per-wave scalar organises the walk (E170, E171).
- **Incidents — the boundary structure** `[VERIFIED — these populations]`. Tight (single point: an opening boundary equal
  to a closing boundary) first incidents: Case B 37,908 of 210,335; Case C 1,932 of 20,000; late shapes 0 of 5,400.
  Hosts (the reading that opens at the incident) of every rank occur; late shapes are hosted by the nearest runner
  (2,311, at its second opening) or the fastest (2,605).
- **The grid label is not specific to the oracle's incident.** The lap assignment at the first incident is a
  `GridClass8` pattern (`e ∈ S`, `mm ≤ 4`, unit class) in 210,330 / 18,021 / 5,363 cases (the 5 Case B exceptions are
  six-reading crowds such as `(1, 19, …, 24)`, `R ≈ 2.2–2.6`); late shapes need only `(e = nearest, mm = 2, c = 5)`
  (`R` near 10) or `(nearest, 3, 3)` (`R` near 9). **Controls:** second incidents in the same `R` bin are covered at the
  same rates (Case B `[2,4)`: 6,635/6,640 first, 74,540/74,726 second; late `[8,16)`: 5,363/5,400 first, 5,400/5,400
  second); and **random instants that need not be lonely** fit the pattern at 99.96% for `R ∈ [1,2)`, 93.0% `[2,4)`,
  67.4% `[4,8)`, 41.3% `[8,16)` (Case B, every tenth set). Below `R = 2` the grid clause constrains nothing (as E170's
  sandwich predicted); above it the pattern describes lonely instants in general, first and second alike.

**Reading, in the owner's frame** `[reasoned from the definitions]`: the oracle only ever visits opening boundaries
`(8K + 1)/(8a)` and stops at the first one no window contains (the flank form, `ExistenceAt8_flank`, proved equivalent).
For whole-number readings, reading `d`'s window contains `a`'s opening exactly when `|(8K + 1)·d − 8la| < a` for some
integer `l`: every step of the walk is an exact residue test modulo `8a`, and an incident hosted by `a` is a multiplier
`u ≡ 1 (mod 8)` with `u·d mod 8a ∈ [a, 7a]` for every reading. A tight incident is an exact integer relation
`(8K_a + 1)·c = (8K_c + 7)·a` between two readings. E170–E171 rule out summaries of this test (scalars per move, per
wave, grid labels); what is left to study is the boundary test itself.

---

## E172 — 2026-09-29 — correction: E170–E171 imported the frame, and used pre-registration language on LRC

**Owner:** *"Pre-reg? Did you lose context, we do that for ecc/btc work not lrc. Although you slipping context maybe we
need it because at every time you want to try and retroactively turn it in to a density or coverage attempt"*

Yes. This session did not read `feedback-n8-cascade-is-the-oracle-2026-09-27` or
`feedback-n8-no-prereg-no-imports-2026-09-14` before working. E170 and E171 are built on the imported shapes both list:
- **Pre-registration language** on LRC: "fixed before any data was seen", survival criteria (E170, E171 docstrings).
  CLAUDE.md §2 scopes that to ECC/BTC work.
- **Termination by a decreasing quantity / well-founded rank** (E170's panel, adopted from the parallel session's
  suggestion; E171 Part B's waves). It says only *that* the cascade stops.
- **The finite-openings fence**: E170's "a non-isolating chain is exactly one that runs a full period" is the
  half-lap / finitely-many-openings shape (`exists_lonely_iff_half`, E100).
- **A move budget**: E171's "chain length ≤ 7 × waves; what must be bounded is the number of waves".
- **Coverage**: E171 Part A asked whether a grid label *covers* the incidents.
- **Density**: E171's random-instant control (proportions of uniformly sampled instants), against its own "no density"
  paragraph.
- E170's "correction to E114" was already on disk (the oracle memory: move counts refuted at order five,
  `experiments/nN/cascade_length_unbounded_v1.out`).

None of these names a place. **Read E170's quantity panel and "two facts for the termination question", E171 Part B, and
E171 Part A's coverage figures and both controls as off-frame: they are not steps.** Pre-registration did not protect
against this; the E170–E171 docstrings fixed their checks in advance and so fixed the imported question in place.

**What stands** (facts about named objects, not routes): the Lean review in E170 (`Cover8` card bound, `LonelyRunner/`
`3ea9feb`; the band cover builds and `band_lonely` is axiom-clean; Spec gate PASS 2,338; what `Cover8` asserts as
written); **the scripts are the cascade** (E171 C1, C2: 0 violations; the oracle confirmation the memory asks for); and
the late band shapes' landings as places: the nearest runner's second opening `9/(8·d_min)` in 2,311 of 5,400, the
fastest reading's opening in 2,605 (consistent with E100, E151).

Next work is under the memory's place test: a statement names the class of arrangements and the place the isolation is,
given by the readings, checked against the cascade; an exception is perturbed through the cascade.

---

## E173 — 2026-09-29 — the recurrence recorded in memory; corrections to E170–E172

**Owner:** *"yes move it to the top and record it"*.

- **Memory.** `feedback-n8-cascade-is-the-oracle-2026-09-27` was linked only from `feedback_INDEX.md`; it now heads
  `MEMORY.md` (with the no-prereg memory) and the n=8 section of `lrc_INDEX.md`. Both memories were revised through
  `memory-drafter` (isolated; raw artefacts and owner quotes only). What was added: the 2026-09-29 entry points (a parallel
  session's rank note adopted as the plan without the place test; pre-registration returning without the word, as checks
  and survival criteria "fixed before any data"; the owner's boundary/incident direction turned back into a rate); two
  shapes new to the list (a decreasing quantity or rank per move or per wave; a rate in place of a place); the place test
  applied to incoming notes and to a test script's pass condition; and, on the other side, CLAUDE.md §3 checks (the gate,
  `#print axioms`, E171's C1/C2) stay, and monotone facts proved about the cascade stay as tools.
- **Corrections found by the drafter** (each checked here):
  - E172 quotes E171 as saying "chain length ≤ 7 × waves; what must be bounded is the number of waves". That wording is
    not on disk anywhere else; it was chat. The on-disk form is `wave_incident_v1.py` line 36 ("a wave has at most seven
    moves").
  - E170 cites `Iteration.lean:770` for `lonely_iff_run_ends`; the theorem is at line 772 (770 is its docstring).
  - E171/E172's late-shape landings, 2,311 (nearest runner's second opening) and 2,605 (fastest reading's opening), sum
    to 4,916 of 5,400. The other 484 are hosted by ranks 1, 2, 4 and 5 (263, 46, 166, 9; `wave_incident_v1.out`).
  - E171's "Reading, in the owner's frame" (each step of the walk as an exact residue test modulo `8a`; an incident as a
    multiplier `u ≡ 1 (mod 8)` putting every `u·d mod 8a` in `[a, 7a]`) restates the flank form, `ExistenceAt8_flank`,
    already proved equivalent to the target. Under the place test an equivalent restatement is not a step; it is recorded
    as a restatement, not as a lead.

---

## E174 — 2026-09-29 — the place test on the boundary incidents

**Owner:** *"ok now apply the place test to the boundary incidents"*.

(`LonelyRunner/experiments/nN/redo/place_incidents_v1.{py,out}`, `place_incidents_v1b.{py,out}`, commit `58a9be6`;
exact.) Class: all 346,104 sets of seven distinct whole-number readings in `1..24` (E100's population). The incident:
the cascade's landing `t*` is an opening boundary `(8K+1)/(8a)` of a host `a`; the stretch that follows ends at the
first closing `(8L+7)/(8c)`. Oracle check: landing = first lonely instant computed without the cascade, 0 violations.

Place statements, each checked against the landing by exact equality:
- **S0, a named view** (E100's menu: bound, next opening `9/(8e)`, rung R1, nudge, reverse R1, ladder rung): **310,889**
  (bound 200,736; next opening 63,806; R1 37,438; reverse R1 7,847; ladder 1,062). E100 reproduced.
- **S1, a named view displaced by one separation**: the view `v` has a runner in the subject's slot; it leaves, and
  `t*` is its exit, `t* = move(v)` (E158; `SeparationN`): **31,318** (from rung R1 22,187, from a next opening 6,555,
  from a nudge 2,576; the runner that leaves is one of ranks 3–6 in 30,476 and ranks 1–2 in 842). None from the bound: a runner
  captured at the bound leaves at an R1 view, already S0.
- **S2, the stretch at a ladder rung** `a/q` (`q ≤ 8`): the incident's left boundary is the **latest opening at or
  before the rung**, `max_e (⌊e·a/q − 1/8⌋ + 1/8)/e`: **3,129 of the 3,897 incidents S0 and S1 miss** (rungs `1/8`
  1,053; `1/7` 827; `1/5` 785; `1/4` 245; `1/6` 198; `1/3` 15; `2/7` 5; `1/2` 1). Two forms, and only two
  `[reasoned from the definitions; confirmed on all 3,129]`: the rung is itself clear for every reading and lies
  inside the incident's stretch (**2,170**; the rung isolates and the cascade lands at the left end of the same
  stretch, which E100's equality test did not count), or the rung is obstructed and the stretch ends before it, closed
  by the reading in the way at the rung (**959**; obstructed ⟺ the closer is in the way at the rung, on all 3,129).
  Example: `(1, 2, 3, 4, 15, 22, 24)` lands at `25/176`, the opening of 22 on lap 3, and the stretch contains the rung
  `1/7` (`22/7 = 3 + 1/7` puts 22 just past its opening there).
- **Not yet placed: 768.** Listed in `place_incidents_v1b.out`. The first ones land on an earlier stretch before an
  obstructed rung, not the last one: `(1, 6, 15, 21, 23, 24, …)` at `41/184` (the opening of 23 on lap 5) below the rung
  `1/4`, where 24 is in the way; the latest opening before `1/4` (21's, `41/168`) is lonely too, but later.
- **None of the 3,897 is a single point.** Every one of them, moved one reading by ±1, lands at an S0 or S1 place for
  between 1 and 13 of its moves (`place_incidents_v1.out`), so they sit inside families, not at isolated coincidences.

---

## E175 — 2026-09-29 — the 768 through the cascade: rungs with q = 9, 10, 11, one separation

**Owner:** *"yes place the 768 through the cascade and see what is happen there"*.

(`LonelyRunner/experiments/nN/redo/place_768_v1{,c,d}.{py,out}`, commit `6be6f20`; exact.) The 768 incidents E174 left
unplaced, each traced move by move from the bound, perturbed one reading at a time, and tested against rungs `a/q` up to
`q = 40`.

- **All 768 are a rung displaced by one separation, at `q = 9, 10, 11`** `[VERIFIED — readings ≤ 24]`: the rung has a
  runner in the subject's slot; it leaves and the isolation is there (`t* = move(a/q)`). By nearest reading: `d_min = 1`,
  28 sets, rung `2/9` (`R = 16/9`); `d_min = 2`, 453 sets, rungs `1/11` (247) and `1/10` (206); `d_min = 3`, 287 sets,
  `1/10` (170) and `1/11` (117). None is a single point. Traces: the cascade walks up by single separations to the rung's
  neighbourhood and the last move is the exit of the reading sitting in the slot at the rung.
- **Why `q = 9` is where they start** `[reasoned from the definitions; confirmed on all 768]`: reading `d` is in the
  slot at rung `a/q` exactly when `|d·a − n·q| < q/8` for an integer `n`. For `q ≤ 8` that forces `d·a = n·q`, so only
  multiples of `q` can be there (this is why E100's rung R1 uses the multiples `D_q`, and why its menu, cut at `q ≤ 8`,
  was complete for them). For `q ≥ 9` a reading with `d·a ≡ ±1 (mod q)` also fits. At the 768's rungs every reading in
  the slot has residue `0` or `+1`: **exact multiples only in 261 sets** (E100's R1 view with `q > 8`, e.g.
  `(2, 3, 4, 14, 17, 22, 24)`: 22 = 2·11 on the rung `1/11`, leaving at `17/176 = 1/11 + 1/(8·22)`), **a reading one past
  the grid in 507** (the same place relocated by the deviation, e.g. `(2, 3, 4, 14, 17, 23, 24)`: 23 in the slot at
  `1/11`, leaving at `17/184`; `(1, …, 23, 24)` at `2/9`: 23 at `5 + 1/9`, leaving at `41/184`, `1/1656` after the rung).
- **The stretch form too**: every one of the 768 is also the stretch at a rung (least `q`: 9 in 689, 10 in 51, `3/13`
  in 28). The rung closes the stretch in 741 (the reading in the way at the rung closes it; residues `0` or `±1`) and lies
  inside it in 27.
- **Perturbation**: moving one reading by ±1 sends each of the 768 back to an E174 place (named view, one separation
  from one, or the stretch at a rung with `q ≤ 8`) for between 1 and 7 of its ranks (`place_768_v1.out`).

**The place test on readings ≤ 24, complete** `[VERIFIED — all 346,104 sets of seven readings in 1..24]`: every incident
has a place given by the readings. Named view 310,889; a named view displaced by one separation 31,318; the stretch at a
rung (`q ≤ 8`) 3,129; a rung with `q = 9–11` displaced by one separation 768. With the rung R1 family defined by the slot
condition `|d·a mod q| < q/8` rather than a cut at `q ≤ 8`, it takes both the multiples of `q` and the readings off the
grid by less than `q/8` (one off at `q = 9–16`, two off from `q = 17`). Scope: this is the population of readings ≤ 24;
the general statement is not tested beyond it.

---

## E176 — 2026-09-29 — the place statement on larger readings and the late band shapes

**Owner:** *"yes test it on larger readings and the late band shapes"*.

(`LonelyRunner/experiments/nN/redo/place_general_v1.{py,out}`, `place_general_v1b.{py,out}`, commit `f52df8d`; exact.)

**Scale.** E174–E175's rungs `a/q` were instants in absolute time, which is not scale-free: multiplying every reading
by `λ` moves the same place to a rung with denominator `λq`, and at the late band shapes' scale (nearest reading 27,720)
there is no rung of small `q`. Here the rung is a **position of the nearest runner**: the instant `a/(q·d_min)` at which
it sits at `a/q` of its lap. For `d_min = 1` this is E174–E175's rung; for any `d_min` every absolute rung with
denominator `q` is a nearest-runner rung with denominator at most `q`. Places, in order: the bound; a reading's next
opening `9/(8e)`; one separation from either; a rung itself, a rung displaced by one separation, or the stretch at a rung
(least `q` recorded). Oracle check (landing = first lonely instant computed without the cascade): 0 violations in every
population. Scale check (`S` against `3S`): 0 of 1,046 placed differently.

| population | sets | placed | largest least `q` | least `q ≥ 17` | not placed (`q ≤ 40`) |
|---|---|---|---|---|---|
| readings ≤ 24, all (control) | 346,104 | all | 11 | 0 | 0 |
| nearest reading 1, readings ≤ 32, all | 736,281 | all | 15 | 0 | 0 |
| random, readings ≤ 48 | 30,000 | all | 17 | 2 | 0 |
| random, readings ≤ 96 | 30,000 | all | 31 | 76 | 0 |
| random, readings ≤ 200 | 30,000 | 29,997 | 39 | 239 | 3 |
| late band shapes | 5,400 | all | 3 | 0 | 0 |

- **Late band shapes, all 5,400 placed with no rung finer than thirds** `[VERIFIED — these shapes]`: the nearest
  runner's next opening `9/(8·d_min)` (`R = 9`) 2,311; one separation from the bound or a next opening 1,568; the stretch
  at the nearest runner's position `4/3` of a lap (`R = 32/3`) 1,487; that rung displaced by one separation 34.
- **The needed `q` grows with the spread.** Every rung place with spread ≤ 24 has `q ≤ 16`; the `q ≥ 17` places occur
  at spread above 24 (2 at readings ≤ 48, then mostly spread above 64).
- **The 320 incidents needing `q ≥ 17` or not placed at `q ≤ 40` are one place** `[VERIFIED — these populations]`: in
  all 320 the readings in the subject's slot at the bound are within `d_min` of a multiple of `8·d_min` (captured at the
  bound); the isolation follows 2 to 8 separations from the bound (134 + 37 at two), landing just after it (`R` 1.01 to
  1.41). Example: `(1, 50, 105, 106, 136, 189, 199)`: 136 = 17·8 sits at the bound; when it leaves at `R = 1.0074`, 199
  is in the slot; when 199 leaves, isolation at `R = 201/199`. A large-`q` rung is the rung description of an instant
  just after the bound; the place is the bound's capture followed by the separations of the readings carried into the
  slot (E157–E158's leftovers; E161's transport), not a rung.

---

## E177 — 2026-09-29 — correction to E176's last bullet (a parallel session's review)

The parallel session reviewed E176 (owner relayed it; text not on disk) and reproduced the three unplaced examples
independently (all three isolate after exactly two moves, e.g. `1/8 →(136) 137/1088 →(199) 201/1592`). Two corrections,
both accepted:
- **The 320/320 is a definition, not a pattern.** At the bound `1/(8m)`, reading `d` is in the subject's slot exactly
  when `|d − 8Nm| < m` for an integer `N`. `place_general_v1b.py` line 43 tests that condition on readings already
  selected as in the slot, so it cannot fail. Every incident other than the bound has the bound obstructed, also by
  definition; and selecting `q ≥ 17` selects instants close to the bound (a rung near `1/8` needs a large `q`). What
  remains is an observation on these samples: those incidents finish in 2–8 moves just after the bound.
- **"The bound's capture followed by the separations of the readings carried into the slot" is not a place.** Without a
  restriction it is the cascade from the bound itself; E176's "one place, not a rung" is withdrawn. Likewise rungs with
  unrestricted `q` describe any rational instant; E176's growth of the needed `q` with spread is that effect.

The exact condition for the next step, from the review (same test as E171's reading): when setter `b` exits lap `K` at
`(8K+1)/(8b)`, reading `d` is in the slot exactly when `|(8K+1)·d − 8Lb| < b` for an integer `L`. The review's proposed
step ("force a terminal overlap within a bounded chain"; "why those chains cannot keep renewing") is the
that/when-it-stops shape (E172); it is flagged to the owner, not run. The place-test form of the same material: from the
residue condition, name which reading the bound's capture carries into the slot and where its exit is, for the class
where exactly one is carried and its exit is clear; check against the cascade; perturb the exceptions.

---

## E178 — 2026-09-29 — the isolation followed along the deformation from the AP: every event a pinch, none unprotected

**Owner:** *"yes run the deformation and pinch test"* (after the parallel session's direction, relayed: *"deforming the
AP moves isolation without destroying its existence"*; the replacement window to be derived, not assumed).

(`LonelyRunner/experiments/nN/redo/deform_pinch_v1.{py,out}`, `deform_pinch_v1b.{py,out}`, commit `043af1b`; exact.)
**The path** is `WindowPinchN`'s deformation in `ArrangementShapeN`'s coordinates: subject (the slowest runner) at 0,
span 7; target readings `S` give shape readings `x_i = 7 S_i / S_7`; along `s ∈ [0, 1]`, `d_i(s) = i + s (x_i − i)`,
the AP `1..7` at `s = 0`, the target at `s = 1`. At every step the cascade's first isolation, followed exactly (400-step
grid, events located by exact bisection, then `τ` solved from the tight pair constraint
`(8k_i+1) d_j(s) = (8k_j+7) d_i(s)`, linear in `s`). Scope: two events between neighbouring grid points whose effects
cancel on the landing are not seen.

**Forced by the definitions** `[reasoned]`: windows of different lap assignments are disjoint, so the first isolation
changes only when its window closes to a single instant (death) or a new window opens from a single instant before it
(birth); both are **pinches**. On a rational path each pinch parameter is rational, so the readings there have a common
period `P`; at a **simple** pinch (one reading on `+1/8`, one on `−1/8`, the rest strictly clear) `PinchOpenN` applies
(lonely on both sides). The local argument can fail only at a multi-pinch with no other open window.

| population | paths | events | simple / multi pinches | no other open window | unprotected |
|---|---|---|---|---|---|
| Case B to 24, every 100th | 2,104 | 8,900 (4,263 deaths, 4,637 births) | 8,668 / 232 | 2,104 | 0 |
| late band shapes, every 10th | 540 | 2,079 (1,961 / 118) | 2,079 / 0 | 540 | 0 |
| Case C sample | 500 | 5,902 (4,572 / 1,330) | 5,833 / 69 | 500 | 0 |

Oracle check (cascade landing = first lonely component, every tenth grid point): 0 violations in all three.
`[VERIFIED — these samples]`:
- **Every event is a pinch**: the tight window is a single instant at `τ` in all 16,881.
- **The events with no other open window are exactly the `s = 0` event of each path** (the AP, whose windows are all
  single points; a simple pinch; `P = 1`): matching counts on the full samples, and checked directly on subsamples
  (526 of 526, 135 of 135, 100 of 100 at `τ = 0`). **Every later event, 13,737 of them, happens while another window of
  positive width exists.** No unprotected multi-pinch in any sample.
- **At the AP start** the class-1 window at `1/8` dies at once in every path and the isolation moves to another φ(8)
  class: class 3 (lap change `⌊3i/8⌋`) in all 540 late shapes; class 5 or class 3 in Case B (lap changes
  `⌊5i/8⌋` 1,190, `⌊3i/8⌋` 952).
- **The mirror `P − t₀` is never the replacement** (0 of 10,796 deaths): an earlier window is always there.
- **Jumps** in `R = 8 d_min t` at deaths: up to 1.4 (Case B), 3.2 (late), 1.5 (Case C). The negative jumps (Case B 69,
  Case C 32) are a death and a birth at the same `τ`, the new window at `3/5` of the dying instant (`R` ratio `5/3` in
  every listed case).

**Reading** `[reasoned]`: along these paths the deformation never reduces the isolation to a single point after leaving
the AP; the local half ("a pinch does not destroy isolation") has, at every event found, one of two proved reasons —
`PinchOpenN` at a simple pinch, or another window of positive width. Not proved: that an open window always coexists at
every pinch after `s = 0` (the fact these samples show). Not addressed by this test: the global half, that the
relocations stay at bounded times along the whole path (E115/O5: `WindowBound` on the moves is the whole-number
conjecture).

---

## E179 — 2026-09-29 — the protecting window at each deformation event: a relay, not the AP's windows carried along

**Owner:** *"yes identify the protecting window at each event"*.

(`LonelyRunner/experiments/nN/redo/deform_protect_v1.{py,out}`, `deform_protect_v1b.{py,out}`, commit `9a07e0f`;
exact; same paths and events as E178.) At each event after `s = 0` the **protectors** are the windows of positive width
at `τ`. For a fixed lap assignment each pair condition is linear in `s`, so the parameters where it is a window form one
interval `[s_lo, s_hi]` `[reasoned]`. Hence "from the AP" is exact: the window exists at `s = 0`, i.e. it is the AP's
class window at `(8n+c)/8` with lap assignment `⌊i(8n+c)/8⌋`, and has existed all the way to `τ`; and an AP class window
survives the whole path exactly when its lap assignment is still a window for the target.

`[VERIFIED — these samples]`:

| population | events after `s = 0` | with a protector | protected by an AP class window | paths protected by one at every event | targets an AP class window survives to |
|---|---|---|---|---|---|
| Case B, every 100th | 6,796 | all | 4,361 | 1,001 of 2,104 | 313 of 2,104 |
| late band shapes, every 10th | 1,539 | all | 0 | 0 of 540 | 0 of 540 |
| Case C sample | 5,402 | all | 1,203 | 12 of 500 | 7 of 500 |

- The AP class windows that protect are all on lap 0 (classes 5, 3, 7). The target's first isolation is itself an AP
  class window in 87 Case B targets, 1 Case C target, no late shape.
- **So the protection is a relay**: AP class windows protect the start of many paths; windows born along the path take
  over, each born while others are open (every event after `s = 0` has a protector, E178), and in the late shapes the
  born windows carry all of it. The proposal "the protector is always an AP class window carried along" (E178's closing
  suggestion) is refuted on these samples.
- **The protectors are at named places** (subsamples, E174–E176's list applied to each protector's left end at `τ`):
  Case B, 20,974 protector instances, all placed (AP-origin at rungs with `q ≤ 7` bar 2; born mostly `q ≤ 8`, 669 at
  `q = 9–19`); late shapes, 2,598, all born, all placed with `q ≤ 7`, the commonest the nearest runner's second opening
  (`R = 9`); Case C, 75,695 (wide spreads have many windows), 1,600 not placed at `q ≤ 40` and the rest spread to
  `q = 40`. By E177, rungs with large `q` describe almost any instant, so the Case C naming is weak.

**Reading** `[reasoned]`: what the deformation shows is not persistence of the AP's own windows but a relay of windows at
named places, with a birth always ahead of the last open window's death (after `s = 0`, on these samples). The analytic
target this points to is the relay condition: along the deformation, whenever an open window is about to die, another
window is already open or is born first. Not proved; not addressed here: the global half (E178).

---

## E180 — 2026-09-29 — reflecting a pinch around the common period: a death is a birth, exactly, at every simple pinch

**Owner:** *"There may be a more general rule here: reflect a pinched isolation event around a common grid period. This
swaps the boundary runners, and the active inequality reverses sign—so the obstruction that kills the old window can
support the new o"* (message cut off).

**Derivation** `[reasoned from the definitions]`. At an event `τ` of the deformation (E178) the tight window, lap
assignment `k`, is a single instant `t₀`; at a simple pinch runner `a` is on `+1/8` and `b` on `−1/8`. The readings are
rational at `τ`; `P` is their least common period, `P·dᵢ(τ) = Nᵢ`, and `P > t₀`. At `P − t₀` every position is negated,
so `a` and `b` swap roles: the **reflected window** has `k'ᵢ = Nᵢ − kᵢ − 1`. With `g_k(s) = (8k_b+7)·d_a(s) −
(8k_a+1)·d_b(s)` the old window's active inequality, the reflected one is `g_{k'}(s) = g_k(s) + 8(N_a d_b(s) −
N_b d_a(s))`; the added term vanishes at `τ`, and with `eᵢ = dᵢ′`,
`g_k′ = (d_b e_a − d_a e_b)·(8k_a+1)/d_a` while `g_{k'}′ = (d_b e_a − d_a e_b)·((8k_a+1)/d_a − 8P)`. Since
`P > t₀ = (8k_a+1)/(8d_a)` the bracket is negative: **the slopes have opposite signs, so a death of `k` at `τ` is a birth
of `k'` at `τ`, and a birth of `k` is a death of `k'`.** The other readings keep their margin under reflection. This is
`PinchOpenN`'s mechanism (`TwoPinnerN.mirror_readings`, the sign dichotomy) stated for windows along the deformation.

**Checked** (`LonelyRunner/experiments/nN/redo/mirror_rule_v1.{py,out}`, commit above; exact; subsamples of E178's
paths: Case B every 400th, late band shapes every 40th, Case C first 100) `[VERIFIED — these subsamples]`:
- **Simple pinches, 3,161**: the reflected window is tight at `τ` at `P − t₀` in all, and behaves as derived (death ↔
  birth) in all 3,161.
- **Multi-pinches, 69**: tight at `P − t₀` in all; pair as derived in 28; the other 41 are windows that exist at the
  single parameter `τ` only (the original and its reflection both), neither a death nor a birth.
- **The reflected window is far**: median `R = 8 d_min (P − t₀)` 150 (Case B), 782 (Case C), 1.2 million (late shapes),
  against the original's median 1.75, 1.00, 4.24. So it is never the first isolation (E178: 0 of 10,796 deaths).

**What it gives** `[reasoned]`: along a rational path, **the relay condition of E179 holds at every simple pinch**, by
derivation, not observation: no simple pinch can remove the last window. What it does not give: bounded times. The
reflected window's laps grow with `P`, and approaching a parameter where windows accumulate the periods grow without
bound; so the global half (E178; E115/O5) is untouched by reflection, and the isolation near the first one is carried by
the born windows at named places (E179). Left open by this entry: multi-pinches (the 28 that pair and the 41
single-parameter windows need their own statement), and the bounded-time half.

---

## E181 — 2026-09-29 — partial reflection in Lean; every simple pinch has a partner at the same parameter

**Owner:** *"yes put the reflection identity in Lean and test it"*; and *"Could there be a series of pinches interacting
between the other 6 so its like an orchestrated overlapping pattern?"*

**Already in the tree, from the parallel session** (uncommitted when read): `LRC/Spec/PinchReflectionN.lean`, the full
reflection around a common period `(λ+1)t` of every reading — reflected labels `Pᵢ − qᵢ − 1`, every active slack's slope
reversed with factor `−λ` (`active_slope_reversal`, including simultaneous pinches), and an actual right neighbourhood
of reflected windows (`reflected_right_windows`). Not duplicated. Its slope identity uses only the two active readings;
its window theorem needs every reading whole at `(λ+1)t`.

**New in Lean: `LRC/Spec/PartialReflectionN.lean`**, `partial_reflected_right_inequalities`: reflect only the readings in
`R ⊆ S` (each whole at `(λ+1)t`, e.g. just the pinching pair around its own period); every other reading keeps its own
label and must be strictly clear at the reflected instant `λt`; then the new labels satisfy every pairwise window
inequality on a right neighbourhood. The one new step: at `λt` a slack is zero only if both readings sit on boundaries,
and unreflected readings are strictly inside, so every zero slack is between reflected readings. `[PROVED — Lean]`,
`[propext, Classical.choice, Quot.sound]`. **Tested on a real event** (`experiments/nN/partial_reflection_axioms_v1.lean`,
`real_event_instance`): the death at `τ = 23/37` on the path to `(1, 7, 12, 15, 17, 18, 23)`, pair period `37/42`,
`λ = 3/5`, every hypothesis discharged by computation; axiom-clean. **Spec gate PASS 2,365** declarations, 139 modules,
tree stable (`experiments/nN/spec_gate_partial_reflection.out`). **Not committed**: `PartialReflectionN` imports
`PinchReflectionN`, which imports `SymbolicWindowTransportN`; both are the parallel session's and uncommitted, so they go
in first.

**Against the cascade** (`LonelyRunner/experiments/nN/redo/partial_reflection_v1{,b}.{py,out}`, commit `47c77de`; exact;
E178's paths, subsamples) `[VERIFIED — these subsamples]`:
- **Deaths**: at every simple-pinch death, 1,712 of 1,712, a partial reflection around the pinching pair's own period
  with the other five strictly clear exists within 21 multiples; its labels form a window just after the pinch, born
  exactly there, in 1,712 of 1,712 (the theorem's conclusion on real data).
- **Births**: at every simple-pinch birth, 1,449 of 1,449, the partner is a window that dies at the same parameter.
- **Place test**: the partner is the cascade's replacement in 29 of 1,712 deaths, exactly E178's simultaneous events
  (a window dies and an earlier one is born, `R` ratio `5/3`, first multiple of the pair period).
- **Distance**: death partners at median `R` 23 (Case B), 67 (late shapes), 23 (Case C), against the full reflection's
  77.5, 1.27 million, 647; birth partners in the late shapes at median 6.2 (first multiple in 23 of 24).

**Reading** `[reasoned; the pairing verified on these subsamples]`: pinches come in **linked pairs**. Every simple pinch
has a partner of the opposite kind at the same parameter, at `Q − t₀` with `Q` a multiple of the pinching pair's own
period, and the other five readings clear there: an overlapping pattern set by the pair, with the other five's clearance
as the condition. The pairing gives the relay condition at every simple pinch with a partner far nearer than the full
reflection, but still not at bounded times; what keeps the first isolation close remains the windows already open
(E178–E179), and the bounded-time half stays open.

---

## E182 — 2026-09-29 — where the isolation goes when its window dies: exhaustive three cases; what the relocation forces and what it does not

**Owner:** *"yes run the three-case relocation test if you tell me why it matters. We are trying to determine how the
cascade is forced to show n=8. Does the relocation help us? then yes do it"*.

**Why it matters** `[reasoned]`: `lonely_iff_run_ends` makes n = 8 the statement that the cascade always stops. Along the
deformation from the AP (isolated) to a target, the cascade's landing changes only at pinches (E178); a birth moves it to
the newborn window's instant; a death is the only moment the isolation could be lost, so the relocation at a death is the
step that has to be forced.

**The three cases** `[reasoned from the definitions]`: at a death runner `a` sits on `+1/8` (leaving) and `b` on `−1/8`
(entering) at the dying instant `t₀`; just after, `b` closes before `a` opens, so their windows overlap and cover
everything from `a`'s entry to `b`'s exit `T_b`. So the new first isolation is at `T_b` (case 1, `b`'s separation, E158),
earlier than `t₀` (case 2, a window born at the same instant, E181), or later than `T_b` (case 3, a reading in the way at
`T_b`, carried there by the shift, E161).

**Checked** (`LonelyRunner/experiments/nN/redo/relocation_death_v1.{py,out}`, commit `f41cbc0`; exact at `τ + 10^-15`;
E178's full samples; simple pinches) `[VERIFIED — these samples]`:

| population | simple deaths | case 1 | case 2 | case 3 | isolation between `a`'s opening and `T_b` | paths with no case 3 |
|---|---|---|---|---|---|---|
| Case B, every 100th | 2,052 | 524 | 69 | 1,459 | 0 | 1,084 of 2,104 |
| late band shapes, every 10th | 1,421 | 107 | 0 | 1,314 | 0 | 0 of 540 |
| Case C sample | 4,014 | 1,233 | 31 | 2,750 | 0 | 8 of 500 |

Case 3: the readings in the way at `T_b` are usually one (1,099 / 847 / 1,754), faster than `b` only, slower only, or
both; the cascade from `T_b` reaches the landing in 1 to 14 moves; the jump in `R` beyond `T_b` has median 0.35 / 1.71 /
0.09, maximum 3.0 / 6.1 / 2.3. Note: a different, older `relocation_v1.py` (commit `87dac69`, 2026-09-25, relocation
factor against the fitted AP) exists; it was overwritten in the working tree by mistake during this entry and restored
from `HEAD` before anything ran.

**What the relocation forces** `[reasoned from proved pieces]`: in cases 1 and 3 there is no isolation before `t₀` just
after the death, so the new landing is the cascade restarted at the dying instant (the cascade reaches the least lonely
instant above its start, `first_isolation_of_fixed`, `iterate_le_of_lonely`). That restarted cascade is forced to stop no
later than the reflected window: the partial partner when the other five are clear at `Q − t₀` (`PartialReflectionN`),
the full reflection `P − t₀` always (`PinchReflectionN.reflected_right_windows`). So every event along a rational
deformation is forced: a birth jumps to the newborn instant; a death restarts the cascade, which passes `b`'s exit and
stops no later than the reflection.

**What it does not do**: a single separation is the minority (case 1: 26%, 8%, 31% of simple deaths); in general the
relocation is the cascade restarted, not one named step. And the proof by deformation now needs exactly one global fact,
finitely many events along the path; given the local facts that is the same as the landing staying at bounded times on
the path, which is O5's statement in another form, equivalent to the conjecture as a bare bound. In the framework's
terms the owner's principle, that isolation can fail only if two runners share a speed, is what would have to supply it:
along the order-preserving path the speed ratios stay away from equality, and the separation lemmas already on disk
(`sweep_lap_bound`, E127's crowd run-out) bound separation per pair by the ratio gap. Not attempted here.

---

## E183 — 2026-09-29 — making the pairwise separation bound control the restart: it does, exactly when there is no bridge up

**Owner:** *"yes try making the pairwise separation bound control the restart"*. (A bound on the restart is the
when-at-the-latest shape of E172; done at the owner's direction, stated in the framework's own objects: the cascade's
move types and the separation lemmas in the tree.)

**Derived** `[reasoned from SweepBridgeN]`: the restart after a death (E182) is cascade moves; each setter relative to the
previous one is a sweep (slower, same lap), a bridge down (slower, earlier lap) or a bridge up (faster, later lap).
Between bridges up the setter's rank strictly falls, so the restart has at most `7 (U + 1)` setters, `U` = bridges up.
Sweeps are bounded pair by pair (`sweep_lap_bound`), same-lap groups separate by `t < 1/(4(a − b))`
(`same_lap_separation_time`), and a pair's repeated bridges are bounded by its drift
(`HandoffDriftN.repeated_capture_bounds_drift`). **A first bridge up is not a separation failure**: a faster `b` is in the
slot at `a`'s exit exactly when `(8k+1)·b mod 8a` is within `a` of 0, a residue coincidence no speed gap bounds.

**Checked** (`LonelyRunner/experiments/nN/redo/restart_bridges_v1.{py,out}`, commit above; exact; every case-3 restart of
E182) `[VERIFIED — these samples]`: all 5,523 restarts reach the landing, satisfy the `7 (U + 1)` bound, and every sweep
step is within the pair bound.

| population | case-3 restarts | no bridge up | bridges up per restart | same pair bridging up twice |
|---|---|---|---|---|
| Case B, every 100th | 1,459 | 385 | 1: 736, 2: 264, up to 6 | 2 |
| late band shapes, every 10th | 1,314 | 141 | 2: 458, up to 8 | 2 |
| Case C sample | 2,750 | 841 | 1: 1,379, up to 6 | 7 |

**Reading** `[reasoned; counts as above]`: the pairwise separation bounds control the restart exactly when it has no
bridge up (26%, 11%, 31% of the case-3 restarts). The rest extend through bridges up between distinct pairs; repeats of
one pair, where the drift bound bites, occur in 11 of 5,523. So speed gaps cannot control the restart in general: what
extends it is which faster readings sit in the slot at a setter's exit, a condition on the readings' residues
`(8k+1)·b mod 8a`, i.e. on the arrangement's own grid, not on how close two speeds are. Any control of the restart would
have to come from that residue structure.

---

## E184 — 2026-09-30 — corrections after re-reading memory and the log: E178–E183 re-derived E113–E115 without citing them; two in-place edits

**Owner:** *"You just compacted you context, please read you memory (not grep) you can skim scan handover, manuscrip and
paper document though"*. Read in full: `feedback-n8-cascade-is-the-oracle`, `feedback-n8-no-prereg-no-imports`,
`feedback-n8-obligation-is-loneliness`, `feedback_document_cadence_running_log`, `project-n8-cascade-function-sources`,
`project-n8-tight-instances`, `lrc_INDEX`, `feedback_INDEX`; skimmed handover v10, `MANUSCRIPT_v21` §0 and §17,
`PAPER_v9_1`; read E52, E112, E113.

1. **E178–E183 re-derived the owner's path route and did not cite it** (O2/O3 again: read the log's treatment of a route
   before deriving). Already on record:
   - E52: the proof is the deformation argument (global isolation at the AP; survives small changes; what is owed is that
     the relocated isolation cannot escape to infinity, *"bounded by the speeds of the arrangement"*).
   - E112: `DeformationN.lonely_along_path` (Lean, 2026-09-26) owes two hypotheses along every path from the AP: local
     stability and the window.
   - E113: at a simple pinch the wall lemma is the mirror (same pair, roles swapped, opens on the other side); the path
     route owes (A) no lonely whole-number arrangement has only multi pinches, (B) the window. Checked there: multi
     pinches only, 0 of 346,104 sets `≤ 24`.
   - E114 `PinchOpenN`; E115 `LonelyRunnerAt8 ⇐ WindowBound` (`PathWindowN`), O4 one runner at a time avoids multi
     pinches, O5 the continuum carries nothing across a whole-number point.
   So E180's reflection is E113 item 3 (mirror), E178–E182's "local half / global half" is E113's (A)/(B), and E182's
   "one global fact" is (B), `WindowBound`, which E52 names as the owner's bound, not an import. **New relative to that
   record:** `PartialReflectionN` (Lean, reflection around the pinching pair's own period, the others strictly clear;
   E181; generalises the mirror from the full period); E178's straight-path counts (after `s = 0` every pinch had another
   open window, 13,737 of 13,737 on samples); E182's three exhaustive relocation cases at a death; E183's decomposition.
2. **Two in-place edits of this log, against its append-only rule** (`feedback_document_cadence_running_log`): E174's
   figure for the separating runner's rank (29,826 changed to 30,476; commit `cf60341`) and E175's stretch-form line
   (commit `363862c`). Both corrected true figures, recounted from the `.out` files; they should have been appended as
   corrections. Recorded here; no further in-place edits.
3. **E183's target was a cap** (a bound on the restart), a shape `feedback-n8-obligation-is-loneliness` and
   `MANUSCRIPT_v21` §0 list as foreign. It was flagged (E172 shape) and run at the owner's direction; its result is a
   record of which restarts the pairwise lemmas control, not a target to pursue.

---

## E185 — 2026-09-30 — the window (B): what it is on the path route, and the target's event read on the last move

**Owner:** *"work on the window (B) on the path route making sure it is compliant to the framework, no density, no
coverage, boundaries and isolation events and cascade as the oracle"*.

**What (B) is on the path route** `[reasoned from the Lean statements and E116]`: `PathRouteN.segment_lonely` needs the
window only along one move (one runner moving, six fixed at rational readings), and `DeformationN.lonely_along_path`
uses it only for closedness. On a move: off the lattice of the six, `OneFreeN.lonely_of_one_free_eight` places the event
(order seven on the six, then stepping); at a lonely lattice point, `move_one_strict` / `move_one_period` keep nearby
points lonely at that point's own instant or its mirror, inside its period, so the bound is free there; at a lattice point
that is not lonely the instants escape like `1/ε` (E116). So (B) on a move is loneliness at its lattice points, and there
is no separate escape to rule out. The target is a lattice point of the last move (O5, E116). **So (B) at the target is
the target's own isolation event, seen from the last move**: six readings fixed, the seventh arriving.

**Read on the last move** (`LonelyRunner/experiments/nN/redo/last_move_v1.{py,out}`, commit above; exact; all 346,104 sets
of seven readings in `1..24`; any runner may be moved last, E115 O4). The six fixed readings have their own clear set `F`
at `1/8` (native order seven clears them at `1/7`, so `F` has intervals with room). The target's event `t*` (the cascade's
landing on all seven) lies in one of `F`'s intervals, index `j` in time order `[VERIFIED — readings ≤ 24]`:
- **Mover = the fastest reading**: `j = 1` (the six's first clear interval) in 309,156; `j = 2` 35,218; `j = 3` 1,673;
  `j = 4` 54; `j = 5` 3. The event is that interval's left end (a boundary of the six, the mover clear there) in 316,874
  and the mover's opening inside it in 29,230.
- **Best mover**: some choice of mover gives `j = 1` in 345,133 sets; the least `j` is 2 in 958 and 3 in 13. The 971 sets
  where every choice gives `j ≥ 2` are listed in the `.out` (first: `(1, 3, 4, 5, 6, 7, 8)`, `R* = 25/7`).
- Each `F`-interval before `t*`'s lies inside one slot of the mover: 0 exceptions. **This is forced** (a connected
  interval inside the mover's in-the-way set lies in one of its disjoint slots), a consistency check, not a finding. The
  R8 check (a mover faster than 7 times every fixed reading gives `j = 1`) was **not exercised**: no set with readings
  `≤ 24` has such a mover.

**Reading** `[reasoned; the counts are this window's]`: at the target, (B) is the place statement *the target's event is
in the first clear interval of the other six that the mover's slot does not swallow*; an interval `[a, b]` of `F` is
swallowed exactly when `x·a` and `x·b` lie within `1/8` of one whole number `k`, a boundary condition on the mover's
reading `x` against the six's own clear interval. In 345,133 of 346,104 sets some mover leaves the six's **first** clear
interval open, so the event is named by the six's own first isolation (a lower-order object) and one boundary comparison.
The 971 sets where every mover swallows the first interval are the exceptions to that statement; per the place test they
are to be perturbed through the cascade next.

---

## E186 — 2026-09-30 — the parallel session's double-and-backtrack rule, checked

**Owner:** relayed the parallel session's rule (`LonelyRunner/experiments/nN/redo/double_backtrack_selector_v1.md`,
`LRC/Spec/DoubleBacktrackN.lean`, uncommitted) and asked for it to be checked.

**The rule** at a dying window's pinch `t` (old labels `qᵢ`, phases `fᵢ ∈ [1/8, 7/8]`): `pᵢ = 2qᵢ + [fᵢ ≥ 9/16]`, the
last opening at or before `2t`; `T = maxᵢ (pᵢ + 1/8)/dᵢ`; a window exactly when the largest need is at most the rollback
`2t − T`. `[reasoned]` The algebra holds: at `2t` a phase `f` becomes `2f mod 1`, clear exactly when `f ≤ 7/16` or
`f ≥ 9/16`, so only phases strictly between those can be in the way, and the upper bounds at `T` are exactly the need
inequality.

**Checked** (`LonelyRunner/experiments/nN/redo/double_backtrack_check_v1.{py,out}`, commit `d3f4163`; exact):
- The Lean module builds and its 17 audited declarations use only `[propext, Classical.choice, Quot.sound]`
  (`experiments/nN/double_backtrack_axioms_v1.lean`, run here). Not gated, not committed.
- The worked example reproduces exactly (`p = (0,1,2,2,3,4,5)`, `T = 41/56`, `δ = 303/7336`, largest need
  `212775/11326784`, parameter range `[199/738, 2189/2539]`), and so does the failure case (rollback `1/56` against need
  `231/776`).
- On E178's subsampled paths (1,712 simple deaths, a population independent of the md's 459): the rule's test is exact
  (strict ⇒ a window just after the pinch, every case; fails ⇒ not, every case). Strict 267 of 511 (Case B), 87 of 350
  (late band shapes), 532 of 851 (Case C).
- **Place test**: the rule's window is the cascade's replacement (the new first isolation) in 61 of 267, 20 of 87 and 25 of
  532 strict cases, and it is never earlier than the dying instant. So it names **a** window that survives the pinch, not
  where the cascade goes.
- **Frame**: native (openings, the pinch, exact inequalities; no density, no coverage). Two presentation points against the
  owner's standing rule on positive speeds: `region_lonely` puts the subject at speed `0` (`Fin.cases 0 …`), and the md
  writes the target as speeds `(0, 1, 50, …)`; state it with the subject at a positive speed (`lonelyAt_add_const`) and
  write the target as the subject's readings `(1, 50, 105, 106, 136, 189, 199)`.

**Where it sits** `[reasoned]`: a surviving window at a pinch is local stability, which the path route already has
(`PinchOpenN`, `PinchReflectionN`, and `move_one_period` on one-runner moves). The rule's window is nearer than the
reflection's (`T < 2t` against `P − t`), but by E116 the window (B) is not about the replacement's distance: on a move it
is loneliness at the lattice points. The md's next branch (derive a different window from the two conflicting readings)
is again local stability; it does not bear on (B).

---

## E187 — 2026-09-30 — the 971 of E185 through the cascade: every runner has a near-miss before the isolation; the event is read at the host, which is Theorem 6.15's form

**Owner:** *"yes run the 971 through the cascade"*.

**Scripts** (`LonelyRunner/experiments/nN/redo/`, commit above; exact): `swallow_971_v1.{py,out}` recomputes the 971 from
all 346,104 sets (list in `swallow_971_v1_sets.json`) and traces each; `swallow_971_v1b.{py,out}` is the second pass.
Oracle check (landing = first lonely instant computed without the cascade): 0 violations.

**The object** `[reasoned]`. Before `t*` the seven are clear nowhere, so any clear interval of six of them (runner `m`
removed) that ends before `t*` has `m` in the way throughout, and a connected closed interval where `m` is always in the
way lies in **one** slot of `m`, lap `k`: `(k − 1/8)/m < a ≤ b < (k + 1/8)/m`. Call it a **near-miss** of `m` (six
clear, one runner alone in its slot). E185's "the mover swallows the six's first clear interval" is exactly *the mover
has a near-miss before `t*`*, and the 971 are the sets where **every runner** has one. Checked: each first near-miss in
one slot, 0 violations; the seven first near-misses pairwise disjoint (derived: in one `m` blocks and `m'` is clear), 0
violations.

**Why each runner swallows** `[VERIFIED — the 971]`:
- **The slowest**: its first near-miss is its **lap-0 slot, before the bound** `1/(8 d_min)` in all 971. That is forced
  by the bound (the slowest is in the way from the start until `1/(8 d_min)`), and the cascade, which starts at the bound,
  never sees it. It happens whenever the other six are clear somewhere before the bound, which puts `d_min ∈ {1, 2, 3}`
  here (370, 290, 311).
- **The other six** (5,826 first near-misses): at one of their own returns, lap `k = 1` in 3,396, `k = 2` in 1,461, up to
  `k = 7`. In 3,626 the near-miss contains `k/m`, the instant `m` is exactly at the subject; there the others read
  `(d·k mod m)/m`, so **the six are clear at `k/m` exactly when every other reading has `d·k mod m ∈ [m/8, 7m/8]`**, a
  residue statement mod `m`. Checked against "contains `k/m`": 22 disagreements, each a slot of `m` holding **two** clear
  intervals of the six with `k/m` in the second (e.g. `(1,3,4,5,7,12,16)`, `m = 5`: `[17/96, 23/128]` and
  `[25/128, 7/32] ∋ 1/5`), so the equivalence holds for *a* near-miss in the lap-`k` slot, not necessarily the first.
- The dominant time order of the first near-misses is the slowest (lap 0), then **fastest to slowest** (218 sets): the
  first returns `≈ 1/m` in order of speed.

**The cascade walks them** `[VERIFIED — the 971]`: of 8,454 moves from the bound, 7,193 have exactly one reading in the
way, and each such move is inside a near-miss of that reading or is the last move, exiting to `t*` (0 exceptions;
derived). At a visit the move is the blocker's own opening. In 186 sets **every** move is single-blocker: the cascade is a
chain of near-misses, each left through its blocker's opening, landing in the next (trace of `(1,3,4,5,6,7,8)` in the
`.out`: `8, 7, 6, 5, 4` a sweep on lap 1, then `7, 3, 8, 5, 7`, landing at `t* = 25/56`, 7's opening on lap 3).

**The target's event, read at the host** `[reasoned; checked]`: 949 of the 971 have one host `h` (a single reading
opening at `t*`), 22 have two. With one host, the six others are clear on `[c, t*]` with `c` **inside `h`'s slot** (if `h`
entered its slot at a clear instant of the six, the seven would be clear before `t*`); 0 violations. So the event is: a
**last opener** opens at `c` while `h` is still in its slot, and `h` leaves at `t* = (K + 1/8)/h` with no reading closing
in between. That instant is the flank opening at the **candidate scale `h/(8K+1)`** (§6.10, `flankOpening_eq_spine`), `h`
is clear there by construction (Theorem 6.16), and the content is the other six: **Theorem 6.15's own form**. The cascade
has a move at `c` in 656 of 949.

**Place of `t*`** (E174's places plus E175's stretch at a rung `q ≤ 8`): 970 of 971 are named: `S0 R` 350, `S1 R` 328,
`S0 L` 79, `S2` at `1/4, 1/5, 1/8, 1/3, 1/6, 2/7, 1/7, 1/2` 174 in all, `S1 O` 19, `S0 O` 11, `S1 N` 9. One,
`(1, 8, 11, 18, 19, 20, 21)`, is in E175's 768 (placed there by a rung with `q ≤ 11`).

**What this settles for (B) at the target** `[reasoned]`: the 971 are **not a separate kind of isolation event**; their
`t*` is at the same named places as the rest. The first-interval reading of E185 is not a statement that holds for all
sets: it fails as soon as the mover has a near-miss before `t*`, and in the 971 every runner has one (the slowest by the
bound). The reading that is stated for every set is at the host: `t*` is `h`'s opening, the six others clear on a
stretch starting inside `h`'s slot. That is the obligation of record (Theorem 6.15) read at the cascade's landing. So on
the path route, (B) at the target is **Theorem 6.15 at the host's candidate scale**, and the last move adds the stretch
`[c, t*]` and its last opener; it does not add a weaker statement.

**The parallel session's multipliers** (relayed, their files not on disk): at a clear instant, a phase `f ∈ [1/8, 7/8]` is
in the way at `m·t` exactly when `m f` is within `1/8` of a whole number. For `m = 2, 3, 5` those ranges are pairwise
disjoint `[VERIFIED — exact, all pairs in 2..7]`; `{2,4}`, `{2,6}`, `{2,7}`, `{3,6}`, `{3,7}`, `{4,5}` and the rest with
6 or 7 overlap. So each reading blocks at most one of `2t, 3t, 5t`, and one of the three has at most two blockers among
seven readings. It is stated at a clear instant (the old pinch), so it is the replacement after a pinch, local stability
(`hopen`), and it does not bear on (B).

---

## E188 — 2026-09-30 — method: the cycle read from the record; the cascade side and the case list are one object; the landings in rung coordinates

**Owner:** *"yes run the landings through the cascade in residue form / I feel like we keep doing the same thing.  we
propose a a why, check it against cascade and find an exception that rules it out.  But are we understanding why the
exception happens, are we trying to tie all these hints clues of what is happening together.  Are we mapping  things so
we understand before proposing a the mechanisim.  We know cascade never fails, we just need to know how so we can prove
it rather than observe it.  We need to reason through our methodology and especially our repeated attempts to see what
can break us out of the cycle."*

### The cycle, from the record

- **It has been named before.** O10 (E162, owner 2026-09-28): general mechanisms taken for small distinct ones, regime
  lists extended item by item whenever something leaked. It recurred after that: E174 (places, misses), E175 (the 768),
  E178–E183 (deaths, protecting windows, reflection, relocation, restart), E185 (the last move, the 971), E187. Each
  began from a new vantage, stated a rule the majority obeys, and ended on its exceptions. E184 already records that
  E178–E183 re-derived E113–E115.
- **Three times an exception set folded back into one structure, and the structure was not named as the object.** E103
  and E174: the later openings are one separation from a view. E175: the 768 are rungs with `q = 9, 10, 11`. E187: the
  971 land at E174/E175's places.
- **E187's proposed next step was already on disk.** The band `d(8k+1) mod 8e ∈ [e, 7e]` is v21 §15's bridge
  `lonely_eight_of_opening`, proved. The rule "flank = the least multiple of `q`" is v21 §17E's rung-selection rule
  (`LonelyRunner/experiments/nN/rung_selection_v1.out`: it certifies 91,523 of 91,523 v1 residual sets on `[1,40]`, least
  `q` up to 16). §17D records that the `q` needed grows with the window, so no fixed list closes the residual.
- **Forced facts were found after the data, one round each**: E176's 320/320 (E177), E185's one-slot check, E187's
  "`c` inside the host's slot". Each was derivable before running.

### Why it recurs `[reasoned from the record]`

1. **The object mapped was the first isolation.** E109 O1: the cascade gives *a* lonely instant, and "first" is a
   by-product (`first_isolation_of_fixed`), not the obligation. The first isolation's place depends on which host happens
   to open first, so every place rule for it has exceptions (the map below: it is a structured rung's first certified
   instant in 61 of the 145,368 sets where the bound is blocked).
2. **Vantages came from the Lean route's needs** (`hopen`, (B), the path route) **or from incoming notes, not from the
   map.** The cascade side (E100–E187) and the case-list side (v21 §15–§17E) were not read as one object, so each side
   re-found the other's families.
3. **Exceptions were used to rule a statement out, not to read the mechanism.** `methodology_understand_exceptions`
   steps 2–4 (what forces the witness there; is it the main mechanism in disguise) were skipped; when an exception folded
   back, the fold was logged and the vantage changed.
4. **There is no living map.** The record is an append-only log of more than 6,000 lines; each round starts from the
   latest entry.

### The tie `[derived; Lean pointers from E162 and v21]`

One mechanism, E162's (1) and (2). At a grid instant `i/q` (`gcd(i, q) = 1`), a non-multiple of `q` reads a nonzero
multiple of `1/q`, so for `q ≤ 8` the subject's slot holds exactly the readings divisible by `q`
(`GridPairLawN.grid_class_clear`); they separate, the least one last, at `i/q + 1/(8e)`, `e` the least multiple
(`SeparationN.lonely_of_separation`), and a multiple then reads as at `e`'s first opening, clear iff `d mod 8e ∈ [e, 7e]`.
Instances already on disk: `q = 1` from `0` is the bound and R1; no multiple of `q` is R6; E100's rung views; §17C's
rational openings; §17E's rung-selection rule. And every cascade landing (derived below, D1–D2) is this mechanism at its
own `q_c = h/gcd(h, K)`. The cascade from the bound is the mechanism at `q = 1`; when that fails it keeps moving, and its
landing is usually at full resolution (`q_c = h`), where §17D says the list "is the obligation again".

### The landings in rung coordinates

`LonelyRunner/experiments/nN/redo/rung_map_v1.{py,out}` (commit `8101b8a`; exact; all 346,104 sets `≤ 24`; the per-set
JSON, 14.6 MB, is regenerable and not committed).
- **Derived and checked**: D1, the host is the least reading divisible by `q_c` (a slower multiple would read `d/(8h) < 1/8`
  at `t*`); D2, `t*` is the rung instant `i/q_c + 1/(8h)`. 0 violations each.
- **The cascade's own rung**: the bound (`K = 0`) in 200,736 (171,972 with one host, 28,764 with a second, faster host also
  opening there; the script recorded the fastest host, so those show as `q_c = h`). Of the 145,368 blocked-bound sets:
  `q_c = h` (gcd 1, full resolution) 115,094, of which `K = 1` (the host's first opening) is the largest part; `q_c ∈
  [2, 8]` 24,039; `q_c ∈ {9,…,12}` 6,235. Multi-host blocked-bound sets: 520, class by the fastest host.
- **The least certifying rung `q_min`** (rung-selection rule with the exact unit test, R6 included): `1`: 200,736;
  `2`: 74,083; `3`: 47,567; `4`: 16,563; `5`: 6,597; `6`: 360; `7`: 190; `8`: 7; `9`: 1 (`(3,4,5,7,17,18,24)`).
- **The landing is `q_min`'s first certified instant** in 200,797: the 200,736 bound sets and 61 others. Otherwise it is
  earlier (145,307); never later (forced: the landing is the first lonely instant).

**Reading** `[reasoned]`: on blocked-bound sets the first isolation and the structured one are different instants in all
but 61. The first is the multi-move chain's endpoint, placed by fine arithmetic; the structured one is the mechanism
started at a better grid instant and landing in one move. Every set here has a one-move start with `q ≤ 9`. This is the
case-list route read in the cascade's own terms, not a new route.

### Method from here (proposed to the owner)

1. **One living map**, a versioned document read before each step: the objects in rung coordinates; derived facts with
   their Lean status; observed regularities, each with its exceptions and the three questions answered (what feature,
   what forces the witness there, same mechanism in disguise); open questions. The log stays the record; the map is where
   the next step starts.
2. **Classify a step before doing it**: an equivalent restatement of the obligation (not a step, by the place test); a
   rule the majority obeys (not a proof); or an argument uniform over an infinite family (a step). Only the third moves
   the proof. The rung budget (`RungBudgetEightN`, a pigeonhole over the `φ(q)` units) is the one uniform tool in view.
3. **Read an exception in the map's coordinates**, never by opening a new vantage: for the rungs below `q_min`, which
   condition failed (multiples not spread, or every unit blocked) and by which readings.
4. **Derive the forced facts first**; run only for what is not forced.

**The next map question, not a mechanism:** why the rungs `q < q_min` fail, per set, by condition and by reading. That is
what pushes `q` up, and it is what a uniform choice of `q` has to handle. The rung budget's failures (1,329 of 91,523 on
`[1,40]`, where every unit count exceeds `φ(q)` but a unit is still free) are where blocked units coincide; the link
lemma (`N ∣ d′ − c·d`, `link_reading`) names when two readings block together.

---

## E189 — 2026-09-30 — the method adopted; the mechanism map built (v1); the interim reduction (Q5)

**Owner**, on E188's proposed method: *"This is a much better approach.  We need to learn from the failed attempts
methodologically not just about that proposed statement.  Always understanding the exceptions should always be required
/ yes build the map and record the memory"*. Then: *"Only one question.  Since we have reduced "any" arrangement to a
finite set.  Do we need an interim step where we reduce the infinite family to a reduced set too?"*

**The map:** `docs/n8/MECHANISM_MAP_v1.md` (outer repo `c40cfa5`). §0 the method (M1 map first; M2 classify the step:
restatement / majority rule / uniform argument / map run; M3 the three answers required for **every** exception; M4
derive forced facts first; M5 failed attempts entered by method class; M6 state every restriction). §1 objects in rung
coordinates. §2 derived facts with Lean status: the 29 declarations cited were checked against the tree (all resolve;
`PinchReflectionN`, `HandoffDriftN`, `SymbolicWindowTransportN`, `DoubleBacktrackN` and this session's
`PartialReflectionN` are untracked and marked so). §3 regularities R1–R9 with their exceptions and the three answers
(R3's budget failures and R8 marked not understood). §4 open questions Q1–Q5. §5 the equivalent forms of the obligation
(restatements, not steps). §6 failed attempts in classes F1–F11, each with its log entries. The map is a working document;
the log remains the record.

**Q5, the interim reduction** `[reasoned; derived on paper, not checked, not in Lean]`: yes, one is needed; the case-list
form is a finite list, and a uniform argument still has to be told which `q` each set uses. At a fixed rung `q` the
rung's conditions see a reading only through whether `q` divides it, its residue mod `q`, and the cell of its reading at
`1/(8e)` cut by the walls `1/8 − r/q`, `7/8 − r/q`; so at fixed `q` the infinite family falls into finitely many classes,
defined by the readings alone (not by loneliness, E145). Open: `q` itself, which on the windows measured keeps growing
(§17E: 9 on `[1,30]`, 16 on `[1,40]`).

**Gates running:** `compile-diff` of the map against log E100–E188 and v21 §15–§17E (owed before the map is relied on as
complete); `memory-drafter` for the owner's ruling. Results in the next entry.

---

## E190 — 2026-09-30 — the reduction of an arbitrary arrangement, worked through: what each step exploits, and its template one level down

**Owner:** *"So look at the proof we made to reduce "any" arrangement.  There are constraints inherent in the system,
like the arrangement of speeds.  Lets carefully work our way through that"*.

Read (statements and docstrings, not re-derived): `Spec/Target.lean` (`LonelyRunnerAt8`, `ExistenceAt8`,
`lonelyRunnerAt8_of_existence`); `Spec/RealEightN.lean` (`existenceAt8_of_nat`, `existenceAt8_iff_congruence`);
`RealFiveN.exists_rows`; `MergeSixN.exists_merge_model_all`; `ManyDirectionsN.lonely_of_model_many`;
`OrderEightCasesN` (`lonely_eight_of_card_le_six`, `_common_factor`, `_no_multiple_of`, `_spread`, `_descent`,
`_fast`); v21 §17A–B; `PROOF_SHAPE_REVIEW_2026_09_25_v1.md` §2.

### The chain, step by step (all proved, or equivalent as recorded)

- **N1. Arrangement → the subject's readings.** The separations are `(v i − v k)t` and `circDist` is even, so only
  `|v i − v k|` matters (`lonelyRunnerAt8_of_existence`). **What the arrangement adds is coordinates, not a
  restriction** `[reasoned; the review's N1 records it]`: every set of seven distinct positive reals is the reading set of
  the slowest runner of `(c, c + d₁, …, c + d₇)`, `c > 0` (all speeds positive), and smaller sets are order seven's. The
  signs, the gaps and the other seven subjects' readings are all functions of the seven numbers. The converse is not an
  `↔` in Lean (review §2 N1); owed, small.
- **N2. Real → whole numbers** (`existenceAt8_of_nat`). The readings are `l·(r₀ + Σ rⱼ βⱼ)` with whole-number rows over
  directions free of rational relations (`exists_rows`). One class (all rows parallel): whole numbers, rescaled. More
  than one: a whole-number direction `y` on which **two readings coincide** (`exists_merge_model_all`), so at most six
  model readings; **order seven** clears them at `1/7` at a model instant `τ`; **stepping** (pigeonhole returns) finds a
  real time at which every real reading is within the **margin `1/7 − 1/8 = 1/56`** of its model reading
  (`lonely_of_model_many`). What it exploits: independent directions are a **freedom** (the real time can imitate any
  whole-number projection), and the order below has **slack** to pay for the imitation. Rank one has no such freedom;
  that is why whole numbers are what is left.
- **N3. Common factor out; at most six readings by order seven.**
- **N4. The case list → `EightResidual`.** Each case uses one arithmetic fact of the whole numbers and names its instant.

### The template, and where it recurs one level down `[reasoned]`

N2's shape is: **merge readings until at most six remain, settle those by order seven, and spend a freedom to place the
rest inside the slack.** The case list repeats it at rank one, with a resolution `q` in the role of the direction:
- `lonely_eight_of_descent` (`q = 8`): the multiples of 8 are **merged onto the grid** (at `t = (j + τ)/8` a multiple
  `8d′` reads `d′τ`, whatever `j`), their cofactors (at most six) go to **order seven** at `τ`, and the non-multiples are
  placed by a **pigeonhole over the eight shifts `j`** (cost `Σ max 2 (gcd e 8) < 8`).
- `lonely_eight_of_fast` (R8): the six slow readings to order seven at `1/7`; the fast runner is the freedom.
- `lonely_eight_of_card_le_six`: nothing to merge.
- §17E's rung-selection rule is the same shape with the model instant fixed: at `i/q + 1/(8e) = (i + q/(8e))/q` a
  multiple `q·d′` reads `d/(8e)`, i.e. the **cofactors at their own bound `1/(8e′)`, `e′ = e/q`**: "R1 on the multiples"
  is R1 on the cofactors, and the units `i` are the shifts.

**Caution (map M6, F6).** With the model instant left free, the template is the obligation again: a multiple of `q` is
clear at `t` exactly when its cofactor is clear at `q·t`, so "some `(j, τ)` with the cofactors lonely at `τ` and the
non-multiples clear at `(j + τ)/q`" is loneliness at `t = (j + τ)/q`, restated. The content is always a **restriction**:
order seven's instant, the cofactors' bound, a pigeonhole over the shifts.

### The constraint the reduction exploits, at rank one `[reasoned]`

At rank one the arrangement of the speeds that matters is **which readings each `q` divides**. For each `q` the seven
readings split into multiples (merged onto the grid, carried by their cofactors, at most six, so order seven always has a
lonely instant for them) and non-multiples (which must fit into that instant pulled back by `q`). Every rank-one case
in the list uses this split (R6: no multiple; common factor: no non-multiple; descent: few non-multiples cheaply placed;
rung-selection: multiples spread). This is the inherent constraint for Q5: per `q`, the family is described by the split,
the non-multiples' residues mod `q`, and the cofactors' structure.

**Open from here (for the map, not mechanisms):** the split profile of each set across `q` (how many readings each `q`
divides, with their cofactors), read against `q_min` (E188) and the residual; and which restriction of the model instant
the non-multiples need when the split leaves several of them.

---

## E191 — 2026-09-30 — consequences never drawn (M7); map v2 with v1's compile-diff repairs; E190 corrected

**Map:** `MECHANISM_MAP_v2` (built here) · §9 (new: consequences of proved results) and §4 Q6 · M2 (d) plus the new M7 ·
nearest §6 classes F7 (record not read) and F13 (consequence not drawn): this entry records instances of both, one of
them E190's.

**Owner:** *"That is interesting.  We are proving things and then not thinking about how they may affect the whole proof
attempt, that is working harder instead of smarter.  Are there other opportunities we have been missing."* Then:
*"Please be careful, we re proved all n=3 to 7 natively with the framework"*.

**Correction to E190.** E190 said the converse of N1 "is not an `↔` in Lean (review §2 N1); owed, small". Wrong:
`OrderEightN.lonelyRunnerAt8_iff_residual` (`OrderEightCasesN.lean:982`, both directions, `LonelyRunner` commit
`f32daf4`, 2026-09-25) proves the conjecture at eight runners equivalent to every `EightResidual` set being lonely, and
E104 records it. The review (same date) and v21 §17B still carry the question as the author's; the theorem answers it.
E190's own placement (it predates the `**Map:**` convention): map v1 · §4 Q5 · M2 (d), a reading of proved statements ·
nearest class F7, which it fell into on this point.

**v1's `compile-diff`** (`docs/n8/MECHANISM_MAP_v1_COMPILE_DIFF_v1.md`, saved as returned). Losses that change what v1
said, all repaired in v2:
- the hypotheses of "the mechanism" were dropped: `grid_class_clear` holds for one class under small-deviation
  conditions (E129); a separation is the cascade's next move when every other reading keeps its band (E159, E160);
- v1 §2A put a move budget ("at most 7 moves") into the mechanism, the shape E172 and E184 flag as imported;
- R3 lacked v21 §17E's density premise and the same-size null that makes the rung-selection rule structure;
- local stability was widened to the straight deformation, where multi-pinches and the bounded-time half are open;
  partial reflection was stated without its hypotheses; the OWED Props (`WindowBound`, `CaseB8`, `CaseC8`, `Cover8`)
  were missing;
- entry and figure mismatches (3,897 is E174's; "E126" items are E129–E130's; the growth figures are
  `rung_selection_v1.out`'s; v21 §17D's 12, 15, 16 are rational-opening `N`, not rung `q`; `EightResidual` has 22
  fields in the tree, not 19);
- global caveats missing: the range caveat (E114), field usability (v21 §17C), the tool rulings (E101, E112).
Part (C) of the report lists the open items in range that the map does not carry.

**`docs/n8/MECHANISM_MAP_v2.md`** carries those repairs, M7 ("draw the consequence"), the owner's caution on lower
orders, Q6, new failure classes F12 (range-forced) and F13 (consequence not drawn), and §9, the consequence register:
- **C1** the residual is the conjecture (`lonelyRunnerAt8_iff_residual`); manuscript correction owed.
- **C2** the case list's strong induction on the sum has "every smaller-sum set is lonely" in scope where it calls the
  residual, and does not pass it on; passing it makes any proved transfer to a smaller-sum set a case.
- **C3** the rung budget, uniform in `q`, is proved and is not a residual field, while fields were added one resolution
  at a time.
- **C4** `no_small_resolution` quantifies over every `j` (checked, `OrderEightCasesN.lean:791`), and the cascade's
  landing is a clearing resolution with `D` the host; so §17D's final `0` on `[1,40]` records the cascade's arrival, not
  structure.
- **C5** our own order-seven proof (native, re-proved in the framework) uses only that every nonzero residue mod 7 is a
  unit; `BS_TRANSFER_v2` (2026-09-18, before the native re-proof) found the break at 8 to be mathematical (the
  non-units), posed an affine multiplier family at order 8 as the open sub-problem, and the log has not returned to it.
  This is Q6, to be read from our own order-seven modules first.
- **C6** E190's template across N2, descent, R8 and rung-selection.
- **C7** the earlier maps (`EXISTENCE_MAP_v1`–`v5` and others) are cited nowhere in the log.
- **C8** the path route duplicates N2's reduction; its open halves bear on `hopen`.

**Memory:** `feedback_n8_map_first_2026_09_30.md` written by `memory-drafter` (pointers in `MEMORY.md`'s n=8 block,
`lrc_INDEX.md`, `feedback_INDEX.md`; scope notes added to the oracle memory and the exceptions memo). An update for this
entry's rulings (M7, the lower-order caution, v2, the audit starting at E191) is with `memory-drafter`.

---

## E192 — 2026-09-30 — Q6: our order-seven proof read for order eight; the residual is the translated hard branch, at the bottom level only

**Map:** `MECHANISM_MAP_v2` · §4 Q6 and Q5 · M2 (d), a source reading, nothing run · nearest §6 classes F7 (avoided:
our own modules read first) and F9 (orders three to seven read as our native proofs).

**Owner:** *"Yes the lean work is ahead of the manuscript and paper at this time as I feel we need to bed down the proof
attempt first. / yes start with Q6, read our order seven proof first"*. So the manuscript corrections owed from E191
(map v2 §9 C1, C4) wait; the Lean tree leads.

**The reading:** `docs/n8/Q6_ORDER_SEVEN_READ_v1.md`. Our order-seven proof (`Spec/OrderSeven*N.lean`) uses one
arithmetic fact, T7: every nonzero residue mod 7 is a unit. Its steps: the instant `K/(7P)` with the band; descent;
7-adic levels and top digits; the multiplier identity `qz_lambda` (pure algebra); one level (`single_level_avoid`, T7:
bijective slopes, `2 × 3 = 6 < 7`); the top level (`band_top`, T7); the level induction (`unit_filtering`); the easy
branch (`corollary3`: at most three readings per level below the top); the hard branch (`bs_discrete_q`: a crowded
level, moved to the bottom by `exists_pre_congr`, then `four_band` (§5: normalise into the squares `{1,2,4}`, compress
into an arc of length ≤ 5 at a dilation `j ≤ 5` by the carry lemma, shift off `{0,6}`), `five_band` (§6), `five_band_m1`
(§7, moduli 49 and 98)).

At order eight, step by step (`[derived]`, not in Lean): the multiplier identity holds in octal digits; the top level
holds for any odd multiplier; one level holds with a **cost** per reading, `≤ max(2, gcd(r, 8))`, free when the costs
sum to at most 7. That cost is exactly the hypothesis of `lonely_eight_of_descent` (`Σ max 2 (gcd e 8) < 8` over the
non-multiples of 8), so **descent is step 5 at level 0**, with the higher levels sent to order seven through the
cofactors; the easy branch at eight is contained in descent. And the residual's `cost` field (checked,
`OrderEightCasesN.lean:779`: `8 ≤ Σ max 2 (gcd e 8)` over the non-multiples) makes **every residual set the hard branch
at the bottom level**; v21's shapes `(1,6)`–`(4,3)` are that crowded level.

**Consequence:**
- Q5 `[derived]`: the positive-arithmetic fields alone reduce the residual to one shape, a crowded level of non-multiples
  of 8 (cost ≥ 8), with the multiples of 8 carried by order seven through their cofactors. The open statement is about
  that level.
- Q6 `[derived]`: our order-seven architecture carries through the easy branch (the case list already holds it);
  what does not carry is its hard-branch mechanism, which rests on T7 throughout. Mod 8 the units `{±1, ±3}` are not
  cyclic and the non-units `2`, `4` form their own classes.
- A simplification over order seven `[derived]`: a crowded **interior** level never arises at order eight on this route.
- Freedom not yet spent `[reasoned]`: descent fixes order seven's instant `τ` and uses eight shifts. The crowded level can
  also use the choice of `τ` among the cofactors' lonely instants, and dilations, which is what order seven's hard
  branch spends.
- Routes: this does not duplicate any route in map v2 §9. It locates the open statement inside the case list, and it
  adds §3 of the note (the hard-branch tools and their state at 8) to the map at its next version.

**Next (source first):** read `four_band`'s compression and shift in full (`OrderSevenA4N`, `OrderSevenS5bN`) and
`five_band`'s case structure (§6), then a map run on the residual's crowded level (sign-normalised classes mod 8, costs,
and which freedom each set's certificate uses).

**Housekeeping:** `memory-drafter` revised `feedback_n8_map_first_2026_09_30.md` (M7 kept as the session's rule, not an
owner ruling; the `**Map:**` audit starts at E191, the `**Consequence:**` audit at E192). Map v2 §9 C7 should read
"returned 1 before E190"; carried to v3.

---

## E193 — 2026-09-30 — Q6 step 2: the crowded level through our order-seven instant form; the 97 exceptions read

**Map:** `MECHANISM_MAP_v2` · §4 Q6 and Q5 · M2 (d), a map run (pass conditions: the oracle check only) · nearest §6
classes F2 (a rate as the answer: avoided, counts of sets the 56-instant family clears are not reported as findings)
and F11 (the exceptions are read here, not answered with a new vantage).

**Owner:** *"Ok that sounds good, just remember to keep to our own framework, boundaries, isolation events, cascade not
density or other frames."*

**Step 1, read** (`OrderSevenA4N`, `S5N`, `S5bN`, `LemmasN`). `four_band`'s instant is `λ/7^{m+1}`, `λ = j + k·7^m`:
a **fine instant** `j/7^{m+1}` (`j ≤ 5`) where the crowded level's readings leave two adjacent sevenths empty
(compression, by the carry lemma, checked in the kernel over every carry path), then a **grid rotation** `k/7` that
turns the empty pair onto the subject's slot. Readings of one residue class rotate together; `lemma5` is the several
classes at once: arcs rotating at speeds 1, 2, 4 on the 7-grid, a grid time at which every arc misses the slot. So the
hard branch is an isolation event on the grid, found exactly, and the proof covers an infinite family because each
reading enters only through its class, its top digit and its carry bits.

**Step 2, run** (`LonelyRunner/experiments/nN/redo/crowded_level_v1.{py,out}`, `_v1b`; commits `1dace25` and the one
above; exact). Class: 7-sets in `1..24` with a multiple of 8, level-0 cost `≥ 8`, no common factor: 229,061 sets, all
with `m = 1` (modulus 64, instants `(j + 8k)/64`). Derived before running: whether `a/64` is lonely depends only on the
readings mod 64. Oracle check (no lonely `a/64` before the cascade's landing): 0 violations.

**Exceptions, no `a/64` lonely: 97** (each listed in `crowded_level_v1b.out`). All have exactly one multiple of 8. The
three answers `[VERIFIED — these 97]`:
- (i) **Feature.** 34 have no multiple of 6 (31) or of 7 (3): R6 at `1/6` or `1/7`. 12 are one-free (six readings share a
  factor the seventh lacks). One, `(3,4,5,13,16,18,21)`, is R1 (landing at the bound `1/24`). The other **51** meet the
  residual's positive fields (odd, a multiple of each of 5, 6, 7, 8) and are neither R6 nor one-free. No small subset
  explains any exception: the smallest set of readings whose blocked instants cover the 56-instant grid has 6 readings
  (18 sets) or all 7 (79).
- (ii) **Where the isolation is.** Of the 51: 36 are lonely at a grid instant `i/11` (21) or `i/12` (15); 15 are on no
  grid with `q ≤ 12`. Of those 15 the cascade lands at `17/128`, `33/128` or `9/128` (host 16 at the rungs `1/8`, `1/4`,
  `1/16`, modulus `128 = 2·64`) in 6, at host 13's openings `25/104`, `49/104` in 5, and at hosts 5, 23 and the bound in
  the rest.
- (iii) **Same mechanism?** Yes in kind: a grid through the arrangement at another resolution (6, 7, 11, 12) with its
  multiples separating, or the 8-adic grid one level finer (`128 = 2·64`, the counterpart of order seven's §7 move from
  49 to `98 = 2·49`). **Not understood:** why six or seven readings jointly block every `a/64` in these sets (no
  derivation yet; the joint blocking is the object).

**Consequence:**
- Q6 `[VERIFIED — readings ≤ 24]`: order seven's instant form translated to one prime power (`8^{m+1}`, here 64) does not
  settle the crowded level at eight even at `m = 1`. The exceptions move to other resolutions, which the case list's R6
  (5–8), thirds, fifths and sixths/sevenths/ninths already reflect, and in part to `2·64`, as order seven's §7 did. Order
  eight's hard branch is multi-resolution where order seven's needed one prime and one special modulus.
- Q5 `[derived]`: at `m = 1` (a multiple of 8, none of 64) the question "is some `a/64` lonely" depends only on the
  residues mod 64: a finite question for an infinite family. Its complete answer, the list of residue patterns mod 64
  with no lonely `a/64`, is computable and would be a class (c) statement (every other `m = 1` set is lonely at some
  `a/64`), with the list itself as the analogue of order seven's §7 exceptional sets.
- Routes: this narrows Q6 and does not duplicate a route in map v2 §9.

**Next:** the complete finite list at `m = 1` (residue patterns mod 64 whose blocked instants cover all 56), using the
unit group's action and sign to reduce the enumeration; then read which resolution settles each pattern class.

---

## E194 — 2026-09-30 — the complete list at m = 1, modulus 64; the exceptions are the non-unit top level; order seven's §7 move repairs them

**Map:** `MECHANISM_MAP_v2` · §4 Q6 and Q5 · M2 (d) with a finite exhaustive statement (class (c) in form: it covers
every `m = 1` residue pattern) · nearest §6 classes F6 (the instant family is restricted: `a/64`, then `a/(8·2^v)`) and
F11 (the exceptions are read, E193's next step followed).

**Run** (`LonelyRunner/experiments/nN/redo/crowded_m1_cover_v1.c`, `.patterns`; `crowded_m1_cores_v1.{py,out}`;
commit above). Derived first: at `m = 1` whether some `a/64` is lonely depends only on the residues mod 64, and the
answer is invariant under multiplying every residue by a unit mod 64 (the unit permutes the 56 instants), so one odd
residue is normalised to 1. Every multiset of seven residues with no residue 0, a multiple of 8, an odd residue and
level-0 cost `≥ 8` was enumerated: 109,453,344 normalised patterns `[VERIFIED — exhaustive mod 64]`.
- **Exceptional (no `a/64` lonely): 32,642 unit-orbits.** Their minimal covering sub-multisets ("cores"): 12,518
  distinct, of sizes 5 (18), 6 (372), 7 (12,128).
- **Three answers** `[VERIFIED — exhaustive mod 64]`:
  - (i) **Feature: an even cofactor at the top level.** 28,786 orbits contain residue 32 (a multiple of 8 with cofactor
    `≡ 4 mod 8`: it reads `a/2`, blocking every even `a`); a further 3,728 have their multiple at 16 or 48 (cofactor
    `≡ 2 mod 4`: blocks `a ≡ 4 mod 8`). So **32,514 of 32,642** carry a multiple of 8 whose cofactor is **not a unit**.
    Every core of size 5 or 6 contains 32. Order seven's `band_top` holds because every top-level cofactor is a unit mod
    7 (T7); mod 8 that fails, and this is where. Only **128 orbits** have the multiple at an odd cofactor (residues 8, 24,
    40, 56): the counterpart of order seven's own exceptional list at `m = 1` (§7).
  - (ii) **Where the witness is.** Take the modulus from the 2-adic valuation of the multiple, `N = 8·2^v`: the cofactor
    becomes odd and the top level is clear at every unit instant again. On E193's 97 exceptions `[VERIFIED — these 97]`:
    93 have the multiple 16 (`v = 4`), and **all 93 are lonely at some `a/128` with `a` odd**, order seven's own form (a
    unit multiplier); the cascade itself lands at `17/128`, `33/128`, `9/128` in six of them (E193). The other 4 have the
    multiple 8 or 24 (`v = 3`) and stay exceptional: `(1,5,6,7,8,11,13)`, `(1,5,6,7,11,13,24)`, `(2,7,8,9,11,13,15)`,
    `(2,7,9,11,13,15,24)`; the six non-multiples `{1,5,6,7,11,13}` or `{2,7,9,11,13,15}` block the whole `1/64` grid alone,
    and the cascade lands at host 13's openings (`49/104`, `25/104`).
  - (iii) **Same mechanism.** Yes: order seven's instant form, with the modulus read from the top level's 2-adic
    valuation. That is order seven's §7 move (`49 → 98 = 2·49`), which at order eight is the rule for every even cofactor,
    not a special case.

**Consequence:**
- Q6 `[VERIFIED — exhaustive mod 64; the 97]`: the order-seven architecture carries further than E193 found, once its
  top level is taken 2-adically. What fails at `a/64` is almost entirely (32,514 of 32,642 orbits) the non-unit top level,
  and on the window the 2-adic modulus repairs 93 of 97. The residue left is the odd-cofactor list: 128 orbits mod 64, 4
  sets on the window.
- Q5 `[derived; VERIFIED as above]`: the finite reduction at `m = 1` becomes: the top level's 2-adic valuation `v`, then
  residues mod `8·2^v`. The complete exceptional list at `v = 4` (mod 128) is the next computation; `v = 5` (mod 256) needs
  a pruned enumeration.
- The 4 remaining sets land on the 13-grid (a prime other than 2), so the genuine exceptions carry the multi-resolution
  question of E193 (map v2 R3, Q3); they are to be read by M3 next, not answered with a new family.
- Map v2 §9 C3 (the rung budget as a uniform case) and C5 (Q6) are refined by this; carried to map v3.

**Next:** (1) the exhaustive list at `v = 4` (residues mod 128, one multiple of 8 with `v = 4`); (2) the 128 odd-cofactor
orbits mod 64 read by M3 (starting from the cores `{1,5,6,7,11,13}` and `{2,7,9,11,13,15}`); (3) map v3.

---

## E195 — 2026-09-30 — one multiple of 8, not of 64: no exception at modulus 128 or 256 (exhaustive over residues)

**Map:** `MECHANISM_MAP_v2` · §4 Q5, Q6 (and Q4) · M2 (c) in form: a finite exhaustive statement that covers an infinite
family; not proved in Lean · nearest §6 classes F5 (checked: the statement is not forced by the definitions; the same
check at modulus 64 has 128 exceptional orbits) and F6 (the instant family is restricted and stated: `a/2^{W+3}`).

**The statement** `[VERIFIED — exhaustive over residues mod 128 and mod 256; not in Lean]`: every set of seven positive
readings with **exactly one multiple of 8, that multiple not divisible by 64, and an odd reading** is lonely at `1/8` at
an instant `a/128` when the multiple's 2-adic valuation `V` is 3 or 4, and at an instant `a/256` (with `8 ∤ a`) when
`V = 5`. This is the residual's `(1,6)` shape at `m = 1`.

**How it was checked** (`LonelyRunner/experiments/nN/redo/crowded_m1_cover_v2.c`, `_v3.c`, summary
`crowded_m1_cover_E195.out`; commit `8784e8e`). Derived before running: at `a/N` a reading's clearness depends only on its
residue mod `N`, and multiplying every residue by a unit mod `N` permutes the instants, so one odd reading is normalised to
1 and nothing is lost; the multiple `2^V·c` runs over every odd `c`; the other five readings run over every residue that is
not a multiple of 8, with repeats. Counts:
- `V = 3`, modulus 64: 21,846,048 patterns, **128** exceptional orbits (control: equals E194's odd-cofactor list);
- `V = 3`, modulus 128: 1,283,115,904 patterns, **0**;
- `V = 4`, modulus 128: 641,557,952 patterns, **0** (run twice, two programs);
- `V = 5`, modulus 256: 19,650,718,080 patterns, **0**.

**What closes it, read against our order-seven proof** `[derived; checked]`: not order seven's own instant family. At
`V = 3` that family (a dilation `j/64` and a rotation `k/8`) is exactly the `a/64` grid, which leaves the 128 orbits. What
closes every pattern is the **full set of multipliers one or two binary digits finer** (`a/128`, `a/256`): the freedom
`BS_TRANSFER_v1` §3 measured as "the whole unit group mod `8M`", here made exhaustive at fixed moduli.

**Consequence:**
- Q5 `[VERIFIED — as above]`: the `(1,6)` shape with `m = 1` (a multiple of 8 not divisible by 64, whatever its size and
  whatever the other six readings) is closed by three finite checks. This is the order-seven pattern of reduction,
  residues and a finite verification, carried to order eight for this shape.
- **Not closed:** the `(1,6)` shape with the multiple divisible by 64 (`V ≥ 6`): at a fixed modulus `2^{W+3}` the multiple
  reads `0` once `V ≥ W + 3`, so the modulus must grow with `V` and the check grows with it; a statement uniform in `V`
  needs structure this run does not supply (order seven's uniformity in `m` came from its dilation family being enough,
  which is exactly what fails here at `V = 3`). The shapes `(2,5)`, `(3,4)`, `(4,3)` (two to four multiples of 8) are
  not yet checked.
- **Lean:** 2 × 10¹⁰ patterns is not a kernel `decide`. A proof needs the reason each pattern class has its instant (a
  certificate per class, or a structural lemma); that reason is not yet read (M3 on the statement's own content: which
  `a` works, and why one extra binary digit suffices).
- Routes: this is on the case-list route (§17C), as a new case for the residual's `(1,6)` shape; it does not duplicate a
  map v2 §9 route. It refines C3 and C5.

**Next:** (1) why one extra binary digit suffices: for the 128 orbits at `V = 3`, which `a/128` is lonely and what it is
in rung terms; (2) `V = 6, 7` at modulus 256 with the multiple's blocked instants included (feasible), to see where the
fixed modulus stops; (3) the `(2,5)` shape.

---

## E196 — 2026-09-30 — owner: "are we creeping back into trying to derive something that the cascade doesn't do"; E192–E195 assessed; the line paused

**Map:** `MECHANISM_MAP_v2` · the method itself (§0: the cascade is the oracle; the work is its mechanism) · housekeeping
and assessment, nothing new run · nearest §6 classes F1 and a new one, F14 (below).

**Owner:** *"I also wonder are we creeping back into trying to derive something that the cascade doesn't do instead of
trying to figure out why the cascade is a perfect oracle that has never not found an isolation point for any
arrangement"*. Relayed from the parallel session (not on disk): *"Both directions can fail, and I found an exact example
where every eligible \(2t,3t,5t\) candidate fails its immediate repair. At the tripled event, one runner blocks the
backward repair and a different runner blocks the forward repair. Moving to the latter runner's next opening then clears
all seven."*

**Assessment `[reasoned]`: yes.** E192–E195 took our order-seven proof's instant form (a multiplier at modulus
`8·2^V`: dilations and grid rotations) and checked, exhaustively over residues, whether it names a lonely instant. The
cascade entered only as the oracle check (no lonely grid instant before its landing). The cascade does not visit those
instants: it starts at the bound and moves by openings. So the line establishes certificates the cascade does not
produce. They are true statements of the owner's case-list proof form (v21 §0: a condition plus a named instant), and
the results stand at their grades; but they do not say why the cascade finds the isolation, and read in the cascade's
terms E195 says only that the landing comes **no later than** the first lonely grid instant: the when-at-the-latest shape
(F1), which names no place.
- **How it happened:** Q6 asked whether our order-seven *architecture* carries up; reading it (E192) was right, but E193
  onward took its instant family as the object to test, rather than asking what the cascade does on the same sets.
- **The parallel session's note, same reading:** the `2t, 3t, 5t` candidates are replacements the cascade does not
  make. Its own repair, "moving to the latter runner's next opening then clears all seven", **is the cascade's move** (the
  blocking reading's next opening). When a derived rule fails, the fix that works is the cascade's move again; so do the
  rung-selection exits (the least multiple's opening, E188) and E193's exceptions (the cascade's `17/128` is host 16's
  opening).
- **F14 (new class):** a family of instants the cascade does not use, pursued in place of the cascade's mechanism, with
  the cascade reduced to an oracle check. Instances: E193–E195; the double-and-backtrack and `2t, 3t, 5t` lines (E186;
  this note).

**Recorded as data, not pursued:** the stopped run (`crowded_m1_cover_v4.c`, `_partial.out`) found, at `V = 4`, zero
exceptions already for the single dilation `j = 1` with the sixteen rotations `k/16` (`J = 1..5` all 0; `V = 3` not
reached). Because the unit normalisation fixes an odd reading `d₀` at 1, this reads, for the original set: for every odd
reading `d₀`, the subject is lonely at some `a/128` with `a·d₀ ≡ 1 (mod 8)` `[VERIFIED — exhaustive mod 128, V = 4]`.

**Consequence:**
- The E192–E195 results stay on the case-list route (map v2 §9 C3, C5; Q5). They are not the cascade's mechanism and are
  not to be presented as it.
- What the owner asks is the cascade's own question: at every move the readings in the subject's slot separate and the
  latest exit is taken (E162); the landing is the exit after which nothing is in the slot. What stays unexplained is why
  that chain of exits always reaches an empty slot, in the cascade's own objects.
- Standing check: the owner's question is the check for F14 at the start of a step: does the step study what the cascade
  does, or a family it does not use?

---

## E197 — 2026-09-30 — owner: "We have a perfect oracle and you keep wanting to prove something else"

**Map:** none — housekeeping (an owner ruling on direction; nothing run).

**Owner:** *"This keeps on being an ongoing problem.  We want to prove n=8 via the framework.  We have a perfect oracle
and you keep wanting to prove something else"*.

**Recorded as a recurrence of F14 and of the oracle memory's failure.** Since the owner's direction of 2026-09-29 (*"It
is about boundaries, isolation incidents that we have an oracle for"*), the entries that studied the cascade's own run
were E174–E175 (where it lands, the misses perturbed through it) and E178–E183 (how its landing moves as a speed
changes: pinches, reflection, relocation, restart). E185–E195 moved step by step onto other objects: the path route's
window, the reduction proofs, our order-seven proof's multipliers, exhaustive certificate families. The cascade ended as
an oracle check. The owner's own statements of the programme are on record: E74 (*"how and why speed changes deform the
location of the isolation"*), E100 (*"there must be a mechanism that dictates where the isolation is pushed"*), E102
(*"make sure we have the mechanism it uses and we will have proof"*), E111 (*"understanding exactly the proxy seems to be
our work"*). Work resumes on the cascade's run itself, at the owner's direction.

---

## E198 — 2026-09-30 — design phase: how the cascade works, inside the owner's design (`CASCADE_DESIGN_v1`)

**Map:** `MECHANISM_MAP_v2` · §0 (the method) and §1 (objects) · design only, nothing run · frame check applied at every
step of the document: "would this step make sense to someone who had never seen the cascade?".

**Owner:** *"Maybe we need to spend more time in the design phase.  Thinking and reasoning through how the it works.  But
also think and reason all parts along the way.  Every step has to be though of, am I trying to fit this to another frame
to avoid it.  We have a perfect oracle that is so much an advantage that others don't get and we seem to be wasting it
because it doesn't look like other frames"*.

**Written:** `docs/n8/CASCADE_DESIGN_v1.md`, built on the owner's design as recorded in E139–E163 (re-read for this
entry): an arrangement is a grid plus a deviation; at the arrangement's own grid instant every runner is clear except
those captured in the subject's slot (`grid_class_clear`); each capture is released by one cascade move, a separation
(`lonely_of_separation`, `move_eq_separation`); only readings carried over the entering edge obstruct next (`transport`);
the same mechanism at every scale (the slow/fast recursion, `SlowBlockN`, E147–E152; nested clusters, E155) and every lap
(rotations, E141). One question is left (E158): separating one pair cannot keep putting another runner into the slot for
ever; inside the recursion it is the fast group's chain ending inside the slow group's block (E151–E154).

**Consequence:** the programme's open question is restated in the cascade's objects only (what is carried in during each
separation, from which grid position, against the separation's length), with four design questions (§6) for discussion
before any step. The E164–E197 work is placed against it: most of it studied other objects (F14, E196–E197).

---

## E199 — 2026-09-30 — the owner's proof breakdown; existence checked; "only so many arrangements" as the compact gap simplex

**Map:** `MECHANISM_MAP_v2` · the method and §4's open questions · design only, nothing run · frame checks in
`CASCADE_DESIGN_v2.md` §7.

**Owner:** *"Let me try and break it down.  For n=8 proof, we need to prove existence or exhibit - double check that.  The
proof is that for 8 runners any arrangement eventually, each runner becomes lonely.  For our framework, we should lonely
is proven for AP and grid - so for that we already have existence/exhibit - that works for ap/grid but not every
arrangement.  Next step is any arrangement is not infinite.  We prove that for 8 runners there are only so many
arrangements.  Then we should those arrangements can be reference to the ap/grid arrangement and that for those finite
arrangment they are simply ap/grid plus divation.  Cascade works because it shows the map of where that displacement is
relocated to."*

**Checked:** the target is existence for every injective arrangement and every runner (`Spec/Target.lean:401`); the
proofs are classical, so no witness is required, and in the framework existence and the exhibit coincide (`doors_agree`,
`first_isolation_of_fixed`). The AP and grid base is proved with deviation neighbourhoods and named relocated instants
(`APNeighbourhoodN`, `GridNeighbourhoodN`, `GridNudgeN`, `grid_class_clear`, `nested_clear`; all tracked).

**Reasoned** (`docs/n8/CASCADE_DESIGN_v2.md` §7): up to shift and scale (proved symmetries) an arrangement is its seven
gaps normalised to sum 1, a point of a **closed simplex**: compact, with the lower orders and clustered or far speeds on
its boundary faces. The proof the breakdown gives: a **finite cover of the simplex by explicit pieces**, each a reference
(AP, grid) plus a deviation region with a proved relocated instant; the cascade supplies the map (where the isolation
relocates, and where each piece ends at the next event). A cover must be built and checked; it cannot be inferred from
local stability, which would presuppose that every point is lonely.

**Consequence:** the programme's finiteness step is stated in the framework's objects (references, deviations,
relocations; the cascade's map), with three questions to the owner (§7.6) before any step.

---

## E200 — 2026-09-30 — the owner on the breakdown: no "first isolation"; the mix of AP and grid; the isolation pushed by the speed; no gaps

**Map:** `CASCADE_DESIGN_v2` §7 · design only, nothing run.

**Owner** (on E199's points, verbatim): *"I don't like first isolation.  Because that is not required by the conjecture
and I don't believe our frame work.  Often it is, but sometimes it is not."* · *"Hmmm do we not have a mix and match
proof, where the first half of AP will work with a second part of grid?"* · on the gap simplex: *"Yes AP is scale
invariant and Grid extends to infinity, both of those together plus the fact that the conjecture arrangement places
inherent constraints too i.e. runner 2 can speedup past runner 3 without becoming runner 3."* · on the size of a piece:
*"This question doesn't quite make sense to me. Each isolation is pushed there by the speed."* · on which reference
first: *"Think about it, we want to develop our proof so there is no gaps."*

**Recorded:**
- **First isolation is out of the argument** (E109 O1 restated): the proof uses `doors_agree` (lonely ⇔ the cascade
  arrives) and the cascade's landing as *an* isolation; nothing rests on it being the first. (The Lean statement
  `first_isolation_of_fixed`, `Cascade/Iteration.lean:213`, says the landing is at or before every positive lonely time;
  it is a by-product and is not used.)
- **The mix of AP and grid is in the tree** `[PROVED — SlowBlockN, tracked]`: split at the largest gap; the slow part is
  an AP-like group (an R1 group at `d_min`'s scale) clear on its common block on any lap `k` (`slow_clear`,
  `slow_clear_lap`); on that block **the whole question is exactly the fast part's** (`block_iff_fast`,
  `exists_block_iff_fast`, `exists_block_iff_fast_lap`; real readings), and the fast part is read on its own grid. Also
  mixed: descent and the rung form (the multiples carried AP-like through their cofactors, the rest on the grid).
- **"Pieces" withdrawn.** The owner's object is the push: the isolation's location as the speeds make it, which the
  cascade computes. No regions are grown around references.
- **No gaps, reasoned** `[derived]`: growing a region around one reference leaves gaps. The decomposition must apply to
  every arrangement by construction: a largest gap always exists (so the AP part / grid part split always applies);
  every speed is a grid position plus a deviation at any scale (so "grid plus deviation" always applies); the grid
  through the arrangement's own reading is always defined (`GridPairLawN`). Then no arrangement is outside the
  structure, and every proof obligation is of one kind: where the deviation pushes the isolation, shown by the cascade.
  The one obligation left is that the push never loses it: at each level of the split the fast part's isolation falls
  inside the slow part's block (E151), and captures separate without an endless chain (E158).

---

## E201 — 2026-09-30 — E151 in the owner's form: designed, run, refined once; where the fast part's push lands in the slow part

**Map:** `CASCADE_DESIGN_v2` §3–§4, §7; E200's gapless structure · M2 (d), a map run with the statement named in advance
as a place (the slow part's clear interval) · nearest §6 classes F5 (checked: the "some interval" form is forced, the
content is the index) and F14 (avoided: the object is the cascade's own run, split into its slow-part and fast-part
moves).

**Owner:** *"yes, design E151's statement in that form first and then run it"*.

**Design** (`LonelyRunner/experiments/nN/redo/e151_block_v1.py` docstring): split at the largest consecutive ratio and
re-split the lower part until its spread is at most 7 (always stops): every arrangement gets a slow part `P` (AP-like at
`d_min`'s scale) and a fast part `F`. Derived: while `P` is clear, only `F` can be in the subject's slot, so every
cascade move made there is `F`'s own push (D1). Statement v1: the cascade lands in `P`'s first same-lap block, or, after
a move set by `P`, in its second.

**Run v1** (exact): every set `≤ 24` (346,104): first block 345,873, no block 231; late fine shapes (5,400): second
block 5,400, each after a move set by `P`; Case C (1,000 + 1,000): first 994 and 997, no block 6 and 3. Checks: landing
lonely, D1: 0 violations in all four.

**The three answers on v1's 240 exceptions** `[VERIFIED — these 240]`: (i) every one has `P` of spread 7 or just under
(6.7–7), so its same-lap block is a point or tiny; (ii) `P`'s top reading passes to its next lap while the rest of `P` is
on lap 0, and the landing follows that top reading's own exit; (iii) the same mechanism as the late shapes: the slow
part sets a move itself. So the right object is **`P`'s own clear intervals** (its isolation intervals, bounded by its
own exits and entries), not only its same-lap blocks.

**Run v2, refined statement** (`e151_block_v2.{py,out}`): the cascade lands in `P`'s first clear interval, or, after a
move set by `P`, in its second. `[VERIFIED — these populations]`:
- every set `≤ 24`: first 345,873; second 227 (all 227 after a move set by `P`); **third 4**;
- late fine shapes: second 5,400 (all after a move set by `P`);
- Case C `≤ 200`: first 994, second 6 (all after `P`'s move); Case C `≤ 5,000`: first 997, second 3 (likewise).
The 4: `(1,2,4,6,14,15,16)`, `(1,2,5,7,18,23,24)`, `(1,2,5,7,19,23,24)`, `(1,3,4,5,6,7,24)`; each `P` has spread 6–7, and
the chain alternates moves of `P`'s own members (a sweep through `P`) with `F`'s before landing in `P`'s third interval.

**Consequence:**
- **Forced part (F5):** "the landing lies in some clear interval of `P`" holds by definition (at the landing everyone is
  clear). The content is the **index** and **who moves between intervals**: `F`'s push fits in `P`'s first interval in
  almost every set; otherwise `P` itself sets the move to its next interval, and `F` lands there. A proof needs the reason
  `F`'s push fits early, in the cascade's terms.
- **What decides the index** is the next design question: `F`'s push (its own chain from the bound) against the length of
  `P`'s intervals. Short intervals come from `P` near spread 7 (the four) or `P` a single slowest reading with a crowded
  six above it (the late shapes, E154).
- No first-isolation claim is used: the statement is where the cascade lands.

---

## E202 — 2026-09-30 — what decides the index: the push from the bound (AP/grid plus deviation) against the slow part's interval

**Map:** `CASCADE_DESIGN_v2` §2–§4 · M2 (d), designed in the owner's terms first, the checklist in the script's docstring
· nearest §6 classes F5 (the index criterion "the landing is by `7/σ`" is derived, a check) and F1 (avoided: moves are
recorded, never bounded; the test compares two times named by the readings).

**Owner:** *"yes, design what decides the index first, then run it.  remember our checklist to make sure we're not
drifting.  Why ap/grid plus deviation works to find the isolation everytime"*.

**Design** (`LonelyRunner/experiments/nN/redo/e202_index_v1.py` docstring; units `R = 8·d_min·t`): (1) every arrangement
has its bound `R = 1`, where the slow part (spread `σ ≤ 7`) is clear, AP-like in slots 1–6, and the fast part sits on the
slowest reading's own grid: each fast reading `f` at eighth-slot `⌊f/d_min⌋ mod 8` with deviation `{f/d_min}`; so at the
start the only obstruction is the fast readings the deviation has put in the subject's slot, the **captures**
`[derived]`; (2) the cascade separates the captures, and each separation can **carry in** readings over the entering edge
(`transport`); inside the slow part's first interval `R ∈ [1, 7/σ]` every move is the fast part's (E201, D1); (3) the
index is 0 exactly when that **push** ends by `R = 7/σ` `[derived; a check]`. Checklist recorded in the docstring: the
object is the cascade's run; no count as argument; no rate; no instant family; no first isolation; no other proof's
architecture.

**Run** (`e202_index_v1.{py,out}`; exact) `[VERIFIED — these populations]`:
- every set `≤ 24` (346,104): derived check 0 violations; index 0: 345,873 (no capture, landing at the bound 200,736;
  one separation, nothing carried in, 54,642; a chain of carry-ins 90,495); index 1: 227; index 2: 4. **Every landing
  after the first interval has a slow part of spread 5 to 7** (7: 210; 6: 19; 5: 2), whose first interval ends by
  `R = 7/σ ≤ 1.4`.
- captures at the bound sit at grid slot 0 (135,204) or slot 7 (51,357); carry-ins come from slot 6 (121,069), slot 7
  (61,698), and, for fast readings crossing several eighths in one separation, slots 5 to 0 (the rest); 82,448 carry-ins
  are faster than the setter, 150,724 not.
- late fine band shapes (5,400): all index 1; slow part a single reading (`σ = 1`), the capture at slot 7, a sweep of
  about 20 moves through the crowded six outlasting `R = 7` (the population is built to have no lonely point in
  `[1, 7]`), then the slow reading's own move and the landing in its second interval (E154).
- Case C (1,000 + 1,000): index 0 in 994 and 997; the 9 later landings all have `σ` between 6.67 and 7.

**Why AP/grid plus deviation finds the isolation** `[reasoned from the run; the three answers for the later landings]`:
at the bound the AP-like slow part is clear and the fast part is a grid plus a deviation, so the only obstruction is what
the deviation captured (slot 0 or 7); the cascade separates the captures, the separations carry in readings from the
entering edge (a sweep down through the fast part's clusters, E141), and the landing is where a separation carries no one
in. The landing leaves the slow part's first interval only when that interval is short (the slow part near spread 7:
(i) the feature; (ii) the slow part's own top then re-enters and its exit sets the next interval, where the fast part
lands; (iii) the same mechanism, a separation) or when the fast part is a crowd whose sweep is long (the late shapes).

**Consequence:**
- The index is decided by two places read from the arrangement: the slow part's interval end `7/σ` and the end of the
  fast part's sweep from the bound (captures at slots 0/7, carry-ins from the entering edge). On these populations the
  index exceeds 0 only for `σ ≥ 5` or a crowded fast part.
- What a proof needs next, in the same terms: why the sweep started by the captures ends early against the slow part's
  interval; for a crowded fast part, why it ends inside the slow part's second interval (E154's pattern). Not
  established here.

---

## E203 — 2026-09-30 — how the sweep ends: passages of AP-like clusters, linked by bridges from the entering edge

**Map:** `CASCADE_DESIGN_v2` §2, §4 · M2 (d), designed first in the cascade's own terms · nearest §6 classes F1 (avoided:
passages and revisits recorded, never bounded as the argument) and F2 (avoided: no statement of how much time clusters
cover).

**Owner:** *"Thats ok, we want each step to move us closer.  We already have the cascade so figuring how how it is doing
it is important step towards why is it forced.  yes, design why the sweep ends first, then run it"*.

**Design** (`LonelyRunner/experiments/nN/redo/e203_sweep_v1.py` docstring): on lap `k` a cluster is a maximal run with
consecutive ratios below `ρ_k` (E142–E143: a same-lap sweep can only go down through one, and stops at its bottom). The
chain grouped: **passages** (a cluster going through the subject's slot, members exiting in descending speed) linked by
**bridges** (at a cluster bottom's exit another cluster is already in the slot); the landing is a bottom's exit with no
other cluster in the slot: a gap between passages, bounded by one bottom's exit and the next top's entry.

**Run** (exact; commit below) `[VERIFIED — these populations]`; derived checks (descending inside a passage; the landing
a cluster bottom's exit) 0 violations throughout.
- every set `≤ 24` with a chain (145,368): **one passage 96,670**; two 31,913; three 9,217; four 4,402; five to fifteen
  the rest (longest 15, in 2 chains). Bridges 78,267: up 55,137, down 23,123, the same cluster on another lap 7. Chains
  with a revisit (a cluster passing again on a later lap): 4,885. At a bridge the next cluster was, one move earlier, at
  the entering edge (slot 6: 22,336; slot 7: 13,811) or further back when fast (slot 5: 11,510; 4: 6,286; …).
- late fine band shapes (5,400): 13–21 passages, every chain with revisits: a relay across laps (E141's descending waves).
- Case C (762 and 775 chains): mostly one to three passages; revisits in 39 and 29.
- Example read in full: `(1,3,4,5,6,7,8)`: the captured cluster `4…8` passes on lap 1 in five moves; then single readings
  relay across laps (7 on lap 2, 3 on lap 1, 8 on lap 3, 5 on lap 2, 7 on lap 3), up and down alternately; the landing is
  7's exit on lap 3, `R = 25/7`, the rung `3/7` plus 7's exit (E188's form), with every other reading in slots 1–6.

**Reading** `[reasoned from the run]`: the sweep is the captured AP-like cluster going through the slot; it ends at that
cluster's bottom exit unless another cluster is then in the slot, and that cluster got there from the entering edge (or,
if fast, from further back) during the last move. Longer chains are relays of single readings across laps.

**Consequence:**
- How the cascade ends the sweep is now stated in its own objects (passages, bridges, the gap at the landing). Why it
  must end is not: a chain continues exactly while each passage end finds another cluster in the slot, and that is
  decided by where the clusters sit (grid slot and deviation) at the passage ends.
- "Each cluster obstructs once" is **not** the mechanism (revisits in 4,885 chains to 24 and in every late shape; E163
  already found no-return to be the conjecture itself).
- Next design question, in the same terms: the configuration at the passage ends: where every cluster sits at each
  passage end in a chain, what keeps one at the entering edge while the relay continues, and what empties the slot at
  the last one; read on the long relays and the late shapes (including the slow part's own move, E154).

---

## E204 — 2026-09-30 — the passage-end configuration: a conveyor of arrivals, carried by the fast readings; the end is a gap in their arrivals

**Map:** `CASCADE_DESIGN_v2` §2, §3–§4 · M2 (d), designed first · nearest §6 classes F5 (the queue rule is the cascade's rule
restated: stated as such, edge cases counted) and F1 (avoided: move lengths and times-to-edge recorded per move, never
argued monotone).

**Owner:** *"yes, design the passage-end configuration first, then run it"*.

**Design** (`LonelyRunner/experiments/nN/redo/e204_queue_v1.py` docstring): at a move from `t` the readings outside the slot
form the **entering queue**, each reaching the entering edge after `T_c = (7/8 − frac(c·t))/c`; the move lasts `D` (the
setter's remaining stay). Forced: a queue reading is carried in iff `T_c < D` and it is still in the slot at the move's
end (edge cases counted: a fast front passing straight through; a reading re-entering). Content: C1 whether the next
setter is the previous move's queue front; C2 which readings set the moves; C3 the front at the landing.

**Run** (exact) `[VERIFIED — these populations]`:
- relays to 24 with at least three passages (16,785): C1 the next setter was the previous front in 44,580 moves, not in
  15,464 (then several were carried in and the latest exit set the move); every hand-over was the front in 5,456 relays;
  C2 the most frequent setter is the fastest reading in 5,217 relays (ranks 1–5 the rest), 3–6 distinct setters per
  relay; C3 the front at the landing is a fast reading in most (rank 6: 6,264; 5: 3,735; 4: 2,926; …); edge cases: a front
  passing through within the move 2,293 moves, a re-entry 6.
- late fine band shapes (5,400): C1 79,338 against 21,997; all seven readings set moves in every relay; the most frequent
  setter is rank 5 or 6 in 5,220; C3 the landing front is rank 1–2 in 3,740.
- Case C (423 and 397 relays): C1 554 against 281, 484 against 277; the landing front mostly rank 4–6.

**Reading** `[reasoned from the run]`: the relay is mostly a **conveyor**: the reading nearest the entering edge arrives
before the current setter leaves and takes the next hand-over; the fast readings, which come round most often, carry
most of it. It ends at a move where the setter leaves before the front arrives: a **gap in the arrivals**. At the
landing the gap is where the fast readings are all clear (the fast part's own isolation) while the slow setter has just
left (the slow part clear).

**Consequence:**
- How the relay ends is now mapped in the cascade's objects (queue, front, carry-in, the gap). The gap is an instant where
  the fast part is isolated on its own and the slow part is clear: **the same statement as E151/E201 reached from the
  relay's side**: the fast part's own isolation intervals (lower order, native) must meet the slow part's clear intervals
  early. Three design steps (E202–E204) converge on it.
- What is now visible about why: the slow part's intervals are long (AP-like), the fast part's isolation intervals are
  fine-grained at the slow part's scale, so they meet early; they fail to meet early only where the slow part is near
  spread 7 (short intervals, E202) or the fast part is a crowd whose own isolation intervals are sparse (the late shapes).
- Next design question: the fast part's own isolation intervals, placed against the slow part's intervals: their spacing
  at the slow part's scale, read from the fast part's own structure (its own slow/fast split, recursively).

---

## E205 — 2026-09-30 — the fast part's isolation spacing: under one of its own laps, except for crowds

**Map:** `CASCADE_DESIGN_v2` §3–§4 · M2 (d), designed first · nearest §6 class F5 (the index criterion is forced: a check).

**Owner:** *"yes, design the fast part's isolation spacing first, then run it / Then lets review carefully if we are
progressing and check against drift"*.

**Design** (`LonelyRunner/experiments/nN/redo/e205_fast_spacing_v1.py` docstring): the fast part `F`'s own isolation
intervals (its own isolation events, which exist by the native lower order), measured in `F`'s natural unit, one lap of
its slowest reading (`8·d_min/f₁` in `R`). Forced: the landing is in the slow part's first interval `[1, 7/σ]` iff `F` has
an isolation point there; `F`'s gap at the start is its push (E202). Content: the gap at the start in `F`-laps, read
against `F`'s structure (spread `σ_F`, tightest internal ratio: a crowd).

**Run** (exact) `[VERIFIED — these populations]`; forced check 0 violations throughout:
- every set `≤ 24` with a fast part (210,335): first interval 210,104, later 231. `F`'s gap at the start, first-interval
  sets: none 64,967; `≤ 1/4` lap 110,463; `≤ 1/2` 26,288; `≤ 1` 8,123; `≤ 2` 260; `≤ 4` 3. Later sets: `≤ 1/4` 187, `≤ 1/2`
  42, `≤ 1` 2, with the slow part's spread 5–7 in all 231: the interval is short, the gap is not long.
- late fine band shapes (5,400): all later; `F` is a crowd (spread `≤ 4`, tightest ratio `≤ 1.2`) and its gap at the start
  is 1–4 of its laps (`≤ 2`: 2,780; `≤ 4`: 2,620), longer than the slow part's first interval.
- Case C (1,000 + 1,000): first interval 994 and 997; the gap exceeds one lap in 1 and 2 of them; the later landings have
  the slow part's spread 6.7–7.

**Consequence:**
- The two routes past the first interval are separate and each is named by the readings: a slow part near spread 7 (a
  short interval, the fast part's gap short), or a crowded fast part (a gap of one to four of its laps, the slow part's
  interval long). Everywhere else the fast part's gap at the start is under one of its own laps.
- Not established: why a non-crowded fast part's gap is under one lap, or how long a crowd's can be. Both are statements
  about the fast part alone (lower order).

---

## E206 — 2026-09-30 — review: are E197–E205 progressing, and have they drifted

**Map:** none — review of E197–E205 at the owner's request; nothing run.

**Owner:** *"Then lets review carefully if we are progressing and check against drift"*.

**1. The checklist, step by step.** E201–E205 each studied the cascade's own run (its moves, split into the slow part's
and the fast part's), each was designed before it was run, each recorded its checklist in the script, and every derived
check held (0 violations throughout). No instant family the cascade does not visit (the F14 of E193–E195), no rate given
as the answer, no count used as the argument, no first isolation, no other proof's machinery. Forced facts were marked
as checks each time (E201's "some interval", E202's index criterion, E204's queue rule, E205's criterion). **No frame
drift found.** One phrasing to correct: "almost always" (E201–E202 reports) reads as a rate; the content is the listed
exceptions and their mechanism, and reports should say it that way.

**2. Against the owner's plan (E199–E200).** Existence: settled (no first isolation used). AP/grid plus deviation: made
concrete at the one instant every arrangement has, the bound (E202): the slow part is clear there, AP-like, and the only
obstruction is what the deviation captured of the fast part. No gaps: the split applies to every arrangement (E201).
The cascade as the map of the displacement: E202–E204 map it (captures, separations, carry-ins, the conveyor, the gap).
**Not yet touched: the finiteness step** (the compact simplex of E199): the maps have not been connected to it.

**3. What is new against the record.** The gapless split (re-split until the slow part's spread is at most 7); the
landing's interval with exactly two routes past the first (E201, E205); the slow part's own move carrying the isolation to
its second interval on every set tested (E154 generalised); the run from the bound as captures at slots 0/7, passages of
AP-like clusters, a conveyor carried by the fast readings, ending at a gap in the arrivals (E202–E204); the fast part's
gap at the start under one of its own laps except for crowds (E205).

**4. What has not moved.** No forcing argument. Since E201 each step's consequence has come back to E151's statement
(2026-09-27): the fast part's own isolation meets the slow part's clear interval early. Four maps (index, sweep, queue,
spacing) reach it from four sides; the statement itself is unchanged. The maps are not wasted: they have **localised**
the difficulty. But a fifth map of the same statement would be circling (F4-adjacent: new coordinates for the open
statement).

**5. Where the difficulty now lives** `[reasoned from E201–E205]`:
- (i) a slow part near spread 7: a **wall of the split rule** (at spread exactly 7 the slow part's first interval
  shrinks to a point). The split has freedom (any threshold below 7 is still gapless), so this route may be removable by
  the choice of split, at the cost of a larger fast part. Untested.
- (ii) a **crowded fast part** (six readings within ratio about 4, neighbours within 1.2): its own isolation is sparse and
  its gap at the start runs to one to four of its laps. This is the region of E121's supremum shapes and E153's fine
  shapes, and the one E154 read through the cascade (the slow runner's own move, then the crowd lands in the second
  interval).

**6. Drift risks ahead, named now.** (a) "The fast part's gap is under one of its laps" is a when-at-the-latest shape
(F1) if made a lemma on its own; it may enter only as the content of a place statement (the landing lies in the slow
part's first interval). (b) Every count here is scoped to its window (E114's range caveat): crowds reached four laps on
these windows; nothing says how far they reach.

**7. What would move closer** (for the owner to choose): test whether a stricter split removes route (i) (a design
choice, applied to every arrangement, not a narrowing); then design the crowd's mechanism from the cascade (E154), which
would leave one region, named by the readings, for the proof to handle; and connect that region to the finiteness step
(where in the simplex the crowds lie).

---

## E207 — 2026-09-30 — E206's three steps: the stricter split removes route (i); the crowds are the band, already covered by certified cones

**Map:** `CASCADE_DESIGN_v2` §3; E206 §7 · M2 (d) for step 1; steps 2 and 3 answered from the record (source first; F7
avoided: the crowd mechanism and the band's cover were already on disk) · nearest §6 class F7.

**Owner:** *"Yes try tbhis"* (E206's order: a stricter split; the crowd's mechanism; crowds in the simplex).

**Step 1, the stricter split** (`LonelyRunner/experiments/nN/redo/e207_split_v1.{py,out}`; exact) `[VERIFIED — these
populations]`: re-splitting the lower part while its spread exceeds `s` still applies to every arrangement for every `s`
from 1 to 7 (a design choice, not a narrowing).
- every set `≤ 24`: `s = 7`: 231 landings past the slow part's first interval; `s = 5`: 2 (slow part spread exactly 5);
  **`s = 3, 2, 1`: none**.
- Case C (1,000 + 1,000): `s = 7`: 6 and 3; **`s ≤ 5`: none**.
- late fine band shapes (5,400): past the first interval at **every** `s`; the slow part is the slowest reading alone and
  every landing is in its second block `[9, 15]`.
So route (i) (a slow part near spread 7) was an artefact of the split rule. With the slowest reading alone as the slow
part (`s = 1`), every set here lands in its first block `[1, 7]`, except the late band shapes, which land in `[9, 15]`:
**E121's target, `R ∈ [1, 7] ∪ [9, 15]`, reached again from the cascade's run.**

**Step 2, the crowd's mechanism, on record** (read, not re-derived): E122 (owner: *"let the cascade teach how it
works"*): in the band the slowest runner's own window `(7, 9)` splits the range into copy 0 `[1, 7]` and copy 1
`[9, 15]`; from copy 0 to copy 1 every other runner's window lattice slides by the fraction `{sᵢ}` of its own period
(`R + 8` shifts runner `i` by `8{sᵢ}`) while the slowest runner does not slide: copy 1 is copy 0 re-arranged by the
deviations. E154 read the ten late cases through the cascade: the crowd runs out of shared blocks, the slowest runner sets
one move itself (its exit at 9), and the crowd lands one to five moves later.

**Step 3, where the crowds lie, on record:** the late shapes are **the band**, spread 7 to 9 in units of `d_min`: the AP
neighbourhood where R1 just fails. E123–E124: every `1 = s₀ ≤ … ≤ s₆` with `7 ≤ s₆ ≤ 9` lies in one of **105
lap-assignment cones**, each lonely at a named instant `R = maxᵢ (8kᵢ+1)/sᵢ` inside the slowest runner's block 0 or 1,
cut only along walls, certified exactly and independently checked `[VERIFIED — computer-assisted, exact]`. E125: strips
`[9,10]`, `[10,11]`, `[11,12]` covered and checked the same way (131, 168, 255 cones); `[12,13]` generated (308), not
checked; the count grows with the spread. This is the owner's finiteness (E199) already realised on a compact piece of
the simplex: a bounded-spread region, finitely many cones, each a named instant.

**Consequence:**
- The split's structure and the record's band work are one picture: spread `≤ 7`, the bound (R1, proved); spread 7 to 12,
  finitely many certified cones in the slowest runner's first two blocks; larger spreads, on every population here, the
  six others' own run lands in the slowest runner's first block.
- The remaining question is the owner's own from E125 (*"use the cascade to find why the categories exhaust, not
  enumeration"*): why a finite set of lap assignments covers each bounded-spread strip, and what carries the count as the
  spread grows (the fast readings wrap more laps). That is where the work stands.

---

## E208 — 2026-09-30 — E125's question in the band: the landing is the grid's own gap, reached after the deviation bridges earlier ones

**Map:** `CASCADE_DESIGN_v2` §2, §7; E125's open step · M2 (d), designed first · nearest §6 classes F14 (avoided: E128's
grid-class family was not used as the test, since with floor/ceiling positions and any odd class it would contain the
landing almost by construction, F5; the test is the cascade's own chain) and F2 (avoided).

**Owner:** *"yes, design E125's question in the band first, then run it / Then review if we need to prove it in lean
now"*.

**Design** (`LonelyRunner/experiments/nN/redo/e208_band_junctions_v1.py` docstring): the cascade's chain (E122, E125):
consecutive setters `(a, lap k)`, `(b, lap l)` join iff `J = s_b(8k+1) − s_a(8l−1) > 0`; the landing's **break** is the
queue front's next window, with `J ≤ 0`. On the slowest reading's own grid, `sᵢ = nᵢ + δᵢ` (nearest whole number plus
deviation), every slack splits exactly and linearly: `J = [n_b(8k+1) − n_a(8l−1)] + [δ_b(8k+1) − δ_a(8l−1)]`, the
**grid's** slack (a whole number; 0 at the AP's own junctions, where windows touch) plus the **deviation's** part
(amplified by the laps).

**Run** (exact) `[VERIFIED — these populations]`; checks (joins positive, breaks non-positive) 0 violations:
- every integer band set, readings `≤ 28` (86,470 chains): every landing in copy 0 `[1, 7]`. Breaks: **grid gap
  (grid slack < 0) 76,923**; grid tight, deviation negative 1,968; grid overlapping, deviation breaking it 7,579. Joins:
  grid overlap 75,401; grid tight held by the deviation 2,464; **a grid gap bridged by the deviation 20,712**.
- late fine band shapes (5,400): every landing in copy 1 `[9, 15]`. Breaks: grid gap 4,207; tight 46; overlap broken
  1,147. Joins: overlap 59,209; tight 6,064; grid gap bridged 36,062.

**Reading, in the owner's terms** `[reasoned from the run]`: the band's isolation is mostly **the grid's own gap** (the
AP/grid's isolation class) reached by the chain; the chain gets there after **the deviation has bridged earlier grid
gaps**, each bridge a linear condition on the deviations amplified by the laps. That is "AP/grid plus deviation,
relocated": the deviation carries the isolation from one grid gap to a later one; in the rest the deviation opens a gap
where the grid would join.

**Consequence:**
- E125's open step reads, in these objects: to pass both copies the deviation would have to bridge **every** grid gap in
  `[1, 7]` and in `[9, 15]`; each bridge is a linear condition on the deviations, and E124's emptiness certificates are
  exactly the conjunctions of such conditions that are inconsistent. A derivation would name the inconsistent
  conjunction (E125: for the AP it is exactly tight and the pair law is its two-runner case). Not derived here.
- Why copy 1 is reached only by the late shapes: there the deviation bridged 36,062 grid gaps over 5,400 chains (about 7
  per chain) against 20,712 over 86,470 in the integer band (about 0.24): the late shapes are the arrangements whose
  deviations bridge the grid's gaps across the whole of copy 0.

---

## E209 — 2026-09-30 — review: do we need to prove it in Lean now

**Map:** none — review at the owner's request; nothing built.

**Owner:** *"Then review if we need to prove it in lean now"*.

**What is already in Lean** (checked in the tree and the record):
- **The band theorem is proved:** `LRC.BandCover.band_lonely` (`Spec/BandCoverN.lean` with `BandCoverCoreN` and six
  `BandCoverTree*N` modules): seven real readings `1 ≤ s₁ ≤ … ≤ s₆` with `7 ≤ s₆ ≤ 9` are lonely; E124's certified cover
  re-checked by Lean; 289 of 289 declarations `[propext, Classical.choice, Quot.sound]`; no `sorry`, no
  `native_decide`; builds one module at a time (about 53 min, 7.9 GB peak) (E170, E172). **Untracked**, about 20 MB of
  generated Lean, and **imported by nothing on a route to `LonelyRunnerAt8`**.
- The route in the tree: `lonely_of_gridStep8` from **`Cover8 M`** (`Spec/RegimeSkeletonN.lean:71`, OWED): every set of at
  most seven readings has its bound clear or a grid class with step at most `M`. The reductions around it (`SlowBlockN`,
  `TwoBlockN`, `NestedBlocksN`, `GridPairLawN`, `lonely_eight_of_pairwise_laps`) are proved and tracked.

**What E201–E208 add that Lean could take now:** only small derived facts (the split exists; inside the slow part's clear
interval only the fast part obstructs, a corollary of `exists_block_iff_fast_lap`; the junction slack split, algebra).
Everything else in those entries is a map `[VERIFIED — populations]`, not a theorem.

**Assessment** `[reasoned]`:
1. **The band: yes, bank it.** It is finished, axiom-clean, and it is exactly the region the cascade work isolates as
   needing the slowest runner's second block (E201, E205, E207, E208). What is owed is not a proof but a decision: commit
   the modules (size and build cost), then wire `band_lonely` into the route (the band part of any covering). The
   commit needs the owner's go-ahead (generated files of this size; the build time).
2. **The strips 9–12: no, not now.** Certified in Python (E125) and generable into Lean the same way, but the number of
   cones grows with the spread (131, 168, 255, 308, …), so strip by strip cannot close the unbounded spread, and the owner
   asked for derivation over enumeration (E119, E125, E126).
3. **The general case: not yet.** There is no theorem to formalise: E125's inconsistency (the deviation cannot bridge
   every grid gap in both copies) is now visible from the cascade's side (E208) but not derived. A derivation would be
   uniform in spread and far smaller in Lean than certificates, and could replace the 20 MB cover.
4. **A check owed before more Lean on the route: `Cover8 M` as written.** It asserts one step bound `M` for every set.
   The steps needed grew with the spread on the populations (E157: up to 4 on Case B and Case C to 32, up to 7 on random
   wide sets), and nothing on record shows a fixed `M` suffices. A `def … : Prop` is type-checked, never proved (F8,
   `DoorFirstLap`), so whether a fixed `M` can hold must be checked before anything is built on it.

---

## E210 — 2026-09-30 — the band cover committed; E209 corrected; `Cover8 M` checked as written: `M = 2` suffices, and only the band needs 2

**Map:** none — housekeeping (a commit) and a check of an OWED statement's truth (F8), at the owner's direction.

**Owner:** *"yes commit the band cover, then check Cover8 M"*.

**The band cover, committed** (`LonelyRunner/` `388793f`): `BandCoverCoreN`, `BandCoverN`, `BandCoverTree{2,3,4,17,18,19}N`,
the generators `experiments/nN/redo/gen_band_lean_v1.py`, `gen_band_lean_v2.py`, `gen_band_lean_v2_driver.py`, the build
logs and the axiom check. Before the commit: a scan for `sorry`, `native_decide`, `admit`, `unsafe` (the only matches are
docstring sentences); `lake build LonelyRunner.LRC.Spec.BandCoverN` against the current tree, 8,258 jobs, exit 0;
`#print axioms LRC.BandCover.band_lonely`: `[propext, Classical.choice, Quot.sound]` `[PROVED — Lean]`. The modules'
running record is E169, which is in the E167–E169 gap noted in E170. Still imported by nothing on a route to
`LonelyRunnerAt8`.

**Correction to E209 point 4.** E209 said the steps needed "grew with the spread (E157: up to 4 …, up to 7 …)". That read
E157's grid divisor `mm` as `Cover8`'s bound `M`; they differ (`Cover8 M` bounds the step `e/mm` below by `m/M`, and `e`
can be any reading). The record already had the direct measurement (E165, in the docstring of `RegimeSkeletonN`):
`Cover8 2` on every population tested. F7 on the session's part.

**`Cover8 M`, checked as written** (`LonelyRunner/experiments/nN/redo/cover8_check_v1.{py,out}`; an implementation from the
Lean definitions, not from E165's script; pairwise laps decided as 1-D Helly, as `lonely_eight_of_pairwise_laps`)
`[VERIFIED — these populations]`. Least `M` per set (0: the bound is clear):
- every subset of `1..16` with 1 to 7 readings (26,332; sets with fewer than seven readings are inside `Cover8` and were
  not in E165): 0 in 16,513, 1 in 9,819;
- every 7-set `≤ 20` (77,520): 0 or 1; every tenth 7-set `≤ 24` (34,611): 0 or 1;
- the late fine band shapes (5,400): **2** in all; the band's extremal shape (E121): 1; the six-crowd shapes with a slow
  runner (E153/E154, 104): 0 in 5, 1 in 93, **2** in 6; random sets of 2 to 7 readings up to 2,000 (3,000): 0 or 1.
- **No set needs `M ≥ 3`.** Every set needing `M = 2` has spread in the band: the six crowd shapes 7.11 to 8.72, the late
  shapes 7.005 to 7.44 (the step `m/2` with class 5 or 7: the slowest reading's second block, E207).

**Consequence:**
- `Cover8 2` stands on every population, now including the sets of fewer than seven readings: no sign that it is false
  as written. It remains OWED (unproved).
- **A route the tree now allows** `[reasoned; not built]`: the only sets needing `M = 2` lie in the band, which
  `band_lonely` proves for every real shape. So `LonelyRunnerAt8` would follow from: spread `≤ 7` (the bound, R1, proved);
  at most six readings (order seven, native, proved); spread 7 to 9 (`band_lonely`, proved); and, owed, **grid step at
  least `m` (`M = 1`) for seven readings of spread above 9**. That owed statement is strictly smaller than `Cover8 2`
  and holds on every population here. Building it means a new theorem and a new OWED entry in the Spec gate's register.

---

## E211 — 2026-10-01 — design: the band route (`band_lonely` wired in; what stays owed is `WideStep8`)

**Owner:** *"yes, design the route first, then build it in lean"*.

**Map:** v2; §5 (the owed forms of the obligation) and §9 (M7). This step draws the consequence of `band_lonely`
(E169, committed `388793f`), a class (c) result uniform over every real band shape. The wiring itself is not a proof step.
Nearest §6 classes: F13 (a consequence not drawn; this step is the remedy for `band_lonely`); F4 (a restatement taken for
a step; not this, since the new owed statement is implied by `Cover8 M` and is not equivalent to the obligation); F8 (a
false `def … : Prop`; guarded by the check below, run before it is registered).

**Correction to E210's Consequence line.** It said the owed statement for spread above 9 at `M = 1` is "strictly smaller
than `Cover8 2`". That is wrong: it has a smaller domain but a tighter step (`m`, not `m/2`), so neither implies the other.
The right comparison is at equal `M`: the restricted statement `WideStep8 M` below is implied by `Cover8 M` (a Lean lemma
below), and the populations show `M = 1` suffices on it while `Cover8` needs `M = 2`.

**The route** (seven readings; least reading `m`; greatest `W`):

| case | discharge | status |
|---|---|---|
| at most six readings | native order seven at `1/7` (`lonely_eight_of_card_le_six`) | proved |
| `W ≤ 7m` | the bound `1/(8m)` (R1, `lonely_eight_of_spread`) | proved |
| `7m < W ≤ 9m` | `band_lonely` with `sᵢ = dᵢ/m`, instant `t/m` | proved; wiring owed (this step) |
| `9m < W` | `WideStep8 M`: `GridStep8 S m M` | **OWED** |

**Forced before anything runs (M4):**
- F-a. The four cases are exhaustive (trichotomy on `W` against `7m` and `9m`, after the split on the number of readings).
- F-b. The band case needs only the order of the readings: `1 ≤ s₁ ≤ … ≤ s₆`, `7 ≤ s₆ ≤ 9` is `band_lonely`'s hypothesis
  verbatim, and dividing by `m` rescales time (the AP is scale invariant).
- F-c. `Cover8 M → WideStep8 M` (a restriction of the domain).
- F-d. **The place `WideStep8 1` names.** In its grid-class disjunct the slowest reading `m` sits at grid point `n` with
  `n·e < mm·m + e ≤ 2e`, so `n = 1`, `c·n ≤ 7` and its lap is 0. The 1-D Helly instant (the largest left end of the
  assigned clear blocks) therefore lies in `m`'s lap-0 block: `1 ≤ 8mt ≤ 7`, the slowest reading's first clear stretch.
  The bound disjunct is `8mt = 1`. So the owed statement says: *above spread 9, the subject is isolated inside the slowest
  reading's first clear stretch, at a grid-class instant of a grid through one of its own readings with step at least
  `m`*. That is a place given by the readings. It says nothing about the cascade's landing, and none is claimed.

**Checklist.** Objects: the readings' order, spread (the gap simplex's own coordinate), laps and clear blocks, the grid
through a reading (AP/grid plus deviation). No density, rate, coverage, instant family or first isolation. "First clear
stretch" is the slowest reading's lap-0 block, a fixed interval, not a first isolation.

**Check before registering** (F8; CLAUDE.md §3): `WideStep8 1` as written, on seven-reading sets of spread above 9:
exhaustive small ranges, random wide sets, and fine shapes just above 9 (the edge next to the band, where the band needed
the second block). Every set failing `M ≤ 1` is listed.

**Build.** A new module `LRC/Spec/BandRouteN.lean` (namespace `LRC.BandRoute`), so as not to touch the uncommitted edits
of another session in `RegimeSkeletonN.lean` and `TwoBlockN.lean`; it uses only committed declarations.
- `lonely8_of_band`: seven readings with `7m < W ≤ 9m` are lonely.
- `WideStep8 M` (`def … : Prop`, registered OWED in `scripts/nN/spec_gate.sh`).
- `wideStep8_of_cover8 : Cover8 M → WideStep8 M`.
- `lonelyRunnerAt8_of_wideStep8 M : WideStep8 M → LonelyRunnerAt8`.
- `gridStep8_one_first_stretch`: F-d in Lean.
Done-check: build the explicit target, `#print axioms` on each declaration, the hygiene scan, and the gate's register
check for the new `Prop`.

---

## E212 — 2026-10-01 — the band route built: `LonelyRunnerAt8` from `band_lonely` and `WideStep8 M`; `WideStep8 1` checked, including an adversarial walk

**Map:** v2; §5 and §9 (M7 consequence of `band_lonely`), as designed in E211. The checks are class (d) (derivation
checks and a check of an owed statement's truth, F8); the Lean is wiring plus one derived place (F-d). Nearest §6: F5
(a forced fact reported as a finding), which hit this entry twice and is recorded below.

**Built** (`LonelyRunner/LRC/Spec/BandRouteN.lean`, namespace `LRC.BandRoute`) `[PROVED — Lean]`:
- `lonely8_of_band`: seven readings with least `m` and greatest in `(7m, 9m]` are lonely (order the readings, divide by
  `m`, `band_lonely`, rescale by `1/m`).
- `WideStep8 M` (`def … : Prop`): seven readings, least `m`, some reading above `9m` → `GridStep8 S m M`. Registered
  **OWED** in `scripts/nN/spec_gate.sh`.
- `wideStep8_of_cover8 : Cover8 M → WideStep8 M`.
- **`lonelyRunnerAt8_of_wideStep8 M : WideStep8 M → LonelyRunnerAt8`**, for every `M`. Cases: at most six readings (order
  seven), `W ≤ 7m` (R1), `7m < W ≤ 9m` (`lonely8_of_band`), `9m < W` (`WideStep8 M`).
- `gridStep8_one_first_stretch`: `GridStep8 S m 1` gives a lonely `t` with `1 ≤ 8mt ≤ 7` (E211 F-d).

Evidence:
- `lake build LonelyRunner.LRC.Spec.BandRouteN`: 8,352 jobs, exit 0 (`experiments/nN/band_route_build_v1.log`). The only
  warnings in the module are line length. It was rebuilt, exit 0, after a docstring-only edit made after the gate run.
- `#print axioms` on all four theorems: `[propext, Classical.choice, Quot.sound]` (`experiments/nN/band_route_axioms_v1.out`).
- Spec gate PASS (`experiments/nN/band_route_spec_gate_v1.out`): 143 modules, no `sorry`, hygiene clean, 2,413 of 2,413
  declarations axiom-clean, 88 Prop-valued defs all registered, `LRC.BandRoute.WideStep8` on the OWED list, tree digest
  `21392f5945c1`. The gate builds every module on disk, so the pass covers other sessions' uncommitted modules as they
  stood.
- Only committed declarations are used. `RegimeSkeletonN.lean` and `TwoBlockN.lean` carry another session's uncommitted
  edits and are untouched; every declaration used was confirmed present at `HEAD`.

**`WideStep8 1` checked as written** (`experiments/nN/redo/wide_step_check_v1.{py,out}`, `_v2.{py,out}`; `least_M` from
E210's independent implementation) `[VERIFIED — these populations]`. Least `M` (0 = the bound is clear):

| population (seven readings, spread above 9) | sets | 0 | 1 | ≥ 2 |
|---|---|---|---|---|
| every 7-set of readings ≤ 20 | 37,660 | 15,658 | 22,002 | 0 |
| every tenth 7-set ≤ 24 | 16,767 | 6,451 | 10,316 | 0 |
| random 7-sets ≤ 2,000 | 4,000 | 1,016 | 2,984 | 0 |
| fine shapes (least 1,000), spread (9, 9.5] | 4,000 | 1,016 | 2,984 | 0 |
| fine shapes, spread (9.5, 12] | 3,000 | 971 | 2,029 | 0 |
| six-crowd shapes, top just above 9 | 200 | 0 | 200 | 0 |
| v2: late band shapes, one middle reading moved to (9m, 9.5m] | 67,407 | 0 | 67,407 | 0 |
| v2: fine shapes, spread (9, 9.2], a reading in (7m, 9m) | 6,000 | 0 | 6,000 | 0 |

- **F5, first instance.** v1's "edge" population (each late shape's *top* reading moved above `9m`: 27,000 sets, all 0)
  is bound-clear by construction: the other six readings lie in `[m, 7m]` and the moved one in `[9m, 15m]`. It tested
  nothing and is not in the table. v2 replaces it with sets that keep a reading blocked at the bound (checked: 0
  bound-clear in both v2 populations).
- The identical counts of rows three and four were checked element by element: the populations share no set, 1,494 sets
  differ in least `M`, and the totals coincide.

**Adversarial walk** (`wide_first_stretch_walk_v1.{py,out}`). By `gridStep8_one_first_stretch`, a wide set with no clear
`R = 8mt` in `[1, 7]` refutes `WideStep8 1`. This walk is the one that found the late shapes inside the band: 300 walks
of 4,000 steps, spread `(9, 12]`, keeping moves that do not widen the widest clear interval in `[1, 7]`.
- **No wide set with an empty first stretch was reached.**
- The tightest set is `(27720, 85358, 117495, 140959, 159149, 200880, 258489)` (spread 9.325). Its first stretch is two
  isolated points, `R = 1320/373` and `2200/373` (`wide_first_stretch_tight_v1.out`). Both points are held by one pair
  in exact ratio `258489/117495 = 11/5`, in opposite orientations: at `1320/373` the pair reads 15 and 33 (entering edge;
  exit edge), and at `2200/373` it reads 25 and 55 (exit edge; entering edge). Moving the ratio off `11/5` opens one
  point while the other closes. That is E125's pair law at one exact mirror resonance. Every other walk ends with an
  interval of width at least about `10⁻⁸`.
- **F5, second instance.** `wide_first_stretch_pins_v1.out` reports "one pair at both ends" for the 25 tightest sets.
  That is forced: every clear interval opens at some reading's exit and closes at another's entry. Only the single-point
  set's two-point mirror is unforced.

**Consequence:**
- **The owed statement shrinks** (§5 routes) `[PROVED]`. `LonelyRunnerAt8` now follows from `WideStep8 M`, which
  `Cover8 M` implies at every `M`. Seven readings of spread at most 9 are proved (orders three to seven, R1, the band).
  What is owed is seven readings of spread above 9, and the populations say `M = 1` suffices there. `Cover8` stays
  registered as a sufficient route; neither statement is refuted.
- **The owed statement names a place** (place test) `[PROVED]` for `M = 1`. A wide set in `WideStep8 1` is isolated inside
  the slowest reading's first clear stretch, at a grid-class instant of a grid through one of its own readings with step
  at least `m`. It says nothing about the cascade's landing.
- **A new map question for v3 (Q7)** `[reasoned]`: why the slowest reading's first clear stretch can close when the spread
  is 7 to 9 (the late shapes) and did not close above 9 in any population or walk. The lead is the tight set's mirror pair
  `11/5`, E125's pair law at an exact resonance. Its three answers (M3) are not given: status "not understood".
- **Where else** `[reasoned]`: the same wiring would take any further certified strip (E125's `[9,10]`, `[10,11]`,
  `[11,12]`, certified in Python) off the owed domain. The owner stopped strip enumeration in E125 (*"use the cascade to
  find why the categories exhaust, not enumeration"*), so this is not proposed.
- **Standing questions:** E210's comparison with `Cover8 2` is corrected (E211). None other found (grep of v21 §17 and the
  map's §4 for "owed", "standing question", "author's ruling").
- Owed to map v3: C7's fix; E192–E212; Q7; the two F5 instances here.

**Note on E212's standing-questions line.** That line was written before the grep ran; the grep was run afterwards. v21
§17G lists two pending author's rulings. `EightResidual`'s is answered by C1. The other is first-lap clearance (§15I;
provisional since 2026-09-25): every reading on lap 0 at a flank opening `A/(8e)`. `WideStep8 1` does not use it and does
not settle it, because only the slowest reading is on lap 0 there and the others may be on any lap. So the line stands
as written. The two uses of "first" name different objects.

**Audit note (2026-10-01).** The map-first audit (memory `feedback_n8_map_first`) flags E200 and E209 for a grade tag
with no `**Consequence:**` line. In both the tag cites an earlier result and records no new one: E200 cites `SlowBlockN`
`[PROVED]`, and E209 cites earlier populations as `[VERIFIED]`. **Consequence** for both: none new. The log is append-only,
so the audit will keep listing these two; the map v3 cut should carry this note.

---

## E213 — 2026-10-01 — design: the Q7 map run (why the slowest reading's first clear stretch closes only in the band)

**Owner:** *"yes, design the Q7 map run first, then run it"*.

**Map:** v2 plus Q7, which is owed to v3 (E212's Consequence line). §1 objects: the cascade's slot boundaries (a reading's
exit `(8k+1)/s` and entry `(8k−1)/s`, in `R = 8mt` with readings `s` in units of `m`), the landing, and the entering queue
(E204). §4 question: Q7. M2 class (d), a map run: its only pass conditions are derivation checks and the oracle check.
The exception is the tight wide set of E212. Nearest §6 classes, and why this step is none of them:
- F11 (a new vantage in place of reading an exception): not this, since the run reads that exception itself.
- F14 (an instant family the cascade does not use): not this, since exits and entries are the cascade's own instants.
- F5 (a forced fact reported as a finding): guarded by the list below.

**Q7.** The walk reached sets of spread 7 to 9 whose first clear stretch `[1, 7]` is empty (the late shapes). Above 9 it
did not, in any population or walk (E212). The tightest wide set, `(27720, 85358, 117495, 140959, 159149, 200880, 258489)`,
keeps two clear points, both held by the pair `117495 : 258489 = 5 : 11` in mirror orientation.

**Forced before running (M4):**
- M4-1. `R` is clear iff every reading sits in `[1, 7]` mod 8. The least clear point of `[1, 7]`, if there is one, is
  `R = 1` or some reading's exit. So the first stretch is empty iff the bound is blocked and every exit in `(1, 7]` lies
  inside another reading's open window: the cascade's own condition that the exit is not a landing.
- M4-2. A move of one reading shifts only that reading's windows. Speeding it up uncovers a sliver just before each of its
  old exits; slowing it down uncovers a sliver just after each of its old entries.
- M4-3. The mirror algebra. For readings `a < b`, "`b` exits lap `K` where `a` enters lap `l`" means
  `s_b/s_a = (8K+1)/(8l−1)`. "`a` exits lap `k` where `b` enters lap `L`" means `s_b/s_a = (8L−1)/(8k+1)`. Both hold at
  one ratio iff `(8K+1)(8k+1) = (8l−1)(8L−1)`. Moving the ratio off that value opens one junction and closes the other.
  At the tight set, `33·25 = 15·55 = 825`, with `K = 4`, `l = 2`, `k = 3`, `L = 7`.

**The three answers sought (M3), and the part that serves each.**
- (i) The feature: is the mirror pair at an exact resonance specific to the tight set, or present wherever a wide set is
  close to closing? Part B.
- (ii) What forces the witness: when a move covers the landing's exit, where the cascade lands next, and whether that
  place is uncovered by the same move (M4-2). Parts A and B, contrasted with the band's closures in Part C.
- (iii) Main mechanism in disguise (§2A: grid-class clearance, separation, readings carried over an entering edge), or
  new: the tight set's two junctions split into grid slack and deviation, as in E208. Part A.

**Parts:**
- **A. The tight set, perturbed through the cascade.** Move one reading (the least fixed as the scale) by
  `δ ∈ {±1, ±3, ±10, ±30, ±100, ±300, ±1000}` at scale 27,720. Record the exact cascade's landing `R`, its setter and its
  queue front (E204), and whether it lies in `[1, 7]`. Also record the grid/deviation split of the two tight junctions on
  the slowest reading's grid.
- **B. The walk's 300 final wide sets.** Apply every such move to each set, and classify where the cascade lands next
  against the landing's interval before the move:
  - `s`: the same interval;
  - `e`: another interval that was already clear;
  - `n`: a place newly uncovered by the move;
  - `m`: `n` bounded by the old landing's pair, in mirror orientation;
  - `x`: beyond 7, the first stretch emptied.

  Each `x` is listed individually.
- **C. The band's closures.** Run the same walk with spread in `(7, 9]`, recording every step that empties the first
  stretch. At each, record:
  - the moved reading;
  - the slivers its move uncovered (M4-2);
  - which reading covers each sliver afterwards, and on which lap;
  - whether that reading bounded the interval that closed.

  B shows what stays uncovered above 9, and C what covers it in the band.

**Checks** (the only pass conditions):
- C1 (oracle): the cascade's landing equals the least clear point computed without the cascade (`clear_set` on
  `[1, 40]`), on every run.
- M4-1: that least point is `R = 1` or an exit, on every run.
- M4-3 at the tight set.

**Checklist.** The objects are the cascade's boundaries, its landing and its queue. The first stretch is a fixed interval
of the slowest reading, not a first isolation. Counts in B and C are records of a map, with the exceptions listed; none
is the answer. No rate, no instant family beyond the cascade's own exits and entries, no stopping shape. The perturbation
is the owner's tool (E67, E98): *"each isolation is pushed there by the speed"*.

---

## E214 — 2026-10-01 — the Q7 map run: the tight wide set is the grid pair law's mirror on the arrangement's own grid; Q7 sharpened to the closing pair's mirror junction

**Map:** v2 plus Q7 (owed to v3); §1 slot boundaries, landing, queue; §4 Q7; M2 (d), a map run as designed in E213;
nearest §6 class F5, which this entry guards (two forced counts marked below).

**Checks** `[VERIFIED — every run]` (`LonelyRunner/experiments/nN/redo/q7_map_run_v1.out`, `_v2.out`, `_v3.out`):
- C1 (the cascade's landing equals the least clear point from `clear_set`, no cascade): 0 failures across parts A, B
  and C.
- M4-1 (that point is `R = 1` or an exit): 0 failures.
- M4-3 at the tight set: the ratio is `11/5` and `33·25 = 15·55`, and both junction equalities hold exactly.

**A. The tight set, perturbed through the cascade** (`q7_map_run_v1.out` A):
- The landing is `R = 1320/373`. Its setter is `258489` (exiting) and its queue front is `117495` (entering).
- **Only the pair acts locally.** Moving `117495` faster, or `258489` slower, sends the landing to the mirror point
  `R ≈ 5.898`, where the roles swap: setter `117495`, front `258489`. Moving `117495` slower, or `258489` faster, keeps
  it at `R ≈ 3.539`, where that point opens into an interval. This holds for 26 of the 28 pair moves. The other two,
  `117495` by `+300` and `+1000`, go to a new junction with `159149` near `R = 4.0`.
- **The other four readings are slack.** Moves up to `±300` leave the landing where it is. Only moves of `±1000` open
  intervals elsewhere, two of them earlier.
- **The split of the two tight junctions** (E208), on the slowest reading's grid: "`258489` exits at 33, `117495`
  enters at 15" has grid slack `+3` and deviation `−3`; "`117495` exits at 25, `258489` enters at 55" has grid slack `−5`
  and deviation `+5`. One is a grid gap closed by the deviation, the other a grid overlap opened by it.

**The three answers for E212's exception, the tight set** (M3):
- **(i) The feature** `[VERIFIED — exact, v3 (2)]`. The pair sits exactly on the grid through its own reading `117495`
  with divisor 5, at grid points 5 and 11 (deviation 0). The two clear points are classes `c = 3` and `c' = 5 = 8 − 3`.
  At class 3 the pair reads `15 ≡ 7` and `33 ≡ 1`; at class 5 it reads `25 ≡ 1` and `55 ≡ 7`. The pair takes the two
  edges and swaps them. The other five readings sit at interior grid residues (2 to 6 mod 8) in both classes.
- **(ii) What forces the witness** `[derived (M4-3) + VERIFIED (A)]`. The two edge conditions are one ratio, so any move
  of the pair opens exactly one of the two class instants, and the cascade lands at the one that opens.
- **(iii) The main mechanism in disguise** `[VERIFIED for the arithmetic; reasoned as a reading]`. For the pair, yes: it
  is the mirror of `GridPairLawN.grid_pair_law` (the module of map §2A's first row) on the arrangement's own grid.
  Three of the other five deviate by more than that lemma's `1/C` hypothesis allows (`85358` by `−0.37`, `159149` by
  `−0.23` and `200880` by `−0.45`, against `1/5`), yet all five are clear at both class instants. So the lemma as stated
  does not cover this set; its mirror is what holds the witness.
- Status in map §3 (v3): **answered for the tight set**.

**B. The 300 extremal wide sets, every one-reading move of up to `±1000`** (`q7_map_run_v1.out` B; split in `_v2.out`;
listed in `_v3.out`):
- **No move empties the first stretch** (`x = 0` of about 25,000 moves).
- **261 moves cover the interval holding the landing.** The cascade then lands:
  - at the same pair's mirror junction (the other class): 140;
  - at an interval that was already clear: 106. **Forced** (F5), since every one of these sets had another clear
    interval and the landing is the least clear point (checked, 106 of 106);
  - at a new junction: 15, listed individually. Each pairs the moved reading, or the old pair's partner, with a third
    reading.
- 123 further moves leave the old interval clear and open an earlier one; that is a different event.
- Of the 155 covering moves not forced to an existing interval, 140 go to the pair's mirror.

**C. The band's closures** (`q7_map_run_v1.out` C; 32 of 600 walks with spread `(7, 9]` emptied the first stretch):
- Every closing move started from exactly one clear interval (32 of 32). The moved reading bounded that interval in 22,
  and in 10 a third reading's window slid over it.
- After closure the landing is at `R` 9 to 11. `R ≥ 9` is **forced** (F5): the slowest reading is in the way on
  `(7, 9)`.
- Each closing move uncovered 2 to 6 slivers of its own windows (M4-2), 138 in all. Every one is covered afterwards: by one
  reading in 104 cases, by two in 33, by three in 1. The coverer bounded the closed interval in 34 cases; in the other
  104 it is a third reading.

**Consequence:**
- **Q7 is not answered; it is sharpened** `[VERIFIED — these runs]`. The object is now the pair law's other class, the
  closing pair's mirror junction. Above spread 9, at the extremal sets, it opens in 140 of the 155 covering moves that
  are not forced. In the band's closures, every place a closing move uncovers is covered. The next map run should
  locate the closing pair's mirror junction at each band closure, using the M4-3 algebra, and record its slack (grid plus
  deviation) and what covers it. It should do the same at the wide extremal sets, so the two are compared on one object.
  Status in map §3: **not understood**.
- **The extremal wide configurations reach §2A's mechanism** `[reasoned]`: the tight set is `grid_pair_law`'s mirror on
  the arrangement's own grid. The lemma's small-deviation hypothesis is stronger than what the set uses: the others need
  only be clear at both class instants. A two-instant form of the pair law (the pair cannot block both classes) is a
  candidate lemma. As a statement with "the others clear at both instants" among its hypotheses it is close to a
  restatement (F4), so it is recorded, not proposed.
- **Where else:** the band's late shapes are the place to look for the mirror's absence. That is the next run above.
- **Standing questions:** none answered. v21 §17G's first-lap clearance is untouched (E212 note).
- **Owed to map v3:** Q7 as sharpened; the tight set's three answers (a new §3 entry); the F5 instances of E212 and this
  entry; E192–E214.

---

## E215 — 2026-10-01 — review before the mirror-junction run: E212–E214 drifted into the first window and covering; the run as proposed is not run

**Owner:** *"yes, design the mirror junction run first, then run it but before you do.  Stop and think are we chasing
the correct target, native framework, are we introducing any density or coverage or other things from other frames
before we go on"*.

**Map:** none — review at the owner's request; nothing run. Checked against object register v3 items 2, 4 and 15, the
two order-eight memories on the cascade as oracle and on imports, and `Target.lean:160`.

**The target is right; the object drifted.** The target is `LonelyRunnerAt8` through the framework's mechanism (AP/grid
plus deviation; the cascade maps where the displacement is relocated). The band route's Lean (E212) serves it. From E212
on, the object of study slid away from it:

1. **The first window** (register v3 item 15, **MISPLACED**; owner: *"I never thought the first window/cycle was a
   requirement and think it keeps getting introduced from context loss and revert to training data."*). `R ∈ [1, 7]` is
   the slowest reading's first window `mt ∈ [1/8, 7/8]`. E212 called it "the place `WideStep8 1` names" and made it Q7's
   object. The place is the grid-class instant. That it falls in the first window is a by-product, like "first" in the
   landing (E109 O1).
2. **Covering** (register item 4, **NOT APPLICABLE**: *"Covering forms a complement; the construction forms none"*; §6.1
   requires proofs to be pointwise; item 2, blocking, **MISPLACED**). Q7 asked whether the readings' windows can fill
   `[1, 7]`. E213's M4-1 and E214's Part C ("slivers", "covered by", "what covers it") are statements about a union of
   windows over a stretch of instants. The mirror-junction run as proposed ("records … what covers it") continues this.
   The words appear 6, 9 and 10 times in E212, E213 and E214. In those parts the cascade appears only as an oracle check.
3. **A hard-case hunt** (oracle memory: *"Do not hunt for the 'hardest' ones by nearness to the half lap"*; E83). E212's
   walk ranked sets by the widest clear interval inside the first window: a length, and nearness to a fence. As a truth
   check of `WideStep8 1` its logic stands, because an empty first window would refute it. But its extremal set then
   became "the exception", although no explanation had failed on it, and it became Q7's object.
4. **A cap in the owed statement.** `WideStep8 1` implies a lonely instant with `8mt ≤ 7` (`gridStep8_one_first_stretch`,
   proved), so on wide sets it implies that the cascade never leaves the slowest reading's first lap. That is the shape of
   `DoorFirstLap` (`Doors.lean:339`, **REFUTED**), on a smaller domain. The obligation of record has *"No quantifier over
   time, no iteration, no cap"* (`Target.lean:160`). The route `lonelyRunnerAt8_of_wideStep8` holds for every `M`, so the
   cap is my choice of `M = 1`, read off the data. It is not refuted, and nothing in the framework demands it.
   `Cover8 M` has the same property at any uniform `M`: another session's uncommitted `gridStep8_two_bounded` states
   `8mt ≤ 15` at `M = 2`. The dilemma is on disk: without a step bound the statement is loneliness renamed (the tree's own
   note, and map C4); with a uniform step bound it is a cap.
5. **Density, rates:** none used as an argument. Counts were given as records. "140 of 155" was used as evidence for a
   sharpened question, which leans towards F3 (a majority rule stated as a law); flagged.

**How it entered** (for map §6): through consequences, not through a method. E207 recorded that only the band needs the
slowest reading's second block. E210 found that only band shapes need `M = 2`. E211 and E212 chose `M = 1` for the wide
statement, proved its by-product (the first window), and named that by-product the place. Q7 then took the by-product as
its object, and the walk and the covering instruments followed. Each step was checked for density and rates; none was
checked against register item 15.

**What stands:**
- The band route in Lean: `band_lonely` wired in; `lonelyRunnerAt8_of_wideStep8` for every `M`.
- `gridStep8_one_first_stretch`, a true theorem. The fault is the reading put on it, not the theorem.
- The truth checks of `WideStep8 1`, as F8 guards.
- E214's answer (iii), which is native: at the extremal set, the class instant is chosen by the sign of the pair's
  deviation on the arrangement's own grid (`GridPairLawN.grid_pair_law`'s mirror). That is *"each isolation is pushed
  there by the speed"* in the framework's objects: a place, from the grid plus the deviation.

**Not done, pending the owner:**
- The mirror-junction run as proposed.
- Q7 as framed: withdrawn from the map questions, to go into map v3 §6 as this entry's failure.
- The E212 wording in `BandRouteN`'s docstring ("the place `WideStep8 1` names … first clear stretch"), to be corrected
  in place.

**Consequence:** none for the proof. This entry changes what the next step studies, not what is proved.

---

## E216 — 2026-10-01 — design: the re-aimed run (the class instant on the arrangement's own grid, what selects it, how the speed moves it)

**Owner:** *"yes re-aim it, fix the docstring and record the memory"*. The docstring fix is `LonelyRunner` `6107511`. The
memory is with the `memory-drafter` agent. Q7 as framed in E212–E214 is withdrawn (E215), to go into map v3 §6.

**Map:** v2 §2A row 1 (`GridPairLawN`: the grid pair law, the grid-class clearance), §1's certificate and opening
objects, v21 §6.10's candidate scales (Theorem 6.15, the obligation of record). No map §4 question yet: this step
continues E214's answer (iii). M2 class (d), a map run. Nearest §6 classes:
- F14 (an instant family the cascade does not use). Every instant here is a reading's opening `(8K+1)/(8a)`, the
  cascade's own kind of instant and the landing's kind (map C4). The landing is recorded against them in every set.
- F4 (a restatement taken for a step). See M4-6.
- F1 (a cap) and item 15 (the first window). There is no window, the laps are unrestricted, and `M` is a coordinate.

**Object.** A grid through one of the arrangement's own readings `e` with divisor `mm` (step `e/mm`). Each reading `d`
has grid point `n = round(mm·d/e)`. A class `c ∈ {1, 3, 5, 7}` gives residues `r = c·n mod 8`.
- The **class instant** is the opening of the reading `a` on the class's leaving edge (`r_a = 1`),
  `t = c·n_a/(8·d_a)`. That is `a`'s opening at lap `K = (c·n_a − 1)/8`: the candidate scale `d_a/(8K+1)`, pointwise and
  exact.
- At `t`, each reading sits at `p = c·n_a·d/d_a = c·n + ε`, where `ε` is its deviation relative to `a`'s grid point (the
  pair law's rescaling `ν = n_a/x_a`).
- The reading is clear iff `p mod 8 ∈ [1, 7]`, and the class instant is lonely iff all seven are.

**Forced before running (M4):**
- M4-1. A lonely class instant is a clear candidate scale, so it witnesses Theorem 6.15 at that set.
- M4-2. The mirror class `8 − c` maps every residue `r ↦ (8 − r) mod 8`. Interior residues stay interior, `1 ↔ 7`, and
  `0` stays `0`. A reading whose grid point is a multiple of 8 sits at residue 0 in every class of that grid.
- M4-3. At a lonely class instant, every reading at residue 7 has `ε ≤ 0` (clear at the entering edge). This is a
  check, not a finding.
- M4-4. The kinds of failure are exhaustive by residue: residue 0 (captured; in the way unless `|ε| ≥ 1` or it wraps);
  residue 7 with `ε > 0` (past the entering edge: the pair law's case); residue 1 with `ε < 0` (a doubled leaving edge);
  an interior residue `r` with `r + ε ∉ [1, 7]`.
- M4-5. The grid pair law (`grid_pair_law`, proved). When class `c` fails only through its entering-edge reading `b`
  (`ε_b > 0`), the pair `(a, b)` sits in the right order for the mirror class `8 − c` with `b` on the leaving edge. The
  mirror is lonely iff the other readings are clear there. That last condition is content, not forced.
- M4-6. **The restatement hazard.** Every opening `(8K+1)/(8h)` is the class-1 instant of the grid through `h` with
  `mm = 8K + 1`. With `mm` unrestricted, "some lonely class instant exists" is loneliness renamed (map C4). So the run's
  content is which grid and class hold the isolation, and how they move with the speeds. `M = ⌈mm·m/e⌉` (the grid's
  coarseness against the slowest reading) is recorded as a coordinate and never required. The computational range is
  `M ≤ 4`, a range of search, not a statement. Every set with no lonely class instant in the range is listed.

**Parts:**
- **A. Placement**, per set:
  - the lonely class instants in the range, and their coarsest `M`;
  - at each, the edge pair and every interior reading's `ε` against its residue's band `[1 − r, 7 − r]`;
  - at each non-lonely class instant, the failing readings by kind (M4-4);
  - for each class that fails only on its entering edge, whether the mirror is lonely (M4-5); if it is not, the kind
    that fails it;
  - the cascade's landing (setter `h`, lap `K`), and whether it is one of the set's lonely class instants.

  Populations, chosen by construction and ranked by nothing: every 7-set of readings ≤ 16 (11,440); 2,000 seeded
  uniform 7-sets of readings ≤ 200; 1,000 seeded fine shapes at scale 1,000 with spread uniform in `[2, 20]`.
- **B. Relocation** (the owner's tool; *"each isolation is pushed there by the speed"*). Take 30 seeded fine shapes
  (scale 1,000, spread uniform in `[2, 20]`). Move each reading in turn by `−150` to `+150` in steps of 5, readings
  keeping their names. At each step record the lonely class instants and the landing. At each change, record:
  - for an instant that ends, the reading and the kind that end it;
  - for one that begins, its relation to the ended ones: the same grid's mirror (the pair law), the same grid's other
    class, or another grid;
  - where the landing is.

**Checks** (the only pass conditions):
- C1 (oracle): the landing equals the least clear point from `clear_set`.
- M4-2's residue map at every mirror evaluated.
- M4-3 at every lonely class instant.
- The integer clearance test (`c·n_a·d mod 8d_a ∈ [d_a, 7d_a]`) against the `Fraction` position at every lonely instant.

**Checklist.** The objects are the arrangement's own grids, classes (units mod 8), residues, deviations and openings
(candidate scales), and the cascade's landing. Every statement is pointwise at a named instant, with no union of windows.
There is no window and no lap restriction. `M` is a coordinate. The populations are exhaustive or seeded uniform, and
nothing is ranked by nearness to anything. Counts are records, with the exceptions listed.

---

## E217 — 2026-10-01 — the re-aimed run: the grid-class instant is an opening; the pair law's mirror does not carry the isolation in general; the landing's opening persists under speed change

**Map:** v2 §2A row 1, candidate scales (Theorem 6.15); continues E214 (iii); M2 (d), as designed in E216 with the
corrections below. Nearest §6 classes: F5 (one output was forced, and is marked) and F14 (Part B's first form tracked
every lonely opening; Part B′ reads the landing only).

**Corrections to E216's design, found by its own checks and derivation before any result was read:**
- **M4-3 was false as stated.** A reading on residue 7 can be clear with `ε ≥ 2` (past the next lap's leaving edge; for
  example at the progression, grid through 1 with divisor 3, class 3, the reading 2 sits at `18 ≡ 2`). The check fired
  21 times on the progression. It is dropped, and failures are named by the side of the slot the reading is actually on.
- **The family is the readings' openings** `[derived]`. After the pair law's rescaling (`a` on its grid point), the class
  instant depends only on `(a, n_a, c)`: the grid through the leaving-edge reading `a` itself. So the family is every
  opening `(8K+1)/(8a)`, read as class `c` of the grid through `a` with `n_a = (8K+1)/c`. E216's reading `e` adds
  nothing at the instant. Every such instant is a candidate scale `a/(8K+1)`, Theorem 6.15's object.
- **`M` is time** `[derived]`. `t = c·n_a/(8a)` with `n_a·m ≤ M·a` gives `R = 8mt ≤ c·M`. The search range `M ≤ 4` is the
  window `R ≤ 28`, and the "coarsest `M`" E216 planned to record would have been close to "earliest instant". It was
  dropped. This confirms E215 point 4 by derivation: a uniform step bound is a cap on time.
- **"The landing is a lonely class instant" is forced** (F5) whenever the landing lies in the window, because the landing
  is a lonely opening. It held in every set and at every step, and is not a finding.

**Checks** `[VERIFIED — every run]`: C1 (the cascade's landing equals the least clear point from `clear_set`), 0 failures
in every population and at every sweep step. M4-2 (the mirror's residue map), the construction check, and the integer
test against `Fraction` positions: 0 failures (`LonelyRunner/experiments/nN/redo/class_instant_run_v1.out`,
`class_instant_run_v2.out`).

**A. Placement** (every 7-set of readings ≤ 16, 11,440; 2,000 uniform 7-sets of readings ≤ 200; 1,000 fine shapes of
spread uniform in `[2, 20]`):
- Every set has a lonely opening inside the search window. That is the range check (no misses), not a finding.
- **The pair law's mirror, beyond its hypothesis** `[VERIFIED — these populations; a scoped null]`. When an opening fails
  only on its entering edge, the mirror (class `8 − c`, the entering reading on the leaving edge) is lonely in 15,003
  of 73,613, 7,459 of 32,736 and 1,831 of 8,547. The rest fail by all four kinds, most often an interior reading beyond
  its band. So the mirror that held E214's tight set is not, in general, where the isolation goes once the other
  readings' deviations are unrestricted.
- **The pair law's small-deviation hypothesis** (`|ε| ≤ 1` for interior readings) does not describe most lonely openings.
  An interior reading deviates by more than 1 at 87,347 of 159,506, 39,556 of 61,264 and 9,899 of 15,458 of them, and
  is still clear inside its residue's band `[1 − r, 7 − r]`.
- Failing readings at non-lonely openings fall in all four kinds in every population. Recorded, not ranked.

**B. Relocation.** Thirty seeded fine shapes; each reading moved by `−150` to `+150` in steps of 5 (up to 15%):
- Part B's first form (every lonely opening in the window: 1,953 begun, 1,965 ended) tracked a family broader than the
  cascade uses. It is recorded in `_v1.out` and not read as mechanism.
- **B′, the cascade's own landing** (`_v2.out`): across 10,954 steps the landing's opening (setter and lap) changed 16
  times.
  - In 10, an earlier opening became lonely while the old one stayed lonely. That is the landing being the least lonely
    instant, a by-product (E109 O1), not a relocation.
  - In 6, the old landing's isolation was destroyed. Each time **exactly one reading was in the way there, on its
    entering side**. In 3 of the 6 the landing moved to that reading's own exit; in 3 to another reading's.
  - `[VERIFIED — these sweeps; small counts, recorded, not a law]`.

**Consequence:**
- **The grid view of the owed statement is candidate scales plus a cap** `[derived]`. The pair law's class instant is an
  opening of the leaving-edge reading. `GridClass8`'s Helly instant is also an opening (of the reading with the largest
  left end). So every `GridStep8` certificate names a clear candidate scale (Theorem 6.15's object), with its lap
  structure read from a grid. The step bound `M` bounds its time. `WideStep8 M` is Theorem 6.15 on wide sets, plus a
  lap structure, plus a cap. This answers the E215 decision point on how the owed statement should read: the native
  content is the lap structure, and the cap is not native.
- **E214's (iii) is scoped to the tight set** `[VERIFIED — these populations]`. The mirror carried the isolation there
  (both junctions tight at one ratio), and does in about one case in five here. It is not the general relocation.
- **A lead for the next step** `[VERIFIED — these sweeps; reasoned as a reading]`. The landing's opening persists across
  wide speed changes and ends only when one reading enters its slot there. The region of speeds where one opening, with
  one lap for every reading, stays lonely is a set of linear inequalities in the speeds. The band theorem's 105 cones
  (E124) are exactly such regions. So the relocation map is the cone structure: which lap assignment holds where in
  the shape space, and what the cascade does on crossing a wall (one reading entering). This is the owner's *"every
  arrangement is AP/grid plus deviation … the cascade maps where the displacement is relocated"*, with the walls named
  by the reading that enters. Not yet designed.
- **Standing questions:** E215's question on how the owed statement should read is answered in part (above). The cap
  remains a decision for the owner.

**Precision note on E217's lead.** "The band theorem's 105 cones are exactly such regions" overstates. A cone (E124,
`cone_band`) fixes a lap for every reading and requires the lap blocks to meet pairwise. Inside one cone the lonely
instant is the largest left end, which can be a different reading's opening in different parts of the cone. An
opening's persistence region fixes the opening as well. So the two are regions of the same kind (a fixed lap
assignment, linear inequalities in the speeds), and a cone is a union of persistence regions. Also, "about one case in
five" in E217's Consequence is a description of the counts beside it (15,003 of 73,613, and so on), not a rate offered
as a result.

**Corrections found by the memory review (2026-10-01).** The `memory-drafter` agent's pass over E207–E217, checked here
against the files:
- **F7 in E217.** "`M` is time `[derived]`" re-derives E170 (log line 5469): *NB(M − ½) ⇒ `Cover8 M` ⇒
  NB(8⌊7M/8⌋ + 7)*, where NB(X) means every set of at most seven readings is lonely at some `t` with `8·d_min·t ≤ X`.
  E215 item 4 and E217 should have cited it. Reproduced: both `DoorFirstLap` refutations are band sets (spreads 7.469
  and 7.467) needing `M = 2`, first lonely at `R = 2401/234` and `165/16`, above 7.
- **A proxy in E215 item 2.** "The words appear 6, 9 and 10 times in E212, E213 and E214" counts the substring `cover`.
  All six hits in E212 are the names `Cover8` and `wideStep8_of_cover8`, or gate prose. The count is not evidence of the
  item-4 object. The object-level evidence is E213 M4-2 and E214 Part C's instruments (union of windows over a stretch
  of instants), which E215 also cites. The count is withdrawn as evidence; the finding stands on those instruments.
- Recorded in memory: `feedback_n8_cascade_is_the_oracle_2026_09_27.md`, section "Recurrence 2026-10-01", with an
  interval check (delete the interval clause and see whether a place remains; rewrite in `u = d_min·t` and compare with
  register rows; find the time bound an owed Prop implies) and over-application guards. Pointers were updated in
  `MEMORY.md`, `lrc_INDEX.md`, `feedback_INDEX.md` and `feedback_n8_map_first_2026_09_30.md`.

**Precision note on E217's mirror counts.** "When an opening fails only on its entering edge, the mirror … is lonely in
15,003 of 73,613" mixes denominators. 73,613 counts mirror evaluations, one for each entering-edge reading in the way;
the openings that fail only on their entering edge number 70,403 (`class_instant_run_v1.py`, Part A; `.out` line 22):

| population | mirror lonely | mirror evaluations | openings |
|---|---|---|---|
| every 7-set of readings ≤ 16 | 15,003 | 73,613 | 70,403 |
| 2,000 uniform 7-sets of readings ≤ 200 | 7,459 | 32,736 | 28,198 |
| 1,000 fine shapes | 1,831 | 8,547 | 7,312 |

The finding is unchanged: beyond the pair law's hypothesis, the mirror is not in general where the isolation goes.
Found by the `memory-drafter` agent's review. The memory states the denominator correctly.

---

## E218 — 2026-10-01 — design: the persistence-region run (the landing's certificate, its box of arrangements, and where the cascade moves the isolation across each face)

**Owner:** *"yes, design the persistence-region run first, then run it"*.

**Map:** v2 §1 (certificate `(e, k)`, opening, the cascade, landing) and E217's lead (owed to v3). M2 class (d), a map
run. Nearest §6 classes, and why this step is none of them:
- F4 (a restatement taken for a step): the run does not assert that the boxes fill the arrangement space, which would be
  the obligation (Theorem 6.15) restated. It records how the cascade moves between boxes.
- F14 (an instant family the cascade does not use): every instant is the cascade's own landing or its next move.
- F3 (a majority rule stated as a law): the classes are records, with the exceptions listed.

**Interval check** (the oracle memory, 2026-10-01):
- Step 1: the only intervals here are intervals of **speeds** (a box of arrangements), never of instants. Deleting them
  leaves the certificate's instant, which is the place.
- Step 2: no window in `u = d_min·t`; the lap `K` is unrestricted.
- Step 3: no owed statement and no `M`.
- The union here is of regions of arrangements, each with a named instant: the owner's case-list form (MANUSCRIPT_v20
  §0), not register item 4's union of windows over instants.

**Object.** The cascade's landing at an arrangement is a certificate: the setter `h` on its leaving edge at lap `K`,
`t = (8K+1)/(8h)` (a candidate scale), and for every other reading `d` the clear block `[8k_d+1, 8k_d+7]` holding its
position `p_d = (8K+1)·d/h`. The **persistence region** of the certificate `(h, K, k)` is the set of arrangements lonely
at `h`'s opening at lap `K` with every reading in the same block.

**Forced before running (M4):**
- M4-1. With `h` fixed, the region is a **box**: each `d` separately in `[(8k_d+1)·h/(8K+1), (8k_d+7)·h/(8K+1)]`; in speed
  space it is a cone over that box (scale invariance). Every arrangement in it is lonely at that one instant.
- M4-2. This is the grid view (E217). On the grid through `h` of step `h/(8K+1)`, each reading lies in its block of grid
  positions. A face is one reading at its leaving edge (`p_d = 8k_d+1`) or entering edge (`p_d = 8k_d+7`). Per reading,
  the slacks `p_d − (8k_d+1)` and `(8k_d+7) − p_d` sum to 6. The setter's leaving slack is 0 by definition.
- M4-3. Moving `d` alone slower past its leaving face puts it in the way at `t`, on the leaving side; it exits just
  after. So the landing hands off to `d`'s opening at lap `k_d` unless another reading's slack is used up there, or `d`'s
  change of speed has cleared an earlier instant. Those are the exceptions to record.
- M4-4. Moving `d` alone faster past its entering face puts it in the way at `t`, on the entering side. If the run to
  `t` is unchanged, the cascade's next move goes to `d`'s next opening `(8k_d+9)/(8d)`. Whether that is lonely is
  content, not forced.

**Parts:**
- **A. The landing's box.** Every 7-set of readings ≤ 16 (11,440), and 1,000 seeded fine shapes (least reading 1,000,
  spread uniform in `[2, 20]`). Record the certificate and each reading's two slacks, and which readings are tight
  (slack 0) besides the setter. Derivation check: 20 arrangements sampled inside each box are all lonely at the
  certificate's instant. For those, record whether the cascade lands at the same certificate or at an earlier one (the
  by-product).
- **B. Across each face** (the owner's tool, one runner at a time). Take 300 seeded fine shapes and 300 sets drawn
  uniformly from the ≤ 16 family. For each reading `d ≠ h`, move it alone to just past each face: the arrangement is
  scaled by `1000·(8K+1)` so that the face is a whole number, and `d` is one unit beyond it. Run the exact cascade and
  classify the new landing.
  - Leaving face: a hand-off to `d` at lap `k_d`; an earlier instant; or other.
  - Entering face: `d`'s next opening; an earlier instant; or a later opening of another reading, with the extra moves
    and which reading.
  - At each entering crossing whose next opening of `d` is not lonely, record the readings in the way there and on
    which side.

**Checks** (the only pass conditions):
- C1 (oracle): the landing equals the least clear point from `clear_set`, at every arrangement run.
- The box check (M4-1), at every sampled arrangement.
- The construction check: the moved reading is in the way at `t`, on the intended side.

**Checklist.** The objects are the cascade's certificate, its instant (a candidate scale) and the arrangement space's
boxes, each with a named instant. Populations are exhaustive or seeded uniform, ranked by nothing. There is no window,
no cap and no covering of instants. Counts are records, and every exception class is listed.

---

## E219 — 2026-10-01 — the persistence-region run: leaving faces are hand-offs; the isolation is displaced only when a reading enters; the boxes are E124's cells, and their exhaustion is E125's open question again

**Map:** v2 §1 (certificate, landing); E217's lead; M2 (d), as designed in E218. Nearest §6 classes: F5 (M4-3 and
M4-4 checked, not found) and F7/F11 (this run re-arrives at E125's question; see Consequence).

**Checks** `[VERIFIED — every run]` (`LonelyRunner/experiments/nN/redo/persistence_run_v1.out`):
- C1 (the cascade's landing equals the least clear point from `clear_set`): 0 failures at every set, every sampled
  arrangement and every moved arrangement.
- The box check (M4-1): every one of the roughly 124,000 arrangements sampled inside a landing's box is lonely at that
  certificate's instant.
- The construction check (the moved reading is in the way at `t` on the intended side): 0 failures.

**A. The landing's box** (every 7-set of readings ≤ 16, 11,440; 1,000 fine shapes):
- **Tight readings.** Besides the setter, a reading sits exactly on a face in 2,121 of the 11,440 whole-number sets
  (entering side 2,223 times, leaving side 792) and in none of the 1,000 fine shapes. Tightness is a whole-number
  coincidence.
- **The boxes overlap.** Arrangements sampled inside the landing's box land at the same certificate 71,543 times, at an
  earlier one 42,775 times, and later 5 times (the sample changed the slowest reading, and with it the bound).
  "Earlier" is the landing being the least lonely instant, a by-product: another certificate's box overlaps. So the
  landing's region is the box less the boxes of earlier certificates.
- **The setter** is the slowest reading in 6,072 of 11,440 sets (bound landings included) and in 457 of 1,000 fine
  shapes. Recorded.

**B. Across each face, one reading at a time** (300 whole-number sets, 300 fine shapes; every reading other than the
setter, both faces):
- **Leaving face** (the reading slowed past its leaving edge). The landing hands off to that reading's opening at its
  lap in 1,694 of 1,800 fine-shape crossings; the other 106 go to an earlier instant. In the whole-number sets:
  - hand-off in 1,404 of 1,800;
  - earlier instant in 153;
  - other in 243, where a tight reading or a change of order (the moved reading passing the setter) intervenes.

  This is M4-3 `[derived + VERIFIED]`: a continuous hand-off, not a relocation.
- **Entering face** (the reading made faster past its entering edge). The cascade's next move goes to that reading's
  next exit (M4-4, forced). Whether that exit is lonely is the content. In fine shapes:
  - lonely there in 746 of 1,800;
  - an earlier instant in 281 (the faster reading's windows cleared one);
  - a later opening in 773: of another reading 678, of the old setter 67, of the same reading at a later lap 28.

  Where the entering reading's exit is not lonely, one to three other readings are in the way there (most often one,
  on its entering side). The whole-number sets show the same pattern.

**Consequence:**
- **The isolation is displaced only by a reading entering its slot at the isolation instant** `[derived (M4-3) +
  VERIFIED (B)]`. Slowing a reading past its leaving edge is a continuous hand-off to that reading's own opening. This
  sharpens E217 B′ (6 of 6 destroyed by an entering reading) into a derivation plus a check on every face. In the owner's
  words, *"each isolation is pushed there by the speed"*: the push is always a reading entering.
- **The persistence regions are E124's cells** `[reasoned]`. A box is a lap assignment with a named setter; E124's cones
  are lap-assignment cells, and each is a union of these boxes (E217 precision note). Across an entering face the
  relocation follows the cascade's own move rule, from the entering reading's exit onward (M4-4). **So "why the boxes
  exhaust the arrangement space" is E125's open question** (*"why the categories exhaust"*). And "why every relay
  started at an entering face ends in a box" is the cascade's arrival, which is the obligation (`doors_agree`; §5,
  F4). This run adds a fact about the faces. It does not add a mechanism for the exhaustion, and it re-arrives at the
  statement E206 had already found reached "from four sides".
- **Direction** `[reasoned]`: continuing runs of this kind will keep re-arriving at E125, because the objects (a lap
  assignment and its faces) are the same. Map v3 is owed and overdue (E192–E219). It now carries three results that
  bear on where the next step starts:
  - E215's failure record;
  - E217's result that the owed statement is candidate scales plus a cap;
  - this entry's re-arrival at E125.

  The map-first memory says to cut a version before the next step when a consequence duplicates a route, and this one
  does.
- **Standing questions:** none answered. The cap in `WideStep8` is still the owner's decision.

---

## E220 — 2026-10-01 — map v3 cut and checked; the complete account of the cascade designed for approval

**Map:** none — housekeeping (a map cut and its `compile-diff`) and a design written for the owner's approval; nothing
run.

**Owner:** *"Yes I was just thinking the same thing.  We keep proposing mechanisims, testing them and finding exceptions.
We should really know and understand what the cascade does in all configurations, not be testing to find out something
different happens.  I think this is the next major piece of work.  There should be no gaps in what we understand should
happen"*.

**Map v3** (`docs/n8/MECHANISM_MAP_v3.md`; v2 and v1 retained). Scope: log E100–E219 and v21 §15–§17E. It adds:
- §0: the owner's rulings of E196–E215 and of today; **M8** (derive first; a run checks a derivation); the interval
  check; session findings kept apart from owner rulings.
- §1: the objects of E201–E218.
- §2 F–H: the band and the band route; the derived facts of the cascade's run, each with its check named; our order-seven
  proof read for order eight.
- §3 R10–R14.
- §4: Q7 withdrawn; the central statement ("why the carrying-in stops inside the block") reached from six sides; **Q8,
  the complete account**.
- §6: F14, F15 and F16, and new instances of F1, F3, F5 and F7.
- §7: the next step is Q8.
- §8: owed items.
- §9: C9–C15.
- §10: an index of the run artifacts.

**`compile-diff`** (mandatory before promotion; condensed report and its verification in
`docs/n8/MECHANISM_MAP_v3_COMPILE_DIFF_v1.md`):
- The first draft lost 22 items and widened 11 grades or scopes. The largest: the pointer to v1's part (C); open items
  of E190–E219 (strips 9–12, the `WideStep8 1` checks, first-lap clearance, the (2,5)–(4,3) shapes); R11 graded
  "Answered" without M3 on the 128 orbits; the leaving-face hand-off stated without its conditions; the boxes stated
  equal to E124's cells.
- The first repair was verified by the same agent: 21 of 22 losses repaired, all retractions carried. It found nine new
  problems in the repairs and six conflicts in the design. The worst: a leaving-face exception ("the order of the
  readings changes") taken from E219's data and cited as E218 M4-3's derivation, the re-scoping M8 forbids. It is now
  recorded as an **incomplete derivation**: M4-3 assumed the moved reading keeps its place, and E219's 243 "other"
  crossings are that assumption failing. That is gap C2a.
- The second repair was checked mechanically (the corrected phrases absent, the new ones present). C1's `[PROVED]`
  covering E190's `[reasoned]` clause is left as is (low).

**The design** (`docs/n8/CASCADE_DESIGN_v3.md` §8; §1–§7 are v2's, unchanged). It is for the owner's approval before any
work.
- §8.0 states plainly that an account with no gaps anywhere is the proof itself (`doors_agree`). So the design closes
  every other gap by derivation, and isolates the obligation as a statement about where the readings sit at the last
  separation.
- The discipline (M8).
- Level A, the step (complete by derivation).
- Level B, patterns of moves (passages, bridges, junctions derived; the conveyor as data).
- Level C, the run as a function of the arrangement: walls `(8K+1)·d = (8k ± 1)·h`, and the local rule at each kind of
  wall.
- Level D, placement by grid plus deviation and the split: D1 (one cluster) derived; gaps D2 (the fast part's chain ends
  in a block of the slow part), D3 (the band's copy 0 and copy 1), D4 (the nest), D5 (the recursion's exceptions).
- A gap register, and an order of work: A, then B and C, then D3 first, because a derivation there can be checked
  against `band_lonely`.
- Three questions to the owner.

**Consequence:** none for the proof. Map v3 is the start point for the next step (map-first); Q8 waits on the owner's
approval of the design.

---

## E221 — 2026-10-01 — the complete account, Level A: the step, catalogued and checked

**Owner:** *"yes approved, start with the Level A catalogue"* (approving `CASCADE_DESIGN_v3` §8).

**Map:** v3 §4 Q8 and §7; `CASCADE_DESIGN_v3` §8.2. The items are derivations uniform over every arrangement (class (c)
in form). They are the definition unfolded and not progress on the obligation (map §5), and every one is forced: the run
is a check, by design. Nearest §6 classes: F5 (forced facts are stated as such and checked, not reported as findings) and
F4 (Level A is not presented as a step on the obligation).

**The catalogue** (`docs/n8/CASCADE_ACCOUNT_LEVEL_A_v1.md`), A.0–A.12:
- A.0: units and the definition: positions `8dt`, slots `(8k−1, 8k+1)`, blocks `[8k+1, 8k+7]`, BSM's strict
  inequality.
- A.1: the move advances, and no lonely instant lies inside it `[PROVED]`.
- A.2: every cascade instant after the bound is an opening `(8K+1)/(8h)` of its setter, a candidate scale `[PROVED]`.
- A.3: the setter is the crowd member with the largest remaining distance to its leaving edge relative to its speed,
  and the move's length is that time `[derived]`.
- A.4: the step is a rotation of every position by its own speed, read at the setter's exit `[derived]`.
- A.5: the next crowd is exactly the arrivals and the re-entries; a re-entry needs `D > (7 − x_c)/(8c)` `[derived]`.
  The general form; `SeparationN.transport` is its centred special case `[PROVED]`.
- A.6: the three move types `[PROVED — SweepBridgeN]`.
- A.7: the setter is never in the way at its own exit `[PROVED]`.
- A.8: the landing's certificate `[PROVED]`; the setter is the slowest of its lap-`K` cluster `[derived]`.
- A.9: first isolation, a by-product, not used.
- A.10: the bound's captures, grid slots 7 and 0 of the slowest reading's grid `[derived]`.
- A.11: the edge cases.
- A.12: what Level A does not say.

**The check** (`LonelyRunner/experiments/nN/redo/cascade_level_a_check_v1.{py,out}`; exact; the clear set computed
without the cascade) `[VERIFIED — these populations]`:
- every 7-set of readings ≤ 20 (77,520 sets, 60,742 moves);
- 1,000 seeded fine shapes (1,064 moves);
- the 5,400 late band shapes (106,735 moves).

**0 failures on every item** (A.1, A.2, A.3, A.4–A.5, A.6, A.7, A.8, A.10) in all three populations. Edge cases, counted
as derived (A.11):
- a reading exactly on an edge: 1,729 times in the whole-number sets, none in the fine shapes;
- tied setters: 23 and 1;
- re-entries within one move: 10 (sets ≤ 20) and 162 (late shapes), each satisfying A.5's condition.

**Consequence:**
- **Level A is complete** `[derived + PROVED; checked]`. One move of the cascade, in every configuration, is the rotation
  of A.4 read at the setter's exit. Everything after it (who is in the way next, the move type, where the chain can land)
  is A.5–A.8. So every question about a chain is a question about the sequence of these rotations, which is Level B's
  object.
- **What Level B starts from:**
  - A.3 gives the setter as a maximum of `(1 − x_c)/c`;
  - A.5 gives the next crowd as the arrivals (readings within `8rD` of an entering edge) and the re-entries (fast
    readings);
  - A.6 gives the lap order.

  Gap B4 (when the next setter is the queue front) is a question about the order of arrivals' exits, from A.3 applied to
  the next crowd.
- **Re-entries are real but rare** (162 in 106,735 moves of the late shapes). They are fast readings lapping within one
  move. They bear on E204's conveyor "carried by the fast readings".
- **Lean, optional** `[reasoned]`: A.3, A.5 (the general transport), A.8's cluster clause and A.10 are on paper and
  small. They would sit beside `SeparationN` and `SweepBridgeN`. The owner's call; not needed before Level B.
- **Standing questions:** none answered.

---

## E222 — 2026-10-01 — the complete account, Level B: patterns of moves, catalogued and checked; no Lean until the map is complete

**Owner:** *"Yes we are not looking at lean until the map is complete"* (approving Level B next, and declining the
optional Lean offered in E221). This supersedes `CASCADE_DESIGN_v3` §8.7's clause *"Lean follows each derived item as it
is completed"* and E221's Lean consequence; carried to the next versions of the design and the map. The catalogues cite
existing Lean declarations as anchors (reading, not building). Recorded in memory by the `memory-drafter` agent.

**Map:** v3 §4 Q8; `CASCADE_DESIGN_v3` §8.3. Derivations uniform over every arrangement, all forced by Level A, checked by
design (M8). Nearest §6 classes: F5 (stated as forced) and F3 (the records below are data, not laws).

**The catalogue** (`docs/n8/CASCADE_ACCOUNT_LEVEL_B_v1.md`), B.1–B.11, all `[derived]` from Level A:
- B.1: the setter is the latest exit `(8l+1)/(8s)` over the crowd.
- B.2: the junction: at the setter `a`'s exit on lap `k`, reading `b` is in slot `l` iff
  `s_a(8l−1) < s_b(8k+1) < s_a(8l+1)`. Every reading's place at an exit is decided by its ratio to the setter.
- B.3: the slower readings in the setter's slot form an unbroken run, every reading within ratio `ρ_k` below it.
- B.4: a sweep step jumps to the bottom of that run, not to the next slower reading.
- B.5: passages descend through consecutive ratios below `ρ_k` to the lap-`k` cluster's bottom, or end at a bridge.
- B.6: bridges, up or down: the latest exit is on another lap.
- B.7: the queue.
- B.8: **gap B4 closed**: the next setter is the queue front iff the front is in the next crowd and no member exits later.
  An arrival outlasts the front iff its entry lag exceeds the difference of their stays: any slower arrival outlasts it;
  a faster one only by entering late enough. This holds unless the front itself lapped.
- B.9: the chain ends iff nobody is in a slot at the exit: a gap in the arrivals, or the front passing through.
- B.10: the first move.
- B.11: what Level B does not say.

**Two corrections to B.8, both before commit:**
- (1) The first draft said an arrival can outlast the front "only by being slower". That is false for a faster arrival
  entering late. It was found while the check was being designed, before it ran, and corrected.
- (2) The check found 35 moves (late shapes) where the front had itself lapped, so an arrival entered before it. The
  statement now carries that exception. The classification by exits holds there.

**The check** (`LonelyRunner/experiments/nN/redo/cascade_level_b_check_v1.{py,out}`; exact) `[VERIFIED — these
populations]`: every 7-set of readings ≤ 20, 1,000 seeded fine shapes, the 5,400 late band shapes. **0 failures on every
item** (B1, B2, B3, B4, B5–B6, B8's condition and its slower-arrival clause, B9, B10). Records, which are data and not
laws:
- conveyor breaks by kind (the front not in the next crowd; a slower arrival; a faster arrival entering late), in all
  three populations. The last kind (512, 7, 1,190) is the case the first draft of B.8 excluded;
- landings after at least one move, by a gap in the arrivals or by the front passing through: 27,213 and 1,102 (sets
  ≤ 20), 515 and 30 (fine), 2,927 and 2,473 (late shapes).

**Consequence:**
- **Level B is complete** `[derived; checked]`. A chain is passages (each sweep jumps to the bottom of the run within
  `ρ_k` below the setter) joined by bridges (a latest exit on another lap). Its hand-overs follow the conveyor exactly
  when B.8's condition holds. It ends when nobody is in a slot at an exit. Gap B4 is closed.
- **What Level C starts from:** by B.2, every reading's place at every exit is a ratio inequality against the current
  setter. So the whole chain, as a function of the speeds, is fixed by finitely many inequalities of the form
  `s_a(8l ± 1)` against `s_b(8k + 1)`, as long as the chain is finite. These are Level C's walls (design §8.4 C1), now
  derived from B.2 rather than assumed.
- **E204's "gap in the arrivals" is half the story in the late shapes:** 2,473 of their landings come from the front
  passing through within the last move, against 2,927 with no arrival. Both are B.9.
- **Standing questions:** none answered. The owner's Lean ruling is recorded above.

---

## E223 — 2026-10-01 — the complete account, Level C: the run as a function of the arrangement, catalogued and checked

**Owner:** *"Yes on to the next, if it not large then continue on to other too"*.

**Map:** v3 §4 Q8; `CASCADE_DESIGN_v3` §8.4. Derived items, checked (M8). Nearest §6 classes: F5 (stated as forced) and
F3 (records, not laws). No Lean (E222).

**Memory housekeeping.** The `memory-drafter` agent of E222 stopped on a usage limit at its last step (a link check). Its
writes are complete and were verified here:
- `project_n8_lean_on_hold_until_map_complete_2026_10_01.md`, every `[[link]]` resolving and every file it cites present;
- the pointer in `lrc_INDEX.md`;
- one sentence in `MEMORY.md`'s n=8 line.

**The catalogue** (`docs/n8/CASCADE_ACCOUNT_LEVEL_C_v1.md`):
- C.1: a finite chain is decided by the signs of finitely many forms, linear and homogeneous in the speeds, and **all of
  them are edge forms** `b(8k + 1) − a(8j ± 1)`. Off every wall, nearby arrangements have the same chain.
- C.2: the walls.
- C.3: a tie wall is an edge wall on the leaving side. At an intermediate move, crossing it is a relabelling; at the
  final move it is the landing's leaving face, a hand-off.
- C.4: **crossing a wall at an intermediate move changes the route, never the landing**, unless the wall is also a face
  of the landing's box or of an earlier certificate's box. **Gap C2 closed**: the routes rejoin at the latest at the
  landing.
- C.5: at an infinitesimal crossing of the landing's faces, the leaving face is a hand-off and the entering face's next
  move is the entering reading's next exit. Neither makes an earlier landing, unless the face coincides with an earlier
  box's face. **Gap C2a resolved:** E219's exceptions came from moving the reading a finite distance, across other walls.
- C.6: the landing's region is its box less earlier boxes; its boundary is made of faces.
- C.7: what Level C does not say.
- **Flag for the owner:** C.4 and C.5 use `move_le_of_lonely` (the chain never passes a lonely instant), and with it
  first isolation, to describe what the oracle does at a wall. Not as an argument for the conjecture (E200).

**Repairs found by the check** (M8: each exception read, the derivation repaired, with a derived reason):
- C.3's first draft said a tie never changes the landing. 54 crossings (8, 41, 5) did. All were at the final move, all
  continuous hand-offs: a tie is an edge on the leaving side. C.1 and C.3 were repaired.
- C.5's first draft did not state that the crossed face must not also be an earlier box's face. 4 crossings were of that
  kind, read in full on `(1, 3, 4, 5, 6, 7, 8)`: reading 4 at `21/5` is on the landing's entering face and on its own
  leaving edge at the earlier instant `15/56`. The condition is now explicit.

**The check** (`LonelyRunner/experiments/nN/redo/cascade_level_c_check_v1.{py,out}`; exact rational speeds; crossings at
relative distance `10⁻⁹`) `[VERIFIED — these populations]`: 300 seeded fine shapes, 300 late band shapes, 300 sets from
readings ≤ 16. **0 failures after the repairs.**
- C.1: 2,301 perturbations inside the margins, every chain unchanged (133 whole-number sets on a wall, not perturbed).
- C.3: ties at intermediate moves unchanged; 54 final-move hand-offs, as derived.
- C.4: every changed landing is also a face of the landing's box (92, 4,029, 147); routes changed with the landing kept
  in 208, 4,079 and 305 crossings.
- C.5: leaving faces all hand-offs (317, 324, 225); entering faces all go next to the entering reading's exit (lonely
  there 278, 51, 233; the relay continues 262, 103, 173); 4 coincident faces.

**Consequence:**
- **Level C is complete** `[derived; checked]`. A chain's dependence on the speeds is a hyperplane arrangement of edge
  walls `b(8k + 1) = a(8j ± 1)`. Most walls change only the route. The landing changes only on its own box's faces
  (hand-off on leaving; one more move, to the entering reading's exit, on entering) and on earlier boxes' faces. With
  Level B: the isolation moves continuously except when a reading enters at it, and is then carried by the cascade's
  ordinary moves.
- **Levels A–C are the cascade's local and semi-local account without gaps.** What remains is Level D: which landing
  region contains a given arrangement, from the grid plus deviation and the split. Its gaps D2–D5 contain the obligation.
- **Standing questions:** the first-isolation flag above, for the owner.

---

## E224 — 2026-10-01 — Level D: the interval check on the approved design's D items, before any work; a re-aim proposed

**Map:** none — design check of `CASCADE_DESIGN_v3` §8.5 before starting Level D (the owner's *"continue on to other
too"*); nothing derived or run.

**The interval check** (memory `feedback_n8_cascade_is_the_oracle`, 2026-10-01) on §8.5 and §8.6:
- **D3**, second half: *"which band shapes reach copy 1"*. Copy 1 means the landing is not in `R ∈ [1, 7]`. A band
  shape reaches it iff it has no lonely instant there. Step 1 (delete the interval clause) leaves nothing. Step 2: it is
  `u ∈ [1/8, 7/8]`, register v3 item 15, and "is a clear set empty", item 8. The same drift as Q7 (E215), carried into
  the approved design by me. D3's first half, the chain pattern of E154 and its landing certificate in copy 1, names an
  instant and stands.
- **D2**: *"`F`'s chain … ends inside a clear block of `P`"*. At the landing every reading is clear, `P` included, so
  "inside a block of `P`" is forced (F5), and "the chain ends" is the obligation (F4). D2 has content only in what it
  names: the certificate, by `F`'s grid positions and deviations.
- D4 and D5 inherit D2's form.

**What Levels A–C now show about where Level D lives** `[derived, E222–E223]`: the landing moves continuously under any
change of speeds except when a reading enters its slot at the isolation instant (C.5). Then the cascade moves to that
reading's next exit. It lands there (746 of 1,800 in E219; 278, 51, 233 in E223's infinitesimal crossings), or the relay
continues by Level B's rules. So the open statement is localised to one event: **where the relay started by an entering
reading lands**, named by the readings. This is *"each isolation is pushed there by the speed"*: the entering reading
pushes it to its own exit, and from there the relay carries it.

**Proposed re-aim of Level D, for the owner** (not started):
- **D-object:** the landing certificate as a function of the arrangement (Level C's regions), reached from a reference
  where it is known (the bound when the spread is at most 7; the AP's class instants) by crossing faces. Each crossing
  is a derived local rule: hand-off on a leaving face, one move to the entering reading's exit on an entering face.
- **D-gap:** at an entering-face crossing, where the relay from the entering reading's exit lands, named by the grid
  positions and deviations at that exit. This is the single derivation target; D2–D5 become its instances (the band,
  the split, the nest, the recursion's exceptions).
- **Not the object:** which arrangements land in a given window (item 15), whether a window's clear set is empty
  (item 8), or that the relay ends (F1; the obligation).

**Consequence:** none for the proof. Level D waits on the owner's ruling on the re-aim.

---

## E225 — 2026-10-01 — owner: Level D re-aim approved; first isolation is established; a ruling asked for that was already on disk (F7)

**Owner:** *"1. Yes"* (E224's re-aim of Level D approved). *"2. First isolation isn't needed by the conjecture and I don't
think we have established if the cascade has or not... I seem to remember there are speed where lap occure.  Does that
mean that is the first isolation or just the first isolation that the cascade finds."* Then: *"So why did you ask rather
than read the results we have already documented.  Documentation is only good if you bother reading it"*.

**Map:** none — housekeeping (an owner question answered from the record, and a failure recorded).

**The answer, from the record** `[PROVED; VERIFIED]`: the cascade's landing is the first isolation, the earliest positive
lonely time, not only the first the cascade finds.
- `bound_le_of_lonely` (`Cascade/Iteration.lean:198`): nothing positive before the bound is lonely.
- `move_le_of_lonely` (line 107) and `iterate_le_of_lonely` (line 184): the cascade never passes a lonely instant.
- So `first_isolation_of_fixed` (line 213; manuscript v21 Theorem 6.2): the landing is at or before every positive
  lonely time. The file is in the gated `LRC/Cascade/` tree.
- Independently: `experiments/nN/cascade_first_check_v1.out` finds the landing equal to the earliest lonely instant in
  6,436 of 6,436 sets, and every C1 check of E171 and E212–E223 agreed.

The "laps" are:
- the first isolation itself lying beyond the slowest reading's first lap (the late shapes; `DoorFirstLap` refuted);
- bridges up to faster readings' later laps;
- fast readings lapping within one move (A.5 re-entries).

None skips a lonely instant. Per E200 nothing in the argument rests on it; using it to describe the oracle is sound
because it is proved.

**The failure (F7; O2 in memory `feedback_n8_no_prereg_no_imports`, "asked for a ruling already on disk").** E223's flag
asked the owner to rule on using first isolation, as if its standing were open. The facts were on disk in three places:
- Level A's own A.9, written the same day, cites `first_isolation_of_fixed` as `[PROVED]`;
- map v3 §2C;
- E200, which rules on the argument, not on the fact.

Step 0 of the pre-use check (grep the record first) was skipped. **Correction in practice:** before any question to the
owner, the log, the map, the catalogues and the Lean tree are searched for the answer; a question goes to the owner only
for what is not on disk (a decision, or something undefined). To be carried into map v4 §6 F7.

**Consequence:** C.4 and C.5 stand as written; their flag is withdrawn (the use is a description of a proved property of
the oracle). Level D proceeds on the approved re-aim (E224).

---

## E226 — 2026-10-01 — Levels A–C crosswalked to the record: mostly restatement of v21 §6 and E142–E183 (F7); Level D placed on the flank programme

**Map:** none — a citation pass after the owner's *"Documentation is only good if you bother reading it"* (E225); nothing
derived or run.

**Done:** v21 §6.1–§6.6 and §6.9–§6.15 read in full; the log's E142–E143, E178–E183, E202–E204 and E115 read; each Level
A–C item grepped against the log up to E220 and v21. Result in `docs/n8/CASCADE_ACCOUNT_CROSSWALK_v1.md`.

**Finding (F7, the third instance today after E217 and E225):**
- Most of Levels A–C restates in position language what v21 §6 already has, proved or verified: §6.1–§6.2 (the move,
  the scale recursion, a step is one dilation), Theorems 6.2–6.3, 6.12–6.17, 6.19, 6.23–6.24.
- The rest restates E142–E143 (move types, cluster bottom) and E178–E183 (the landing changes only at pinches; a death
  restarts the cascade past the entering reading's exit), with the path route's `margin_or_pinch` and `PinchOpenN`.
- What the greps do not find is B.4, B.8, C.3, the resolution of E219's exceptions as finite-travel effects, and the
  count of landings by pass-through. Those are the account's additions; nothing else in A–C is to be cited as new.
- The checks of E221–E223 stand as re-confirmations.

**Cause:** the design (E220) and each level were built from the definition and recent entries, not from the manuscript
of record. Map-first reads the map, but map v3 does not reproduce v21 §6, and v21 §6 was not opened. Step 0 of the
pre-use check (search our own record) was skipped at the design stage, so the derivations were sound and redundant.

**Level D, placed:** in the record's terms the re-aimed target (E224) is Theorem 6.15 locally, and the record's native
machinery for it is the flank framework (v21 §6.9–§6.11: Theorems 6.8, 6.9, 6.12–6.14, 6.18; Proposition 6.10; the U/K
calculus). Its open items as the record states them:
- the derivation at a general flank;
- the shadowing triples;
- "both on a common lattice, run-length failing";
- the index bound (measured, not proved).

Level D is designed from these after v21 §6.7 and §17 are read in full.

**Consequence:** the complete account is a consolidation with a citation layer (the crosswalk) plus five additions. The
next step reads v21 §6.7 and §17 and the latest handover before Level D's design, so that the design starts from the
record.

---

## E227 — 2026-10-01 — the record read for Level D (v21 §6.7, §17, handover v10, and the Lean tree first); design v4

**Owner:** *"Yes"* (to reading v21 §6.7, §17 and the latest handover in full, then designing Level D from the open
items). Then, while I worked: *"Remember that lean now outpaces the manuscript, handover and paper documents so"*.

**Map:** v3 §4 Q8; `CASCADE_DESIGN_v3` §8.5 re-aimed (E224, E225). A design from the record; nothing derived or run.

**Read in full:** v21 §6.7 (Existence; the rules-with-conditions form; the 2026-09-20 amendment: exhibit `(e, k)`, no
bound on `k`), §17 (the case list; `EightResidual`'s shapes; §17E's constraints on a proof's shape; §17G), handover v10
(§4's open step, the pair law as its first piece, owed: doubled edges and deviations beyond `1/C`, the twelve routes not to
re-derive). Then, on the owner's reminder, **the Lean `Spec/` tree surveyed module by module** (every module's stated
content, its commit date, and the untracked modules of other sessions), as the primary record of what is proved.

**What the survey changed** (my first v4 draft, written from the documents alone, would have re-proposed proved work):
- the exact band condition at a class instant ("D-a" in the draft) is `TwoBlockN.lonely_eight_of_blocks` and
  `lonely_eight_of_pairwise_laps`;
- doubled edges are in part `DoubledSlotN`, `DoubledNbhdN` and `GridClassN`;
- captured readings are in part `GridNudgeN` and `RungR1N`;
- neighbourhoods of every complete grid, the AP and the pair pattern are `GridNeighbourhoodN`, `APNeighbourhoodN` and
  `GridPairN`/`GridPairLawN`, each with a radius;
- local cascade transport is another session's untracked `CascadeTransportN` and `CascadeGridN`.

**Design v4** (`docs/n8/CASCADE_DESIGN_v4.md`; v3 retained):
- v3's §8.5–§8.9 are replaced and v3 §8.7's Lean clause is removed (E222).
- The base is the Lean rules, listed with their anchors.
- The targets are what Lean lacks:
  - **D1**: the selection, from the readings, of a reading, grid, class and laps that `lonely_eight_of_pairwise_laps`
    accepts, with no uniform cap. This is the obligation, and handover §4's open step in Lean's terms.
  - **D2**: where the isolation goes when it leaves a grid's neighbourhood (beyond the proved radii).
  - **D3**: captured readings beyond `GridNudgeN`'s single largest reading and `RungR1N`'s rungs; the pinned pair (both
    edges occupied) is the named failure of the nudge.
  - **D4**: transport, with the other session's modules once committed.
- Order: D3's pinned pair first, then D2, then D1.

**Consequence:**
- Lean is now the first source read for each target (E225–E227). The crosswalk of E226 covers v21 and the log; its next
  version owes the Lean modules too (for example the untracked `CascadeTransportN` against Levels A and B).
- Level D starts at D3, the pinned pair, after the owner's approval of v4.

---

## E228 — 2026-10-01 — design: D3, the pinned pair at the grid instant (captured readings with both edges occupied)

**Owner:** *"yes to v4"* (`CASCADE_DESIGN_v4`; its order starts with D3's pinned pair).

**Map:** v3 §4 Q8; design v4 §8.5 D3. M2 class (d), a map run whose pass conditions are derivation checks, preparing a
rule in v21 §6.7's form (a condition on the readings and a named instant). Nearest §6 classes:
- F14 (instants the cascade does not use): every instant here is a move of the cascade run from the grid instant;
- F7 (the record not read): the Lean tree and E27–E36 were read first and are listed below.

**Record first** (E225–E227 order: Lean, then log, then documents):
- `GridNudgeN`: at a grid instant `t₀` with every reading on an exact eighth, if exactly one reading is captured
  (residue 0) and it is the largest, the subject is lonely at `t₀ + 1/(8p)` if no reading sits at residue 7, or at
  `t₀ − 1/(8p)` if none sits at residue 1. They fail together exactly when both edges are occupied: **the pinned pair**.
  `nat_nudge_forward`: the whole-number form at `t₀ = 1/8`.
- `RungR1N.rung_r1_nat`: multiples of `q ≤ 8` captured at a rung `a/q`, R1 among themselves, the others with room.
- `GridPairN`, `GridPairLawN`, `TwoPinnerN`: nothing captured, one reading on each edge, so lonely at `t` or at the
  mirror.
- `DoubledSlotN`, `DoubledNbhdN`: the arrangement with one runner moved by whole laps into another's slot, which is one
  captured reading with both edges occupied, at named instants, under small deviation.
- Log E27–E28: a core "pinned on both sides" at its first isolation; its next cell starts at the reading on the entering
  edge's next opening `(8m+9)/(8b)` in 72 of 98, otherwise "the core's own cascade continued" `[EMPIRICAL]`. E29–E36:
  train and core.

**The object.** Whole-number readings at the subject's own grid instant `t₀ = 1/8`, where reading `d` sits at position
`d` (eighths). It has:
- a captured set `C` (multiples of 8, at least one);
- leaving-edge readings `E₁ ≡ 1`, at least one;
- entering-edge readings `E₇ ≡ 7`, at least one;
- interior readings `≡ 2 … 6`.

`GridNudgeN` does not apply (both edges occupied) and the pair law does not apply (something captured).

**Forced, from Levels A–C:**
- F-1. At `t₀` the crowd is `C`: readings on an edge are clear (BSM).
- F-2. The first move goes to the exit of the slowest captured reading `c*`, at `t₁ = 1/8 + 1/(8c*)`. Every captured
  reading sits at the centre of its slot and needs `1/(8c)`, so the slowest exits last (B.1).
- F-3. Every landing is an opening of its setter `h` (A.2). So the landing instant is `λ/8` with
  `λ = (8K + 1)/h`: a dilation of the grid instant by a ratio fixed by the integer `h` and its exit lap `K`. If `h`
  exits on its first lap after `t₀`, then `λ = (h + 9 − r)/h` for `h ≡ r ∈ {2, …, 7}`; `(h + 1)/h` for a captured `h`;
  and `(h + 8)/h` for `h ≡ 1`. Further laps add `8j`. **The relay from the grid instant is integer arithmetic in the
  readings.**
- F-4. E28's "the reading on the entering edge's next opening" is `h ∈ E₇` on its first lap, `λ = (h + 2)/h`.

**The run** (`LonelyRunner/experiments/nN/redo/d3_pinned_pair_v1.py`; exact). Take every 7-set of readings ≤ 24 with the
object's conditions, and a seeded uniform sample of such sets with readings ≤ 64. Run the cascade from `t₀ = 1/8` (A.1:
it lands at the first lonely instant at or after `t₀`, a lonely instant of the subject).
- Record the landing as `(h's residue r, extra laps j, λ)`: whose exit, as which grid role (captured, `E₇`, interior,
  `E₁`), and on which lap.
- Record the number of moves.

**Checks** (the only pass conditions):
- F-2: the first move is `c*`'s exit.
- F-3: the landing is `λ/8` with `λ = (8K+1)/h` exactly, and `h`'s first-lap formula holds when `j = 0`.
- C1: the landing equals the least clear point at or after `t₀`, computed without the cascade.

**What the run is for.** To read, in grid data, which role's exit holds the isolation. Then (the next entry) to derive the
exact arithmetic condition for each role that occurs, as a rule: the condition, the named instant `λ/8`, and the proof by
the band test (`lonely_eight_of_blocks`). Counts are records, never the answer. Every set where the landing is not a
first-lap exit (`j > 0`) is listed.

**Checklist:**
- The objects are the grid instant (the subject's own AP instant, v21 §6.6), the cascade's moves from it, and the setter
  roles by residue.
- No window of instants: the run starts at a named instant and records named instants.
- No cap: `K` and `j` are free and recorded.
- No ranking; populations exhaustive or seeded uniform.

---

## E229 — 2026-10-01 — D3 run: from the pinned grid instant every role's exit can hold the isolation; D3 is the record's "fourth rule" (the `L₀` ladder)

**Map:** v3 §4 Q8; design v4 D3; M2 (d), as designed in E228. Nearest §6 classes: F3 (the role counts are records, not a
rule) and F7 (the record's own statement of this object, `PROOF_REQUIREMENTS_v2` §7, read after the run; it should have
been read before it, and is now carried).

**Checks** `[VERIFIED — these populations]` (`LonelyRunner/experiments/nN/redo/d3_pinned_pair_v1.{py,out}`; exact): every
7-set of readings ≤ 24 with a captured reading and both edges occupied (86,301 sets), and 3,000 seeded such sets of
readings ≤ 64. **0 failures** on:
- F-2: the first move from `1/8` is the slowest captured reading's exit;
- F-3: every landing is `λ/8` with `λ = (8K+1)/h`, and the first-lap formula holds with `j ≥ 0` whole;
- C1: the oracle check.

**The map** (records, not a rule). Whose exit holds the isolation from the pinned grid instant (sets ≤ 24):
- the reading on the entering edge (`≡ 7`): 33,069, E28's pattern;
- interior readings: 40,019 (`r = 6`: 17,049; `5`: 10,246; `3`: 5,300; `4`: 4,579; `2`: 2,845);
- captured readings: 9,583;
- the leaving edge (`≡ 1`): 3,630.

The landing's setter exits on its first lap after `1/8` in 71,946, on a later lap in 14,355 (listed). The landing is at
the first move in 4,186; the relay runs 1 to 25 moves. The seeded sample to 64 has the same shape.

**Reading** `[derived]`. At any of these landings the condition is Theorem 6.14 at the flank `h` with
`k = (h + 8 − r)/8 + j`, which is the band test. So D3 yields no new kind of rule. The pinned pair is not one
configuration with one answer: it is the obligation localised to the class where `GridNudgeN` stops.

**What the record already says about this object** (read after the run):
- `PROOF_REQUIREMENTS_v2` §7: for whole-number differences every runner the three base rules miss has a difference
  `≡ 0 (mod 8g)`. *"The obligation is a fourth rule: produce `(D, a)` when `j ≥ 1` differences are divisible by `8g`."*
  Its candidate is the `L₀` ladder (the first live lattice, then the next): `[VERIFIED — 31,066 of 31,066]`, not proved.
- v21 §17C makes the ladder a case at `D ≤ 64` (`ResolutionClears8`; "a case boundary, not a claim").
- §17E item 5: its relation to the rational-opening fields is "not yet worked out".
- Map v3 C4: the cascade's landing `(8K+1)/(8h)` is itself a clearing resolution with `D = h`.

**Consequence:**
- D3 is the record's fourth rule. Its open content is the ladder's justification by place, and the ladder's relation to
  the cascade (whose instants are the readings' openings, while the ladder's resolutions `D` need not be readings).
  Map v3 C4 shows the two meet when `D = h`.
- The D targets of design v4 all reduce to D1, the selection. D1 is `PROOF_REQUIREMENTS_v2` §4 verbatim: *"a rule that
  produces `(D, a)` from the differences, valid for every configuration — or a finite set of rules whose side conditions
  are exhaustive"*, which is the obligation. Levels A–C and this map localise it to the captured case and the ladder;
  they do not shorten it.
- **Next, proposed:** relate the cascade's relay from a dead lattice to the ladder's next live lattice, by derivation
  first. In candidate-scale terms, when the landing's `(h, K)` is the ladder's `(D, a)`, and why. Then check.

---

## E230 — 2026-10-01 — owner: "are you making additional requirement for what looked like proof in the past?" Yes; corrected against `MANUSCRIPT_v20` §0

**Owner:** *"So you're saying if we prove D we prove the conjecture?"*, then, quoting my answer: *"Are you sure or are you
making additional requirement for what looked like proof in the past?"*

**Map:** none — a correction of my statements of the obligation, against the owner's own text.

**What stands:** proving `∃ (e, k)` for every configuration is the conjecture (`doors_agree`, Theorem 6.15, both ways).
The open part is the captured configurations that no proved case covers (`lonelyRunnerAt8_iff_residual`; every residual
set has multiples of 8).

**What I added that the owner's text does not require** (`MANUSCRIPT_v20` §0, 2026-09-24: *"A proof is a finite list of
cases. Each case is a condition on the difference set together with a proof that `(e, k)` exists on that condition. The
list closes when the conditions are jointly exhaustive."*; *"Existence is all that is owed, not a formula … by any means
— pigeonhole, contradiction, induction, construction. A closed form for `e` or `k` is more than the obligation asks."*;
*"A case proved is proof of that case."*; the foreign shapes are a cap, a move count and *"a uniform theorem — one
statement or formula covering every set"*):
1. **"cover every captured configuration uniformly"**: a uniform theorem is a foreign shape. Withdrawn.
2. **"and name its instant"**, and design v4's D1 ("from the readings, name a reading, grid, class and laps"): more than is
   owed. What is owed is `∃ (e, k)` on each case's condition, by any means. Withdrawn.
3. **"An existence argument with no bound on where" as falling short**: wrong. Existence by contradiction or pigeonhole is
   admissible (v20 §0; `exists_clear_step` is `by_contra`, `exists_fixed_of_lonely` uses pigeonhole). Propositions
   6.10–6.11 were withdrawn for their **covering statement form**, a union bound concluded from an assumed cover (§6A row
   seven; `CORRECTIONS_2026_09_17_v2` §5(b)), on the owner's question whether counts were *"added as part of a reference to
   other's needs"*. They were not withdrawn for being existence arguments.
4. **The `D ≤ 64` small-resolution case as falling short**: it is a proved case (`ResolutionClears8`, v21 §17C). A case
   proved is proof of that case. Only the verified-not-proved remainder of the `L₀` ladder (31,066 runners) is not proof,
   and only because it is finite evidence about an infinite family.
5. **"No intermediate theorem sits between D and the conjecture"**: misleading. What remains is the cases not yet covered,
   and every proved case and every reduction shrinks it. Examples: `lonelyRunnerAt8_iff_residual`; E192's reduction of the
   residual to one crowded level; the band route; E195's `(1,6)` shape at `V = 3, 4, 5`, if its residue reduction is
   accepted as proof.

**Cause (F7):**
- E229 and my answer took `PROOF_REQUIREMENTS_v2` §4 (2026-09-14, *"a rule that produces `(D, a)`"*) as the statement of
  what a proof is. `MANUSCRIPT_v20` §0 (2026-09-24, the owner's) superseded it.
- The memory that records the ruling, `feedback_n8_obligation_is_loneliness_2026_09_24`, was not read this session. It is
  linked from the oracle memory, not from `MEMORY.md`'s must-read list.
- Its own rule applies: *"Take every framing sentence … from the owner's documents. It must be quotable with file and
  section."*

**Carried to design v5 and map v4:** D1 restated as **`∃ (e, k)` on conditions that, with the proved cases, are jointly
exhaustive over the captured configurations, by any means.** D2 and D3 are restated likewise as cases.

**Consequence:** the target is unchanged in substance (the uncovered captured cases), and lighter in form: any admissible
argument for `∃ (e, k)` on a condition counts, and each proved condition is progress.

---

## E231 — 2026-10-01 — Level D as cases is `Order8SkeletonN`'s five holes; the block of three, from proved lemmas, down to one strip

**Owner:** *"Ok so lets contiunue on"* (after E230's restatement: `∃ (e, k)` on conditions, any admissible means, each
proved condition progress).

**Map:** v3 §4 Q8; design v4 restated by E230. Record first: Lean, then the log. A derivation from proved lemmas; no run.
Nearest §6 class F7, avoided this time: E229's proposed step (the relay against the `L₀` ladder) was **not run**,
because E4 and E11 already answer it. E4: the ladder's resolution is almost never a disparity, so the cascade's landing
(always a reading's opening, A.2) rarely is the ladder's `(D, a)`. E11 item 4: the ladder is *"a divisibility device,
not a scale-invariant one"*, kept as a rule.

**Level D as cases is already stated in Lean.** `Order8SkeletonN.lonelyRunnerAt8_of_arrangement_holes` (2026-09-25)
gives `LonelyRunnerAt8` from exactly five named owed statements, split on separation of scale at `T = 9` (the
organising principle of E7–E11):
- `ArrBlockRule8 f 9` for `f = 3, 4, 5, 6`: a runner whose readings split into a core and a fast block of `f` readings,
  at least 9 times the core across, is lonely. `f = 1, 2` are proved (`blockRule8_one` by R8, `blockRule8_two` by the
  fast pair).
- `ArrBoundedCovered8 9`: a scale-free runner (every consecutive ratio below 9) is lonely.

These are E230's cases. The record's architecture for the block holes (E30; log l.1757–1768) has three step types:
- separated levels by nested windows: `SplitChainN`, proved;
- compact levels by collapse: `TrainCollapseN` (a train `N + e` with `N ≥ 56m`), proved; `SyncBlockN` reduces a
  synchronised block to an `N`-free question, which is open (true on 288,288 cases);
- bounded shapes by window constants, owed.

**Derived for `f = 3`** `[derived from proved lemmas; no Lean instance built (owner, E222)]`:
- The core has `7 − 3 = 4` readings. Native order five makes it lonely at `θ = 1/5` (`lonely_five_nat`).
- `SplitChainN.lonely_of_split` then needs `needT F ≤ 2(θ − 1/8)/m = 3/(20m)`, with `m` the core's largest reading.
- For the block `x₁ ≤ x₂ ≤ x₃`, nested in any order, `needT = 1/x₃ + 1/(2x₂) + 1/(4x₁) ≤ 7/(4x₁)`. The validity
  conditions hold: `x₁(1/(2x₃) + 1/(4x₂)) ≤ 3/4`.
- So **a core of four below a block of three with `x₁ ≥ (35/3)·m` is lonely.**
- The skeleton's `T = 9` therefore leaves one strip for `f = 3`: **`9m ≤ x₁ < (35/3)m`**, and within it only blocks
  whose exact `needT` exceeds `3/(20m)`.
- `lonely_eight_of_split` uses a core of six at `1/7` (`needT ≤ 1/(28m)`, so `x₁ ≥ 49m` for three). The core's actual
  size, four at `1/5`, is what brings it to `35/3`.
- For `f ≥ 4`, nesting equal speeds is invalid (`x·needT_{f−1} = (2^{f−1} − 1)/4 > 3/4`), which is where compact
  blocks and collapse enter. Cores of 3, 2, 1 give `θ = 1/4, 1/3, 1/2` and wider windows `1/(4m)`, `5/(12m)`, `3/(4m)`.

**Consequence:**
- The first hole reduces, by proved lemmas, to the strip `9m ≤ x₁ < 35m/3` for blocks of three. The window inside the
  strip has two parts:
  - the core's actual clear window, which can be wider than the margin bound `(θ − 1/8)/m` each side;
  - the triple's true window, where `pair_window`'s constant `3/4` is proved and E7 measured `≤ 0.495` for pairs.
- This is one case in v20 §0's form: `∃ (e, k)` on a condition.
- **Next, proposed:** derive the strip for `f = 3` from the core's own clear set (a set of at most four readings, lonely
  at `1/5`) and the triple's joint clear stretches, using the `pair_window` structure. Then check exactly.

---

## E232 — 2026-10-01 — design: the cascade inside the hole `ArrBlockRule8 3 9`, read move by move

**Owner:** *"Im lost, we have holes, the cascade does not fail at these holes so then what are we missing.  Understanding
how the cascade approaches these holes so we can figure out the mechanisim?"*; then *"Yes"* to the map run, starting
with blocks of three.

**Map:** v3 §4 Q8; the hole `ArrBlockRule8 3 9` (`Order8SkeletonN`). M2 class (d), a map run: no window, no bound, no
rule proposed. The only pass conditions are derivation checks and the oracle check.

**The population: the hole, less every block-level rule already proved.**
- **The hole.** Whole-number readings: a core of four (`c₁ < … < c₄ = m`) below a block of three (`x₁ < x₂ < x₃`,
  `x₁ ≥ 9m`).
- **Excluded, because a proved rule covers them:**
  - the fast pair (`FastPair8`: `x₂ ≥ 9x₁`, so the top two are a block of two);
  - R8 (`x₃ ≥ 7x₂`);
  - the block split (`BlockSplit8`: a common factor of the block at least `28m`);
  - nested windows with the core at `θ = 1/5` (E231: the best valid order's `needT ≤ 3/(20m)`).
- **Sampling:** 2,000 seeded configurations at fine scale. The core's ratios are uniform in `(0.05, 1]` of `m`;
  `x₁/m` is uniform in `[9, 35/3)`; `x₂/x₁` and `x₃/x₂` are uniform in `(1, 2)`; the exclusions above are then
  applied.

**What is read, per path, in the hole's own objects:**
- the core's own first isolation `τ_C` (the cascade on the four core readings alone) and the core's lonely cells;
- the full set's landing `t*`, and which core cell holds it (the first, or a later one), with `t*/τ_C`;
- the path's setters in order, each marked as a core reading (C) or a block reading (B) with its lap, and the pattern
  (for example C…C then B…B);
- where the three block readings sit at `τ_C`;
- the move that ends the path, and who is nearest to entering then (the queue front, B.7).

**Forced before running (checks):**
- C1: `t*` equals the least clear point of the full set, computed without the cascade.
- `t* ≥ τ_C`: the core is clear at `t*`, and `τ_C` is the core's first lonely instant (A.9 applied to the core).
- `t*` lies in a lonely cell of the core (it is clear there).

**After the run:** look for what every path has in common, and read every path that differs (M3) before stating
anything.

## E233 — 2026-10-01 — the cascade inside the hole `ArrBlockRule8 3 9`: a core relay, then a block relay inside the core's lonely stretches

**Map:** v3 §4 Q8; E232's design, run as designed. M2 class (d), a map run. The pass conditions are derivation checks
and the oracle check. No rule is proposed.

**Scripts** (`LonelyRunner/experiments/nN/redo/`, each `.py` with its `.out`; all three use the same 2,000 configurations,
`gen(232, 2000)`):
- `hole3_cascade_v1`: E232's reading (setters, pattern, landing stretch, block positions at `τ_C`);
- `hole3_cascade_v2`: the block's own relay from `τ_C` against the core's first stretch;
- `hole3_cascade_v3`: every path that differs, read move by move.

**Checks (all 0 failures):**
- E232's three: C1 (`t*` equals the least clear point of the full set, computed without the cascade); `t* ≥ τ_C`; `t*` lies
  in a lonely stretch of the core.
- v2: `t*` is in the core's first stretch exactly when the block's own relay from `τ_C` lands before that stretch closes,
  and then `t*` is that landing.
- v3, F1: a move made from an instant inside a core stretch has only block setters (the core is clear there, A.1).
- v3, F2: `t*` is the block's own relay (the three block readings alone) run from the path's first instant inside the
  stretch that holds `t*`.

**What every path shares `[derived from A.1; checked F1, F2]`.** Write `S₀, S₁, …` for the core's lonely stretches from
`τ_C` on (the core's own cascade lands at `τ_C`, the start of `S₀`).
1. **Before `S₀`, the core relays.** 406 of the 411 moves made before `S₀` have a core setter.
2. **Inside a stretch, the block relays.** Every move made from inside a stretch (1,489) has a block setter (F1). From the
   path's first instant in a stretch, the path is the three block readings' own relay (F2).
3. **The landing** is the block's relay landing, in the first stretch where that relay lands before the stretch closes.

The 2,000 configurations split as follows:

| landing stretch | count | path |
|---|---|---|
| `S₀`, `t* = τ_C` | 866 | no block reading in the way at `τ_C` |
| `S₀`, `t* > τ_C` | 1,106 | 1 to 3 block moves from `τ_C` (patterns B1, B2, …); 5 of these enter `S₀` past `τ_C` (below) |
| `S₁` | 28 | the block's relay overran `S₀` (below) |

**Every path that differs, read move by move (M3; `hole3_cascade_v3.out`).**
- **The 28 landing in `S₁`.**
  - *Feature.* The block's relay from `τ_C` is longer than `S₀`. In laps of `x₁`, `S₀` has length 0 to 0.334 in these
    28 and the block's relay 0.045 to 0.533 (v2 lists each pair).
  - *What forces the witness.* The block move that would land past `S₀`'s end does land there, in the gap. In the gap
    every move (41 over the 28 paths) has a core setter, sometimes with block readings in the way as well. So from the
    gap the path is the core's own relay, which lands at the core's first lonely instant after the gap: the start of
    `S₁` (all 28 enter `S₁` at its start). The block then relays inside `S₁` (F2): 0 to 3 moves, 20 in all.
  - *Same mechanism.* Yes: steps 1 to 3 applied again from the gap.
- **The 5 that do not pass through `τ_C`.**
  - *Feature.* At the core's last move before `τ_C`, a block reading is also in the way, and its exit is later than the
    core reading's (by under 0.15 laps of `x₁`).
  - *What forces the witness.* That block reading sets the move (B.1, the latest exit), so the path enters `S₀` past
    `τ_C`. The block then relays from there inside `S₀` (F2).
  - *Same mechanism.* Yes: step 2 from a later entry instant. All 5 have a long `S₀` (0.94 to 7.46 laps of `x₁`) and
    land in it.
- **The single-point stretch.** For the core `(70, 490, 729, 1000)`, `S₀` is the single instant `τ_C`. A block reading is
  in the way there, so the block's move leaves `S₀` at once. The path then follows the 28 above (one of them).

**Records, not forced (scoped to this sample):**
- No block reading set a move in a gap (0 of 41). The derivation allows it: a core reading near its leaving edge can
  exit before a fast block reading in the way does. This is therefore not a statement.
- No path landed beyond `S₁`.
- The block's relay from `τ_C` took at most 0.686 laps of `x₁`.

The last two are *when at the latest* shapes. They are recorded as data, and promoting either to a statement would be a
cap (memory `feedback_n8_cascade_is_the_oracle`, interval check step 2).

**Import check.**
- *Place test.* Class: the hole less the proved block rules. Place: the block's relay landing from the path's entry instant
  into a core stretch. The entry instant is the core's own landing (`τ_C`, or the start of `S₁`) except in the 5 above.
  Both relays are cascades on subsets of the readings, so the place is constructed from the readings.
- *Interval check.* Delete "inside the stretch" and what remains, "the block's relay from the entry instant", still
  constructs the instant. The stretches are where that relay is cut off: they are the core's own lonely set, not a window
  in `u`. Rewritten in `u = c₁·t`, they are not register item 15 (they start at the core's isolation, not at `u = 1/8`),
  and no uniform `u ≤ X` is stated.

**Consequence (M7, for map §9).**
- In this hole the cascade is two cascades of lower order composed:
  - the core's (four readings: order 5, native and proved);
  - the block's (three readings: order 4, native and proved), run from an entry instant rather than from its own bound.
- So the proof-form question for `ArrBlockRule8 3 9` is not whether some instant exists. It is, per configuration, which
  core stretch holds the block's relay landing. The record's route (`lonely_of_split`, E231) answers it with a uniform
  margin around one core instant and a uniform `needT`, which is why it leaves the strip `9m ≤ x₁ < 35m/3`. The cascade
  answers it with the actual stretch and the actual relay, and moves to the next stretch when the first is too short.
- The block's relay from an arbitrary entry instant, in its own readings, is the object this points to. It is not yet
  read: no run here asks where the three-reading relay lands from a given instant.
- Next on the owner's sequence: blocks of four to six (E232), read the same way, to see whether steps 1 to 3 hold with a
  larger block.

## E234 — 2026-10-01 — design: the holes `ArrBlockRule8 f 9`, `f = 4, 5, 6`, read the same way

**Owner:** *"Yes"* to E232's map run, *"starting with blocks of three"*; the sequence continues to four, five and six.

**Map:** v3 §4 Q8; E232's design carried to the other three block holes. M2 class (d), a map run. The pass conditions
are derivation checks and the oracle check. E233's place (the block's relay from the entry instant into a core stretch)
is compared with the landing as check F2. No rule is proposed.

**The population, per `f`:** whole-number readings; a core of `7 − f` (`c₁ < … < m`, `m = 1000`, the others uniform in
`(0.05, 1]·m`) below a block of `f`. `x₁/m` is uniform in `[9, 60]`. This is a search range, not a statement. For
`f = 3` nested windows cover everything above `35m/3` (E231). For `f ≥ 4` no such edge was derived, so the range is
wider and the excluded share is recorded by rule. Consecutive block ratios are uniform in `(1, 2)`. 1,000
configurations per `f`.

**Excluded, because a proved rule covers them.** Each rule is checked on every split of the seven readings into a
slower part and a top-`k` part, not only on the hole's own split:
- R8 (`lonely_eight_of_fast`: `7s < V` for every other reading `s`);
- the fast pair (`FastPair8`);
- the block split (`BlockSplit8`: a top-`k` set whose common factor is at least `28 ×` every other reading). A
  non-top set cannot satisfy it;
- the train collapse (`lonely_of_train_collapse`): a top-`k` set, `k ≥ 2`, with spread at most `m'` and least element at
  least `56m'`, where `m' = max(the other readings, the spread)`. The midpoint condition holds for two adjacent offsets;
- nested windows (`lonely_of_split`): the slowest `j` readings as the core, lonely at `θ = 1/(j + 1)` (native orders
  `j + 1 ≤ 7`), the rest as a valid nested list in its best order, with `needT ≤ 2(θ − 1/8)/(largest core reading)`.

**Checks (forced):** C1, `t* ≥ τ_C`, `t*` in a core stretch (E232); F1 and F2 (E233).

**Records:** the stretch holding `t*`; the setters by region (before `S₀`, inside `S_k`, in the gap after `S_k`) and
class (C or B); the paths that do not pass through `τ_C`; every path landing beyond `S₀`, read move by move; any block
setter in a gap.

**After the run:** what every path shares, then every path that differs, read (M3) before anything is stated.

## E235 — 2026-10-01 — the holes `f = 4, 5, 6`: the same two relays; overruns only at `f = 4` (2 of 1,000)

**Map:** v3 §4 Q8; E234 run as designed. M2 class (d). Script `LonelyRunner/experiments/nN/redo/holef_cascade_v1.{py,out}`.

**Population, as sampled.** Only nested windows fired among the exclusions, removing 1,384, 87 and 3 draws for
`f = 4, 5, 6`. R8, the fast pair, the block split and the train collapse never fired. With consecutive block ratios in
`(1, 2)` they cannot (R8 and the fast pair need a ratio of 7 or 9). The block split and the train would need the block's
common factor, or its least element, at least 28 or 56 times its spread, and no draw had that. So this is the hole for
blocks of consecutive ratio below 2. `x₁/m` of those kept is spread over `[9, 60]` (v1.out lists it by decade).

**Checks (all three `f`, 0 failures):** C1, `t* ≥ τ_C`, `t*` in a core stretch, F1, F2.

**What every path shares.** E233's steps 1 to 3 hold at every `f`:
1. the core relays to `τ_C`;
2. inside a core stretch only block readings set moves (F1), and the path from its entry instant is the block's own relay
   (F2);
3. the landing is that relay's landing, in the first stretch where it lands before the stretch closes.

| `f` | core | `t* = τ_C` | lands in `S₀` | lands in `S₁` | block moves inside the landing stretch | moves before `S₀` (C / B) |
|---|---|---|---|---|---|---|
| 4 | 3 | 302 | 998 | 2 | 0 to 6 | 110 / 1 |
| 5 | 2 | 273 | 1,000 | 0 | 0 to 6 | 36 / 0 |
| 6 | 1 | 191 | 1,000 | 0 | 0 to 8 | 0 / 0 |

**`f = 6`, derived.** The core is the one reading `m`. Then `τ_C` is the bound `1/(8m)`, and `S₀ = [1/(8m), 7/(8m)]` is
`m`'s own clear stretch. Its length `3/(4m)` is `(3/4)(x₁/m) ≥ 27/4` laps of `x₁` (output: the least is 6.85). Every
path is the block of six relaying from the bound inside `m`'s first clear stretch.

**Every path that differs, read (M3; `f = 4`, listed in full in the `.out`).**
- **The 2 landing in `S₁`.**
  - *Feature.* `S₀` is short (0.030 and 0.279 laps of `x₁`), and a block move from inside it lands in the gap.
  - *What forces the witness.* In the gap the core sets every move (2 of 2), so the path is the core's own relay to the
    start of `S₁`. Both land at that start with no block move there: the block is clear when `S₁` opens.
  - *Same mechanism.* Yes: E233's 28.
- **The 1 not passing through `τ_C`.** Core `(108, 970, 1000)`, block `(39406, 59510, 81409, 100943)`. At the last move
  before `S₀`, block reading 59510 is in the way with core reading 970 and exits later. It sets the move, and the path
  enters `S₀` at `+0.070` laps of `x₁`. *Same mechanism.* Yes: E233's 5.
- **Block setters in a gap:** none at any `f`.

**Records, not forced (scoped to this sample).** No path landed beyond `S₁`. The block's relay from `τ_C` took at most
0.769, 0.728 and 0.961 laps of `x₁`. Both are *when at the latest* shapes and are not statements (E233).

**Overruns by `f` (E233 and E235 together).** 28 of 2,000 at `f = 3`, 2 of 1,000 at `f = 4`, 0 at `f = 5, 6`. The smaller
the core, the longer its lonely stretches, in laps of `x₁`. At `f = 6` the stretch is at least 27/4 laps, by derivation.

**Consequence (M7, for map §9).**
- Across the four block holes the cascade is one structure: the core's cascade (order `8 − f`, native), then the block's
  cascade (order `f + 1`, native) run from an entry instant, cut off where the next core reading enters the way.
- **The place for each hole** is the block's relay landing from the entry instant into the core's lonely set. The
  condition of a case is that this landing comes before the first core entering edge after the entry. Both are edge
  events of the readings (Level C's edge forms), so the case is stated in the framework's own objects.
- **What this shows is missing from the record.** The record's proved rules replace the block's relay by a uniform need
  (`needT`, `pair_window`) and the core's stretch by a uniform margin (`θ − 1/8`), which is why they leave the strip at
  `f = 3` and every block of consecutive ratio below 2 at `f ≥ 4` (1,384 of 2,384 draws excluded at `f = 4`, 87 of 1,087
  at `f = 5`, 3 of 1,003 at `f = 6`). The cascade uses neither. The block's own relay from a given instant, in the
  block's readings, is the object that has not been read. It is the next map item.

## E236 — 2026-10-01 — design: perturbing the hole paths through the cascade, one reading at a time

**Owner:** *"So we are going to use the cascade to show this happening. Are doing that by perturbing the examples or
constructing examples so we can see what happens with the cascade?"*; then, to the perturbation proposal, *"ok go ahead"*.

**Map:** v3 §4 Q8; E233/E235's exceptions. M3 on them, by the owner's method (E67: *"use the cascade pertubate the
speeds to find the mechanisim"*). This is a derivation from Level C, checked by exact perturbation (M8). No rule is
proposed.

**Notation.**
- `g` is the block's relay landing from `τ_C`: the first instant at or after `τ_C` at which the block is clear. It is
  the exit of block reading `h` on lap `K`, `8hg = 8K + 1`.
- `b₀` is the end of `S₀`, where core reading `c` reaches its entering edge on lap `k`, `8cb₀ = 8k + 7`.

**Derived (A.9, C.5).** The core is clear on all of `S₀`, so the full set has a lonely instant in `S₀` exactly when
`g ≤ b₀`, and then lands at `g`. The landing therefore leaves `S₀` at one wall, `g = b₀`, i.e.
`h(8k + 7) = c(8K + 1)`. That is C.5's entering face with `c` as the moving reading: `c` on its entering edge at `h`'s
exit. Two readings move it:
- `W_c`: move `c` to `c* = (8k + 7)/(8g)`. Slower than `c*` is inside (`b₀ > g`).
- `W_h`: move `h` to `h* = (8K + 1)/(8b₀)`. Faster than `h*` is inside (`g < b₀`).

**Predicted at the wall, at relative `η = 10⁻⁹`:**
- W1 (inside): the landing is in `S₀`, at `g`, within `O(η)` of `b₀`.
- W2 (outside): the path visits `g`, and its next instant is `c`'s exit on lap `k + 1`, `(8k + 9)/(8c)`. That is C.5's
  one more move. The core then relays on.

**Predicted along a walk.** The moved reading goes in a straight line from its value to the wall, 100 grid points, and
any change of the landing's stretch index between grid points is located by bisection. The prediction: the index changes
only at walls of the form `g = b₀`, possibly with other readings named if the finite move changed `h`, `K`, `c` or `k`.
Every other change is classified (a jump of `τ_C`, which relabels the stretches; anything else) and listed to be read.

**The late entries (6).** At the core's last move before `S₀`, block reading `b` (lap `L`) sets, exiting after the core
reading that exits at `τ_C`. The tie wall is `b* = (8L + 1)/(8τ_C)`. Predicted (C.3, C.4) at `b*(1 ± η)`: the same
landing on both sides. On the faster side the path passes through `τ_C`; on the slower side it does not.

**Populations:**
- the 30 overruns (E233: 28; E235: 2);
- the 6 late entries;
- controls, landing in `S₀` with `t* > τ_C` and entering at `τ_C`: 100 seeded from `f = 3`, and 50 each from
  `f = 4, 5, 6`. For these the walk goes the other way, from `S₀` out across the same wall.

**Checks:**
- W1, W2 and T1;
- C1 (the landing equals the least clear point, without the cascade) at every wall-side point.

A finite move that changes `(h, K)`, `(c, k)` or `τ_C` by the time it reaches the wall is counted as *region moved*
(C.5's term) and listed, not failed. Pass condition: 0 failures. Every switch off the predicted wall type is read before
anything is stated.

## E237 — 2026-10-01 — the hole paths perturbed: the landing leaves `S₀` at one wall, `g = b₀`, and nowhere else

**Map:** v3 §4 Q8; E236 run as designed. M3 on E233/E235's exceptions, by perturbation through the cascade.

**Scripts** (`LonelyRunner/experiments/nN/redo/`, each `.py` with its `.out`):
- `hole_perturb_v1`: the first run. Its 14 C1 failures were a fault in the check, not in the cascade. `c1_ok` started the
  clear set at `1 / S[0]` with `S[0]` an integer, which is a float; all 14 were landings exactly on the bound
  (0 moves), where the landing and the least clear point agree as rationals (read in the scratch debug, then fixed);
- `hole_perturb_v2`: exact C1; walks in every order-preserving case; R0 at every walk point;
- `hole_perturb_regions_v1`, `hole_perturb_e1_read_v1`, `hole_perturb_e1_refined_v1`: the region-moved cases, read and
  explained.

**Failures in v2 and after: none.** That covers W1, W2, T1, C1 at every wall-side point, and R0 at every grid and
bisection point of 403 one-reading walks (101 grid points each).

**R0, the derived rule** `[derived from A.9; checked at every walk point]`: the full set lands in `S₀` exactly when
`g ≤ b₀`, and then at `g`. Here `g` is the block's relay landing from `τ_C`, and `b₀` is `S₀`'s end. The landing leaves
`S₀` only where that inequality changes.

**1. Moving the core reading `c` that closes `S₀` (`W_c`).**

| population | wall reached; W1 and W2 hold | region moved | skipped (order) |
|---|---|---|---|
| 30 overruns | 29 | 0 | 1 |
| 250 controls | 194 | 56 | 0 |

- At the wall `c* = (8k + 7)/(8g)`: just slower, the landing is in `S₀` at `g`, at `b₀`. Just faster, the path visits `g`,
  and its next instant is `c`'s exit on lap `k + 1`. That is C.5's entering face, the one more move.
- Along every walk from an overrun to the wall, the landing stays in `S₁` until the wall (29 of 29).
- **E2 (region moved), checked on all 56.** `c` also sets `τ_C` (54), or `τ_C` jumps along the move (2). Moving `c` then
  moves the relay's start. All 50 controls at `f = 6` are of this kind, since the one core reading sets both ends of `S₀`.
  No control in which `c` does not set `τ_C` had its region moved (223 of 223).

**2. Moving the block reading `h` whose exit is `g` (`W_h`, the overruns).** The wall is reached in 17. In 12 the
region moved, and 1 was skipped for order.
- **E1′** `[derived; checked 29 of 29, hole_perturb_e1_refined_v1.out]`: moving `h` alone reaches the wall exactly
  when every other block reading is clear at `b₀`. The move shifts no other reading. If a reading `x` is in the way at
  `b₀`, its exit past `b₀` holds the relay past `b₀` whatever `h` does.
- *How E1′ was reached (M3).* The first statement, E1 ("`g` is the only relay instant past `b₀`"), failed on 3 cases.
  Reading them move by move (`hole_perturb_e1_read_v1.out`) showed the reading holding the relay past `b₀` was a second
  crowd member in the same move (2 cases), or the setter of the next move (1 case). Those are not relay instants, so E1
  missed them. E1′ states the condition at `b₀` itself.
- So an overrun can be held by more than one block reading. In that case no single block reading's move undoes it, but
  the closing core reading's move always does (part 1).

**3. The late entries (T1, 6 of 6).** At the tie wall `b* = (8L + 1)/(8τ_C)` the landing is the same on both sides. The
path passes through `τ_C` only on the faster side. A late entry is therefore a change of route, not of landing (C.3, C.4).
In 4 of the 6, the finite move to the wall itself changed the landing, which is the effect of moving a reading a finite
distance (C.5 Gap C2a).

**4. Every other change of landing stretch along the walks** (7, in 5 control walks). Each is classified by what was
discontinuous across the bisection bracket, and R0 held on both sides of each:
- **`g` jumps forward past `b₀`** with `τ_C` fixed (3): the block-clear interval holding `g` closes up;
- **`g` jumps back to `τ_C`** (3): a block reading leaves the way at `τ_C`, so the block is clear there;
- **`τ_C` jumps** (1): the core gains an earlier lonely stretch, which relabels the stretches.

None is unclassified.

**Import check.** Place: `g`, the block's relay landing from the entry instant, which is an instant. Delete "in `S₀`"
and what remains, "the landing is `g` when `g ≤ b₀`; otherwise the core relays to its next stretch and the block relays
again", still constructs the instant from the readings. The wall `h(8k + 7) = c(8K + 1)` is an edge form (C.1). There is
no window in `u`, no cap and no rate.

**Consequence (M7, for map §9).**
- The overrun is C.5's entering face, located: the landing region of `S₀` meets the region of `S₁` along the wall
  `g = b₀`. Perturbation crosses it exactly where predicted, and along 403 walks the landing changed stretch nowhere else
  except at the named jumps of `g` and `τ_C`.
- For the proof form (v20 §0), a hole configuration's case is decided by the sign of `b₀ − g`. That is an edge form in the
  readings once the relay's setters and laps are fixed. Within each case, the instant is `g` (in `S₀`) or the same
  construction from the start of `S₁`.
- E1′ adds a fact the earlier runs did not show: an overrun can be held at `b₀` by more than one block reading.
- The open object is unchanged from E235: `g` itself, the block's relay landing from a given instant, in the block's
  readings.

## E238 — 2026-10-01 — design: `g`, the block's relay landing from the entry instant, read in the block's readings

**Owner:** *"Well we better do that now"* (on E237's open object `g`).

**Map:** v3 §4 Q8; the object E235 and E237 left open. M2 class (d), a map run. Record first:
- v21 §6.10, *"The cascade is a sort and a scan"*: from the bound, the landing is the largest clear candidate scale,
  `[VERIFIED 32,000 of 32,000]`;
- Corollary 6.24: every instant the cascade visits is a candidate;
- Theorem 6.19: the clearance criterion;
- §6.9 and §6.11: the flank framework. At reading `h`'s exits on laps `K, K + 1, …`, every other reading walks by
  `8·frac(d/h)` per lap.

Nothing here is new as a statement. The run reads `g` in those terms, from the hole's own entry instants instead of the
bound.

**The object.** For entry instant `t₀`, each block reading `h` is a flank, with openings `(8K + 1)/(8h)` for
`K ≥ K₀(h)`, where `K₀(h)` is the first lap whose opening is at or after `t₀`. The opening of lap `K₀ + j` is the flank's
index `j`. Derived from A.9 from `t₀` and Corollary 6.24: `g = t₀` if the block is clear at `t₀`; otherwise `g` is the
least clear flank opening at or after `t₀`, over the block's readings. So `g` is named by a pair (`h`, `j`).

**Populations: the hole configurations of E233 and E235, at their actual entry instants.**
- `t₀ = τ_C` for all 5,000 (2,000 at `f = 3`, 1,000 each at `f = 4, 5, 6`);
- `t₀` = the start of `S₁` for the 30 overruns.

**Checks (forced):**
- G1 (oracle, by a second route): `g` from the relay equals the least clear flank opening at or after `t₀`, found by
  scanning each flank with Theorem 6.19's criterion and no cascade.
- G2: when `g > t₀`, the winning flank is the relay's last setter.
- G3: every relay instant after `t₀` is an opening of its setter's flank.

**Records, per path:**
- whether the block is clear at `t₀`;
- the winning flank `h`, by rank in the block, and its index `j`;
- whether `h` was in the way at `t₀`, and whether `g` is the latest exit among the readings in the way at `t₀` (a landing
  in one move);
- the number of moves, and the number of flank openings in `(t₀, g)` that the relay passed without visiting;
- for each read path, the winning flank's scan from `K₀`: each opening clear or blocked, and by which reading at which
  reading mod 8.

**After the run:** what every path shares, then every path that differs, read (M3) before anything is stated. Indices
and move counts are records, not statements. A ceiling on either would be a cap (memory
`feedback_n8_cascade_is_the_oracle`, interval check step 2).

## E239 — 2026-10-01 — `g` read in the block's readings: the least clear flank opening after the entry

**Map:** v3 §4 Q8; E238 run as designed, then M3 on what it showed.

**Scripts** (`LonelyRunner/experiments/nN/redo/`, each `.py` with its `.out`):
- `hole_g_flank_v1`: the flank reading of `g`;
- `first_exit_three_v1`, `first_exit_three_v2`, `first_exit_three_spread_v1`, `first_exit_three_v3`: exhaustive tests of
  the `f = 3` regularity;
- `hole_g_three_control_v1`: an attempt to build a hole configuration to order.

**Checks (0 failures on all 5,030 relays):**
- G1 (oracle by a second route): `g` from the relay equals the least clear flank opening found by scanning each block
  reading's exits with Theorem 6.19's criterion, no cascade.
- G2: the winning flank is the relay's last setter.
- G3: every relay instant is an opening of its setter's flank.

**`g` in the block's readings** `[derived from A.9 and Corollary 6.24; checked G1]`. `g = t₀` if the block is clear at
the entry; otherwise `g` is block reading `h`'s exit on lap `K₀(h) + j`, the least clear flank opening at or after `t₀`.
This is v21 §6.10's sort and scan, run from the entry instant instead of the bound.

| `f` | entry `t₀` | clear at `t₀` | winner by rank (slowest first) | index `j` of the winner | moves |
|---|---|---|---|---|---|
| 3 | `τ_C` | 866 | 495 / 274 / 365 | 0: 1,134 | 1 to 3 |
| 3 | start of `S₁` | 13 | 5 / 5 / 5 | 0: 15 | 1 to 3 |
| 4 | `τ_C` | 302 | 173 / 157 / 186 / 182 | 0: 687; 1: 11 | 1 to 6 |
| 4 | start of `S₁` | 2 | | | |
| 5 | `τ_C` | 273 | 93 / 119 / 149 / 175 / 191 | 0: 662; 1: 57; 2: 7; 3: 1 | 1 to 6 |
| 6 | `τ_C` | 191 | 78 / 82 / 118 / 141 / 184 / 206 | 0: 649; 1: 114; 2: 34; 3: 11; 4: 1 | 1 to 8 |

Further records:
- The winner was in the way at `t₀` in 835 of 1,134 relays at `f = 3`. There, and only there, `g` is the latest exit
  among the readings in the way at `t₀`, reached in one move.
- No two flanks opened at `g` together.

**The paths that differ: `j > 0` (`f = 4, 5, 6`; 236 paths, 41 read in full in the `.out`) (M3).**
- *Feature.* The winner is one of the faster readings (rank 3 or above, except one rank-2 winner at `f = 5`). Its first
  openings after `t₀` are blocked by other block readings inside their in-way arcs (readings 7.0 to 8.0 or 0.0 to 0.9
  eighths at that opening; listed per path).
- *What forces the witness.* The relay first takes the blockers' exits (setters with `j = 0`). The landing is the fast
  reading's later lap, the first of its openings at which no slower block reading is in the way.
- *Same mechanism.* Yes: G1 held on all 236. `j > 0` only says that the least clear opening is not a first exit.

**The `f = 3` regularity, tested (M3 on a record, not a statement).** At `f = 3` the landing was always some reading's
first exit after `t₀` (`j = 0`, 1,149 of 1,149).
- *Not forced for three readings.* Exhaustive and exact over whole-number triples and every start
  (`first_exit_three_v1`, `v2`): 3,830 of 9,880 triples up to 40 have a start at which no first exit is clear (P1 fails).
  On the tight triples tested in `v2`, P1 and P2 ("the landing is a first exit") fail on the same triples: 774 of the
  24,052 triples up to 80 with spread below 2.2, and 20 of the 84,533 with `81 ≤ c ≤ 160` and spread below 1.62.
- *The spread of a failing triple has no floor in sight.* The least spread falls with height: 2.125, 1.833, 1.719 and
  1.609 for `c` in 1–20, 21–40, 41–60 and 61–80, then 1.569 at `(72, 73, 113)` for `c ≤ 160`. The hole's `f = 3` blocks have
  spread 1.003 to 1.617 (`first_exit_three_spread_v1`), and their readings are near `10⁴`. So the record is scoped to this
  sample. It is not a property of tight blocks, and no threshold is claimed. (v12's `53/462` floor decayed the same way.)
- *A control built to order was not possible.* Placing the hole's entry on a failing start of `(8, 15, 29)` put every
  in-strip candidate under nested windows (`hole_g_three_control_v1`: 0 built; 73 covered, 1,527 outside the strip).
- *The shape of every failure below spread 1.62* (`first_exit_three_v3`; all 21 with `c ≤ 160`). Two close readings
  (`b/a ≤ 1.09`, `b − a` from 1 to 8, equal to 1 in 10 of them) and a third at `c/a` from 1.569 to 1.617. Twenty have
  exactly two failing starts and one has four. So these failures can be **constructed** to a shape rather than searched
  for (owner: *"we can now construct rather than search to be able to look for the mechanisim"*). That is E242.

**Import check.** Place: `g`, an instant named by `(h, j)` from the readings and the entry. The index `j` and the move
counts are records. A ceiling on either would be a cap, and none is stated.

**Consequence (M7, for map §9).**
- Within a core stretch, the hole's case is now named fully in the readings: the block's least clear flank opening `(h, j)`
  after the stretch's entry, against the stretch's closing edge `(c, k)`.
- The `f = 3` hope that `g` is always a first exit does not hold for three readings in general. Any proof of the hole has
  to deal with `j > 0` at every `f`.
- The next item is the owner's (E240): record every isolation, not only the cascade's.

## E240 — 2026-10-01 — design: the record of every isolation, not only the cascade's

**Owner:** *"So when we find an isolation, are we mapping what other isolation occur for that given speed via BSM.
Maybe we should be keeping a record of what other isolations there are other than the one cascade points to"*; then
*"Ok continue on with that"*.

**Map:** v3 §4 Q8 and the obligation. Theorem 6.15 and v20 §0 ask for *some* isolation; first-ness is a by-product (E200,
§6A). Until now each run kept only the cascade's isolation. The C1 check computed the clear set and discarded everything
after its first point. This builds a record.

**Scope.**
- For whole-number readings the lonely set has period 1 and is symmetric about 1/2, so `(0, 1/2]` holds every isolation
  up to those two maps (`GrandReturnN.exists_lonely_iff_half`).
- Populations: the hole configurations of E233 (`f = 3`, 2,000) and E235 (`f = 4, 5, 6`, 1,000 each).

**What is recorded, per configuration, as certificates.** An instant is named by `[reading rank, lap]`: an exit
`(8K + 1)/(8d)` on the left, an entering edge `(8K + 7)/(8d)` on the right.
- Every core lonely stretch `S_k` in `(0, 1/2]`, with both ends named.
- For each stretch, the block's relay landing from its start, `g_k`. If `g_k` lies in `S_k`, the stretch holds an
  isolation and `g_k` is the first of them; otherwise the stretch holds none.
- For the first ten stretches, every isolation in the stretch, both ends named.
- The cascade's isolation, by stretch index and certificate.

**Storage.** The full record (`hole_isolations_f<f>_v1.jsonl.gz`, about 45 MB) regenerates exactly from the seeded
script and stays on disk, not committed. The committed record is `hole_isolations_subset_v1.jsonl.gz`: the first 100
configurations of each `f`, and every configuration whose cascade lands beyond `S₀`.

**Checks:**
- I1: the cascade's isolation is the first recorded one (A.9).
- I2: in the first ten stretches, the clear set computed without the cascade gives `g_k` as the first isolation, and
  none exactly when `g_k` lies past the stretch's end.
- I3: every recorded isolation is lonely at its left end (exact).

**Reported:** places and lists only (which stretches hold isolations, and how many isolations each of the first ten
holds). No totals of time, shares or coverage (register items 4 and 8).

## E241 — 2026-10-01 — the isolation record, built: every core stretch in `(0, 1/2]`, and which hold isolations

**Map:** v3 §4 Q8; E240 run as designed.

**Scripts** (`LonelyRunner/experiments/nN/redo/`):
- `hole_isolations_v1.{py,out}`: the record. The full record is in `hole_isolations_f<f>_v1.jsonl.gz`, on disk and not
  committed, about 45 MB; it regenerates exactly. The committed part is `hole_isolations_subset_v1.jsonl.gz`.
- `hole_isolations_runs_v1.{py,out}`: runs of consecutive stretches holding none.

**Checks I1, I2, I3: 0 failures** at every `f`.
- I1: the cascade's isolation is the first one recorded.
- I2: the first ten stretches computed without the cascade agree with `g_k`.
- I3: every recorded isolation is lonely at its left end.

**The record (places and lists).**

| `f` | configurations | core stretches in `(0, 1/2]` (each) | stretches holding none (all configurations) | configurations with every stretch holding | longest run holding none |
|---|---|---|---|---|---|
| 3 | 2,000 | 278 to 825 | 28,615 of 1,090,481 | 4 | 3 (13 configurations); 2 in 446 |
| 4 | 1,000 | 314 to 832 | 4,280 of 574,420 | 131 | 3 (1); 2 in 19 |
| 5 | 1,000 | 394 to 750 | 2,490 of 574,192 | 273 | 1 |
| 6 | 1,000 | 500 | 0 of 500,000 | 1,000 | 0 |

- The first ten stretches all hold isolations in 1,559, 940, 969 and 1,000 configurations for `f = 3, 4, 5, 6`. Where one
  holds none, it is usually alone among the ten.
- Isolations per stretch in the first ten: 0 to 21 at `f = 3`; over 100 at `f ≥ 4` (listed in the `.out`).
- **A lead tested and not upheld:** "a stretch holding none is always followed by one that holds" fails at `f = 3` and
  `f = 4` (runs of two and three, listed). That no path landed beyond `S₁` (E233, E235) is a record of where these
  populations' empty stretches fell: an empty `S₀` was rare, and `S₀` and `S₁` were never both empty. It is not a
  property of the hole.
- **At `f = 6` every core stretch holds an isolation**, in all 500,000. The core is the one reading `m`, and every stretch
  is one of `m`'s clear arcs, at least 27/4 laps of `x₁` long (E235). This is a record, scoped to these 1,000.

**Import check.** Places: each recorded isolation is named by certificates, and each stretch's first isolation is
`g_k`. Counts of stretches and isolations are records of places. No time totals, shares or coverage are stated.

**Consequence (M7).**
- The obligation needs one isolation per configuration, and the record shows that in the block holes there are many: in
  every core stretch but a few per configuration at `f = 3, 4, 5`, and in every stretch at `f = 6`.
- The cascade's isolation is the first. The record now lets a candidate place be checked against *every* isolation,
  not only the first (the oracle memory's scope rule: a rule naming *a* lonely instant is checked by exact loneliness).
- What decides whether a stretch holds an isolation is the same comparison as in E237 (`g_k` against the stretch's
  closing edge), now available for every stretch.

## E242 — 2026-10-01 — design: the `f = 6` hole beyond consecutive ratio 2 (step 1 of the owner's two)

**Owner:** *"Can we close that hole and then move to formalise it?"*; on the plan (1. extend the population, 2. construct,
3. read the native reason in flank form, 4. formalise), *"Yes start with step 1 and then 2"*.

**Map:** v3 §4 Q8; the hole `ArrBlockRule8 6 9`. M2 class (d), a map run. E235's `f = 6` population had consecutive
block ratios in `(1, 2)` only. Blocks with some consecutive ratio between 2 and 9 that no proved rule covers are also
in the hole and have not been read.

**Population.** The core is the one reading `c = 1000`. The block has `x₁/c` uniform in `[9, 60]`, and each
consecutive ratio `x_{i+1}/x_i` log-uniform in `[1, 9)`. Kept only if:
- some consecutive ratio is at least 2;
- the total spread `x₆/x₁` is at most 64 (a search range, not a statement);
- no proved rule covers the set: R8, the fast pair, the block split, the train collapse, or nested windows on every
  split (`holef_cascade_v1.covered`).

1,000 configurations are kept, seed 242. Exclusions are recorded by rule.

**Read, per configuration, with the checks of E235, E239 and E241 (all forced, pass condition 0 failures):**
- C1, `t* ≥ τ_C`, `t*` in a core stretch, F1, F2;
- G1–G3 for the block's relay from `τ_C`;
- I1–I3 for the isolation record of all 500 of `c`'s arcs in `(0, 1/2]`.

**Records:**
- the stretch holding the cascade's isolation;
- the winning flank's rank and index `j`;
- the block's relay from `τ_C`, in laps of `x₁` (a record; a ceiling would be a cap);
- the arcs holding no isolation, and their runs;
- every configuration whose cascade lands beyond `c`'s first arc, read move by move.

## E243 — 2026-10-01 — the `f = 6` hole beyond ratio 2: the same, every arc of `c` holds an isolation

**Map:** v3 §4 Q8; E242 run as designed. Script `LonelyRunner/experiments/nN/redo/hole6_wide_v1.{py,out}`. The
full isolation record is in `hole6_wide_isolations_v1.jsonl.gz` (23.5 MB, on disk, not committed; it regenerates
exactly). The first 100 configurations are committed as `hole6_wide_isolations_subset_v1.jsonl.gz`.

**Population.** 1,000 kept.
- Max consecutive ratio of the kept: 2 (216), 3 (268), 4 (237), 5 (141), 6 (73), 7 (31), 8 (34).
- Spread `x₆/x₁` from 2 to 64.
- Excluded: 8,921 outside the search range, 825 by nested windows, 53 by R8, and 30 with every ratio below 2.

**Checks: 0 failures** (C1, `t* ≥ τ_C`, `t*` in a core stretch, F1, F2, G1–G3, I1–I3).

**Records:**
- The cascade lands in `c`'s first arc in 1,000 of 1,000.
- **Every one of `c`'s 500 arcs in `(0, 1/2]` holds an isolation, in all 1,000** (500,000 of 500,000). With E241 that is
  1,000,000 of 1,000,000 arcs over both `f = 6` populations.
- The block is clear at `τ_C` in 180.
- The winner's index `j` runs to 26, carried by the fastest readings (rank 6; up to 7 at rank 5). The winner's lap is
  short when the block is spread.
- The block's relay from `τ_C` took at most 0.737 laps of `x₁`, a record. The arc is at least 27/4 laps.

**Consequence (M7).** Nothing in the wider population differs from E235 and E241 at `f = 6`. The case "the block's relay
from the bound lands in `c`'s first arc" holds on all 2,000 configurations read. Whether it can fail comes down to one
object of the six-block: its longest blocked stretch, i.e. the longest run of instants with no joint clear point,
measured in laps of `x₁`.
- If every six-block's longest blocked stretch is shorter than 27/4 laps of `x₁`, every arc of `c` holds an isolation.
- If some six-block has a longer one, a configuration can be built that puts `c`'s first arc inside it.

That is what step 2 constructs (E244).

## E244 — 2026-10-01 — design: construct six-blocks with long blocked stretches and place `c`'s arc inside one (step 2)

**Owner:** *"Yes start with step 1 and then 2"*; earlier, *"we can now construct rather than search to be able to look
for the mechanisim"*.

**Map:** v3 §4 Q8; the hole `ArrBlockRule8 6 9`, E243's consequence. M2 class (d), a construction.

**The object.** For a six-block, its blocked stretches are the maximal open runs of instants with no joint clear point
(at `1/8`), between consecutive clear intervals. Scaling a block by `g` divides every instant by `g`, so a blocked
stretch measured in laps of `x₁` depends only on the reduced block. Its start is the right end of a clear interval: an
entering edge of some block reading.

**Derived (E237's rule, at `f = 6`).** Put `c`'s first arc `[1/(8c), 7/(8c)]` so that it starts at the start of a
blocked stretch of length `G` (in time). Then the arc holds no isolation exactly when `G` exceeds the arc's length
`3/(4c)`. The hole requires `c ≤ x₁/9`, so the arc is at least 27/4 laps of `x₁`. The first arc can therefore fail only
for a block with a blocked stretch longer than 27/4 laps of `x₁`.

**Part A (exhaustive, exact).** Every reduced six-set `a₁ < … < a₆ ≤ 32` with `gcd = 1`. For each, the joint clear set
over one period `[0, 1]`, every blocked stretch (including the one through `0`), and the longest one `G`, as `G·a₁`
laps of `a₁`, with its start. Reported:
- the greatest `G·a₁` by height band of `a₆`, to see whether it grows with height, since a quantity found exhaustively to a
  height has drifted with height before;
- the 20 largest, with their sets and starts.

**Part A′ (after reading Part A).** The shapes at the top of Part A are built at larger readings, by construction rather
than search. It is designed once Part A is read and logged.

**Part B (placing).** For each top set, the arc start is put on the stretch's start:
- `c = g/(8(s₀ + n))`, with `n` the least whole number for which `c ≤ g·a₁/9`;
- the set is scaled to whole numbers, and checked against the proved rules (it must be in the hole);
- the cascade is run (C1), and the isolation record is taken for `c`'s arcs.

Read: where the cascade lands, and whether the first arc holds. Every configuration whose first arc holds none is read
move by move.

**Checks.**
- Part A: the clear set of each set is computed twice, by `clear_set` and by direct evaluation at both ends of every
  clear interval. Every left end must be an exit and every right end an entering edge.
- Part B: C1, F1, F2, I1–I3.

## E245 — 2026-10-01 — Part A read; E244's placement condition corrected: the first arc is `[s, 7s]`

**Map:** v3 §4 Q8; E244 Part A. Script `LonelyRunner/experiments/nN/redo/six_gap_v1.{py,out}`.

**Part A (exhaustive, all 897,973 reduced six-sets `≤ 32`; check 0 failures).**
- The longest blocked stretch, in laps of `a₁`, is carried by consecutive blocks `{a, …, a + 5}`. By height band of `a₆`
  its greatest value is 1.30, 1.68, 2.10, 2.84, 3.01, 3.12 and 4.04 (at `(27, …, 32)`). It grows with height: one
  stretch runs from about `0.12` to `0.25` of the period, so its length in laps of `a₁` is roughly `a/10`.
- **The derivation for this shape:** six readings in arithmetic progression with step `τ` (one apart, in reduced time)
  sit at `aτ + iτ`. When `3/20 < τ < 1/4`, each step is below 1/4 and the six span more than 3/4, so every placement puts
  one of them inside the open bad arc of width 1/4. No joint clear point exists there.
  `[derived; agrees with the stretch starts in the .out]`
- In laps of `a₁`, this stretch passes 27/4 for `a` above about 60.

**Correction to E244 (not caught at design time).** E244's derived condition ("the first arc can fail only for a block
with a blocked stretch longer than 27/4 laps") is necessary, but it is not the condition.
- `c`'s first arc is `[s, 7s]` with `s = 1/(8c)`; its length is fixed by its start. The hole gives `s ≥ 9/(8x₁)`.
- So the first arc holds no isolation **exactly when the block is blocked on all of `[s, 7s]`** for some
  `s ≥ 9/(8x₁)`: a blocked stretch `(s₀, s₀ + G)` with `s₀ + G > 7·max(s₀, 9/(8x₁))`, taken just past `s₀`.
- In reduced time the block's pattern has period 1. In a later period `k ≥ 1` a stretch spans a ratio of at most
  `(k + 1)/k ≤ 2`, so only the first period can matter.
- The consecutive blocks' long stretch spans a ratio of about 2 (0.12 to 0.25). It cannot hold a first arc. Part A's
  object measures a necessary condition only.

**Part A″ (run next; it replaces Part B's placement condition).** For every reduced six-set `≤ 32`, compute
`Q = max (s₀ + G)/max(s₀, 9/(8a₁))` over its blocked stretches in the first period. The first arc can hold no isolation
for some `c` exactly when `Q > 7`.
- This is a refutation search for the case "the block's relay from `1/(8c)` lands in `c`'s first arc". It is a truth
  check of a candidate case, not a statement.
- Reported: the greatest `Q` by height band, and the 20 largest with their stretches. Any set with `Q > 7` is placed in
  the hole (Part B) and read move by move.

## E246 — 2026-10-01 — step 2 read: no six-block can hold `c`'s first arc; the `f = 6` case reduced to one early range

**Map:** v3 §4 Q8; E245 Part A″ and E244 Part A′. Scripts `LonelyRunner/experiments/nN/redo/six_gap_v2.{py,out}` and
`six_gap_v3.{py,out}`.

**Checks: 0 failures** (every clear interval's ends are clear; left ends are exits, right ends entering edges).

**Part A″ (exhaustive, 897,973 reduced six-sets `≤ 32`).** No set has `Q > 7`. `Q` is the largest span
`(s₀ + G)/max(s₀, 9/(8a₁))` of a blocked stretch.
- Greatest `Q` by height band of `a₆`: 1.61, 1.94, 2.54, 3.05, 2.63, 2.71, 2.92; the overall greatest is 3.05 at
  `(14, …, 19)`.
- `Q < 2` for 897,546 of the sets, 2 to 3 for 426, and above 3 for 1.

**Part A′ (constructed, not searched).** The five shapes at the top of Part A″ were built for `a = 10 … 300`:
- `AP1` `{a, …, a + 5}`;
- `AP2` (step 2);
- `AP2′` `{a, a + 2, …, a + 8, a + 11}`;
- `TC` `{a, a + 2, a + 3, a + 5, 2a + 2, 2a + 3}`;
- `CL4` `{a, a + 1, a + 2, a + 3, 2a + 3, 3a − 2}`.

In every family `Q` falls with height:
- `AP1` goes to 1.71 at `a = 300`, consistent with E245's limit 5/3.
- `TC` and `CL4` go to about 1.21–1.23.
- The greatest anywhere is 3.33 (`AP2′` at `a = 28`). `Q > 7` at no `a` in any family.

**Derived: the `f = 6` case needs only the start of the block's first period** `[derived from lonely_seven_nat and
periodicity; not in Lean]`.
- The six block readings are whole numbers, `x_i = g·a_i` with `g = gcd`. In real time their clear set has period `1/g`.
  It is non-empty in every period: `lonely_seven_nat` gives an instant at which the six are clear at `1/7`, hence at
  `1/8`, and periodicity carries it to every period.
- So any interval of length at least `1/g` holds a block-clear instant. `c`'s first arc has length `3/(4c)`.
- **If `g ≥ 4c/3`, the first arc holds an isolation**, and that configuration of `ArrBlockRule8 6 9` is closed. This is
  `BlockSplit8`'s idea at `f = 6` with the constant `4/3` in place of 28.
- What remains is `c > 3g/4`, i.e. arc starts `s = 1/(8c) < 1/(6g)`: in reduced time, `s ∈ [9/(8a₁), 1/6)`. That range
  is empty unless `a₁ ≥ 7`.

**The `f = 6` case, stated (v20 §0 form).**
- Condition: the configuration is in `ArrBlockRule8 6 9`.
- Instant: the block's relay landing from `c`'s exit `1/(8c)`, which lies in `c`'s first arc.
- It is proved when `g ≥ 4c/3` (above).
- It is open on `c > 3g/4`, where it is the statement W6(7): *six whole-number readings have a joint clear instant in
  every `[s, 7s]` with `9/(8x₁) ≤ s < 1/(6g)`*. W6(7) is scale-free; it names the window by `c`'s own arc, not by a
  chosen constant.
- **Evidence (records, not proof):** exhaustive to 32 and constructed to 300, the largest span a blocked stretch reaches
  is 3.33 against the 7 needed. Over 2,000 configurations of the hole, every one of `c`'s arcs held an isolation.

**Import check.** Place: the block's relay landing from `c`'s exit, an instant. The window `[s, 7s]` is `c`'s first arc
(an object of the hole), not an `R`-window. Rewritten in `u = c·t`, it is `u ∈ [1/8, 7/8]` for `c`. That is `c`'s
own first window, and in this hole `c` is `d_min`, so it is register item 15's object. Item 15 is **misplaced as a
requirement**. Here it is the cascade's own landing stretch at `f = 6` (E243: 2,000 of 2,000), proposed as the case's
place, for the owner to rule on. `Q` is a refutation statistic for that case, not a statement.

**Consequence (M7).**
- Step 2 found no construction that defeats the `f = 6` case, and it narrowed the open content to W6(7) on the early
  range `[9/(8x₁), 1/(6g))`.
- The margin in the data is a factor of about 2 (3.33 against 7).
- Step 3 (the native reason) has two leads from this run:
  - the AP derivation, where the blocked range is `(3/20, 1/4)` per unit step, span 5/3;
  - the free-phase reduction of compact blocks (`SyncBlockN`'s open `N`-free question, `OneFreeN`).
- **Owner ruling needed:** whether `c`'s first arc may be the case's place, since in `u` it is item 15's object.

## E247 — 2026-10-01 — design: step 3, the native reason for W6(7); phase 3a, the record's mechanisms inside `c`'s first arc

**Owner:** *"Yes"* to step 3: the native reason for W6(7), before any Lean, from two leads (the progression derivation,
and the free-phase view of compact blocks).

**Map:** v3 §4 Q8; the `f = 6` case of E246. Record first, read before designing: `SyncBlockN` (`sync_block`, the free
common phase), `SyncPeriodN` (`block_clear_at_period`), `SyncGridN` (`lonely_of_sync_grid`), `SplitChainN`
(`lonely_of_split`), `FastPairEightN` (`pair_window`), and `OneFreeN` (`exists_clear_step`). What they need:
- **`sync_block`** holds for any block `{N + e}` and any start `t₀`. If the offsets `{e·t₀}` leave a point `y` at distance
  at least `1/8 + Emax/N` from every offset, the named instant `t₀ + fract(−y − N·t₀)/N` clears the block. The margin can
  be met only if `Emax/N < 3/8`: a tight block.
- **Nested windows** need each faster reading's need to fit in the slower one's clear arc: a separated block. Inside
  `c`'s first arc this is `lonely_of_split` with core `{c}` at `θ = 1/2`, which E242's exclusions already applied. Every
  configuration read here fails it.

**Phase 3a: name each `f = 6` landing by a mechanism already in the record, inside `c`'s first arc.** Populations: E235's
`f = 6` (1,000) and E243's (1,000). Mechanisms, each naming an instant whose loneliness is checked exactly:
- K0: the block is clear at `c`'s exit `1/(8c)` (evaluation).
- K1: `sync_block` with carrier `N = x₁` and offsets `x_i − x₁`, at a named start `t₀`: `c`'s exit, or a point `k/q`
  (`q ≤ 12`) with `[t₀, t₀ + 1/x₁]` inside the arc. `y` is the middle of the offsets' widest gap at `t₀`.
- K2: as K1 with the carrier the block reading that makes `max|x_i − N|/N` least, and signed offsets. `sync_block` is
  stated for `e ≥ 0`; signed offsets are its direct extension, marked `[derived]`.

**Read.** The configurations no mechanism reaches are listed with their consecutive ratios and spread, and their shape
is read before anything is stated (M3).

**Phase 3b (after 3a is read):** derive the mechanism the unreached configurations need, starting from the two leads,
then check it by construction and perturbation.

**Checks.**
- Each named instant lies in `c`'s first arc, and the full set is lonely there (exact).
- Every configuration where K1 or K2's hypothesis holds is clear at the named instant. A failure would be a fault in
  the check, since `sync_block` is proved.

## E248 — 2026-10-01 — phase 3a read: the record's mechanisms reach no `f = 6` configuration beyond the trivial case

**Map:** v3 §4 Q8; E247 run as designed. Script `LonelyRunner/experiments/nN/redo/hole6_mech_v1.{py,out}`.

**Checks: 0 failures.** No mechanism's hypothesis held without the full set being lonely at its named instant.

| population | K0 (block clear at `c`'s exit) | K1 / K2 (`sync_block`, two carriers) | not reached |
|---|---|---|---|
| E235 `f = 6` (ratios below 2) | 191 | 0 | 809 |
| E243 `f = 6` (some ratio 2 to 9) | 180 | 0 | 820 |

- **Why `sync_block` never fires here.** Its margin `1/8 + Emax/N` must be met by a point between six offsets, which needs
  `Emax/N` well below `3/8`. Over the unreached configurations, the best carrier's `max|x_i − N|/N` is:
  - E235: 0.2 to 0.3 in 1, 0.3 to 0.4 in 2, 0.4 to 0.5 in 12, 0.5 and above in 794;
  - E243: 0.6 and above in all 820.
- **Nested windows** inside the arc (core `{c}` at `θ = 1/2`) were excluded by construction (E242).
- So the record's proved mechanisms sit at the two ends:
  - *tight blocks* (free phase: `sync_block`, period points, sevenths);
  - *separated blocks* (nested windows, `pair_window`).

  The `f = 6` hole's blocks lie between them. This is the record's own owed item, "bounded shapes by window constants"
  (E30; E231). `WindowConstantFive`, its order-five form, is registered OWED.

**The two leads, read against this.**
- The progression derivation (E245: span 5/3) assumes a free fast phase, which is the tight regime.
- The free-phase view is `sync_block` itself.
- Neither reaches the hole's blocks as sampled. Both remain correct where they apply.

**What the cascade does instead (E239, E243).** It lands at the least clear flank opening after `c`'s exit: a block
reading `h`'s exit at which the other five block readings are all clear. In the record's terms (v21 §6.9–6.11), that is a
flank whose five walkers clear at some opening inside `c`'s first arc. The arc is a run of at least `(27/4)·(x_h/x₁)`
openings of flank `h`. The record proves one walker (Theorem 6.9) and two walkers by run length (Theorem 6.18, with the
`1/2` shadowing family as the exception). It has measured three walkers (§6.11: 1,432 shadowing of 496,128). It has
nothing for five.

**Consequence (M7).**
- The native reason for W6(7) is not in the record's sync or nesting tools. It is the flank question: within `c`'s first
  arc, some flank of the six-block has an opening where its five walkers are all clear (no block shadows all six of its
  flanks across the arc).
- **Phase 3b, proposed:** read each `f = 6` landing in flank terms: the winning flank, its index from `c`'s exit, the five
  walkers' steps there, and which of the six flanks have a clear opening inside the arc at all. Then derive from what
  every configuration shares.

## E249 — 2026-10-01 — design: phase 3b, the `f = 6` landings in flank terms, and the nested actual stretches

**Owner:** *"ok"* to phase 3b.

**Map:** v3 §4 Q8; E248's consequence. M2 class (d), a map run. Record: v21 §6.9–6.11 (flanks, walkers, Theorem 6.9,
Theorem 6.18); `SplitChainN` (nested windows: `stretch`, `needT`).

**Population.** The 1,629 `f = 6` configurations of E235 and E243 that K0 does not settle.

**Read, per configuration, inside `c`'s first arc `[1/(8c), 7/(8c)]`.**
1. **The six flanks.** For each block reading `h`, its openings `(8K + 1)/(8h)` inside the arc (their number `L_h`). At
   each opening the five other block readings are walkers at `x_j(8K + 1)/h` mod 8, and `c` is clear (inside its arc).
   Recorded per flank: the index of its first clear opening (from the arc's first opening of that flank), or *shadowed*
   (no clear opening in the arc), and its number of clear openings.
2. **The winner.** The earliest clear flank opening over the six. At the winner, the five walkers' fractional ratios
   `f_j = frac(x_j/h)`, their steps `ĝ_j = min(f_j, 1 − f_j)` (§6.11), and their positions.
3. **Nested actual stretches.** For `k = 0 … 5`, `C_k` is the joint clear set of `c, x₁, …, x_k` inside the arc
   (`C_0` = the arc), with its longest stretch `λ_k`. Derived: an interval longer than `1/(4x_{k+1})` holds an instant at
   which `x_{k+1}` is clear (its blocked runs are that long). Recorded: `4x_{k+1}λ_k` at each level, and every
   configuration where it drops below 1 at some level.

**Checks (forced):**
- the winner equals the cascade's landing (A.9 and Corollary 6.24);
- the full set is lonely at the winner and at every recorded clear opening (exact).

**After the run:** what every configuration shares (if anything), then every configuration that differs, read (M3)
before anything is stated. Lengths `λ_k` are lengths of named clear stretches (places), not measures of sets.

## E250 — 2026-10-01 — phase 3b read: every level of the nested actual stretches holds with a margin of at least 2.18

**Map:** v3 §4 Q8; E249 run as designed. Script `LonelyRunner/experiments/nN/redo/hole6_flank_v1.{py,out}`.

**Checks: 0 failures.** The winner equals the cascade's landing in all 1,629. The full set is lonely at every first
clear opening recorded.

**1. Flanks.**

| population | flanks with a clear opening in `c`'s first arc: 6 / 5 / 4 / 3 | shadowed flanks by rank 1…6 |
|---|---|---|
| E235 (809) | 764 / 44 / 1 / 0 | 11, 17, 6, 7, 3, 2 |
| E243 (820) | 778 / 40 / 1 / 1 | 16, 18, 5, 4, 1, 1 |

- The winner is at index 0 of its flank in 649 of 809 and 608 of 820. Larger indices belong to the fastest flanks, where
  the arc holds many openings.
- At the winner, the largest walker step `max ĝ` is below 1/2 in all but 3 configurations.

**2. Nested actual stretches.** Here `λ_k` is the longest stretch of the joint clear set of `c, x₁, …, x_k` inside the
arc. Least value over the configurations of `4x_{k+1}λ_k` (this is above 1 exactly when `x_{k+1}` is clear somewhere in
that stretch):

| level `k` | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|---|
| E235 | 27.41 | 3.0028 | 2.532 | 2.204 | 2.258 | 2.181 |
| E243 | 27.12 | 3.0005 | 2.695 | 2.879 | 2.676 | 2.873 |

Below 1 at no level in any configuration.
- **Level 0, derived.** `λ₀` is the arc, `3/(4c)`, so `4x₁λ₀ = 3x₁/c ≥ 27`.
- **Level 1, derived.** The arc is at least 27/4 laps of `x₁`, so it holds a full clear arc of `x₁`, `λ₁ = 3/(4x₁)`, and
  `4x₂λ₁ = 3x₂/x₁ > 3`. The data's least values (3.0028, 3.0005) are `3x₂/x₁` at the tightest pairs.
- **Levels 2–5: records, not derived.** The least margins are 2.18 to 2.88.

**What every configuration shares.** At every level the next block reading has room in some actual stretch, with a
margin of at least 2.18 in this data. Nested windows fails on these blocks because it assumes the worst placement in a
single stretch, losing a factor 2 per level. The actual stretches do not lose it. Inside `c`'s first arc each level has
many stretches, roughly one per lap of the slower readings, and the next reading's blocked runs drift against them from
lap to lap. So some stretch receives a favourable placement.

**Import check.** Places: each stretch is named by its certificate ends, and the next reading's clear instant inside it
is named (its exit, or the stretch's start). The margins are records. A uniform constant would be a window constant, and
none is stated.

**Consequence (M7).** The native reason for W6(7) points to a **drift lemma**, one per level.
- Inside `c`'s first arc, the readings `c, x₁, …, x_k` have, among their many clear stretches, one longer than
  `1/(4x_{k+1})`. The data has twice that.
- The mechanism is the next reading's blocked run walking across the lower level's stretches from lap to lap. That is the
  walker framework of v21 §6.11 (Theorem 6.18 is its two-walker form), applied to stretches in place of openings.
- **Proposed phase 3c:** derive level 2 (`c`, `x₁`, `x₂`, against `x₃`) as a drift statement across `x₁`'s at least six clear
  arcs inside `c`'s arc. That is a statement about two readings, inside the proved two-walker framework. Check it exactly,
  then see whether the argument lifts level by level.

## E251 — 2026-10-01 — owner's check: is phase 3c's object native? The drift lemma is not; excised and replaced

**Owner:** *"Ok, please check that we are searching for a native object and it is not just a similar shaped object as
other frames pretending to be helpful"*.

**Map:** v3 §4 Q8; E248–E250. The memories' tests, run on the proposed phase 3c object and on what led to it:
- the place test and the interval check (`feedback_n8_cascade_is_the_oracle`);
- the pre-use check, steps 0–3 (`feedback_n8_no_prereg_no_imports`);
- the register (`OBJECT_REGISTER_v3.md`).

**The object tested.** E250's drift lemma: *inside `c`'s first arc, the joint clear set of `c, x₁, …, x_k` has a stretch
longer than `1/(4x_{k+1})`, because the next reading's blocked runs drift across the lower level's stretches from lap to
lap.*

**Results.**
1. **Place test: fails.** Delete the interval clause and nothing constructs an instant. "Some stretch is longer than `L`"
   names no place; the instant inside the stretch is not determined.
2. **Register: two items.** "`x_{k+1}`'s blocked runs do not cover `C_k`" is item 4 (covering). "`C_{k+1}` is non-empty" is
   item 8 (set emptiness). The stretch-length comparison is the mechanism by which non-covering is shown.
3. **Pre-use check, step 0 (our own record): the route is already on disk, and classified.** E59 (log l.2046–2052): *"The
   block law becomes a bound on how many consecutive clear bands of the slowest runner … the other five can cover
   without a gap … Covering `k` consecutive bands needs that relation to persist for `k` laps. Its drift rate is set by
   the speed differences."* E61 (l.2094–2108) tested the drift condition and found it held in 0 cases. The oracle memory
   lists *"Proxies over stretches of blocked time (windows, `Q(F)`, block laws, bands …)"* as imported shapes (v4 §4
   item 1). The drift lemma is that route again, under new names: "nested actual stretches", "drift lemma".
4. **Pre-use check, step 1 (trace): fails.** The need for "a stretch longer than the next blocked run" traces to my own
   E249 design. That design took its shape from `SplitChainN`'s nested windows, which is the classical nested-intervals
   argument for fast-growing speeds. It does not trace to a framework step. The cascade does not form stretches; it moves
   from opening to opening (A.1).
5. **Related objects carried with it, reclassified:**
   - E244–E246's *longest blocked stretch* and `Q` (the span of a blocked stretch) are blocked-time proxies, the `Q(F)`
     family. Their use there was as refutation statistics for a place-naming case, a truth check, which the memory allows.
     They are **not** evidence for a mechanism, and E246's "margin of about 2" is withdrawn as such.
   - W6(7) is window-shaped; E246 already flagged it as a cap. The owner's ruling on `c`'s first arc stays open.
   - E249/E250's *nested actual stretches* (part 3, the `λ_k` table) are kept as data, read as a covering measurement,
     and are not a mechanism.

**What passes.**
- **The case's place.** The block's relay landing from `c`'s exit: the least clear block-flank opening `(8K + 1)/(8h)`
  after it (E239; v21 §6.10's sort and scan). At that candidate scale `h/(8K + 1)`, every block reading satisfies the
  clearance criterion `h ≤ x_j(8K + 1) mod 8h ≤ 7h` (Theorem 6.19), and `c`'s reading `c(8K + 1)/h` lies in the band
  `[1, 7]` (Corollary 6.21). Every object here is native: flank, opening, reading, band.
- **E249/E250 parts 1–2** (the flank reading: winners, indices, walkers' steps, shadowed flanks) are native objects
  (v21 §6.9–6.11).

**Excision table** (memory: *"An import found is excised and replaced, not labelled"*):

| import | excised from | replaced by |
|---|---|---|
| the drift lemma (nested actual stretches; non-covering by drift across laps) | E250's Consequence as phase 3c's target; the plan | the flank statement below |
| `Q` and the longest blocked stretch as evidence for a mechanism | E246's Consequence ("margin of about 2") | refutation statistic only (truth check of the case) |

**Phase 3c, replaced (proposed).** The native object is the flank. At a block flank `h`, the openings inside `c`'s band
run are those where `c` reads in `[1, 7]`. There `c` is a slow walker with step `8c/h` per opening, and the five other
block readings are walkers with steps `ĝ_j` (§6.11). The case needs one opening where all five read in the band. The
record's native tools for this are:
- Theorem 6.9 (one walker clears);
- Theorem 6.18 (two walkers, by run length, with the `1/2` shadowing family as the exception);
- §6.11's case table (lattice, cross-lattice, run length, common lattice).

Phase 3c should read, at each configuration's winning flank, which walkers sit near the band's edge at the openings
before the winner and what brings each into the band at the winner. That is per walker and per opening, with no
stretches and no lengths.

**Flagged for the owner, not excised.** `SplitChainN` (nested windows) is proved, has been in the record since E30, and was
used in E231 and as an exclusion since. Its statements conclude loneliness, and the windows are tools inside. Its shape is
the classical nested-intervals method. Whether it is native is the owner's call. Under the memory's rule, nothing proved
is excised on the session's own reading.

## E252 — 2026-10-01 — phase 3c designed on the flank object, reasoned from the record first; E246's piece is E60

**Owner:** *"Yes please and please try to reason and think it through, any time you do not we just end up with another
attempted import"*.

**Map:** v3 §4 Q8; E251's replacement for phase 3c. Read first: v21 §6.9 in full (Theorems 6.8, 6.9, 6.12–6.14, the U/K
calculus, the shadowing computations), §6.11 (Theorem 6.18), `Cascade/Flanks.lean` (`class_killer_int`,
`circDist_periodic_of_lattice`, `lonely_of_flank_unkillable`, `lonely_of_some_flank_unkillable`), and E60.

**The reasoning, step by step, in the framework's objects.**

**R1 — the case at a flank** `[derived from Theorems 6.12–6.14]`.
- At block flank `e`, opening `k` (`u = 8k + 1`), reading `d` reads `d·u/e` and is clear iff `d·u mod 8e ∈ [e, 7e]`.
- `c` reads `c·u/e`. It is in its first band `[1, 7]` exactly for `u ∈ [e/c, 7e/c]`; call that `c`'s **band run** at `e`.
- The `f = 6` case (the cascade's place) is: some block flank `e` has an opening in `c`'s band run at which the five
  other block readings are clear. For whole numbers, the block's clear openings at `e`, `U_e`, repeat with period `e`
  (Theorem 6.13).

**R2 — `c` as the free difference** `[derived; it is E60's lonely_of_off_lattice]`.
- The six block readings are whole, so they are lonely by native order 7, and some block flank `e` has `U_e` non-empty
  (Theorem 6.8 applied to the six).
- With `g = gcd(block)`, the clear openings repeat with period `P = e/g`. If `g ∤ c`, then `c` is off that lattice.
  `class_killer_int` forbids it from being in the way at every opening of a clear class, so `lonely_of_flank_unkillable`
  gives an isolation. The index is bounded: `c` advances `frac(c/g) ≥ 1/g` per step and, by Theorem 6.18's bad-run
  bound, is in the way for at most about `g/4` consecutive steps.
- **This is E60**, proved in Lean and axiom-clean, which I had not read before deriving it. It closes every set with a
  reading not divisible by the gcd of the others. What it leaves is **every six readings coprime** (2,811 of 3,000
  random reduced sets in E60).
- **Correction to E246:** its derived piece (closed when `g ≥ 4c/3`) is contained in E60. Since `g ≥ 4c/3 > c`, `g`
  cannot divide `c`. It adds nothing, and is withdrawn as a separate result.

**R3 — in the generic class the calculus has no further leverage** `[derived]`. When every six readings are coprime, `c`
is on the lattice at every block flank (`P = e`), and its verdict is constant along each residue class `r + je`. The
case at flank `e` is then the finite residue question itself: some `k` in `U_e` with `c·u` in `c`'s band.

**R4 — `c` is a slow walker at every block flank** `[derived from Theorem 6.18's bad-run bound]`.
- `ĝ_c = c/e ≤ 1/9`.
- `c` is in the way for at most `e/(4c)` consecutive openings, and its band run at `e` has at least `(3/4)(e/c) − 1`
  openings, at least 5.75 at `e = x₁` and more at faster flanks.
- So `c` never blocks inside its band run. A flank fails across the run only if **the five block walkers shadow every
  opening of the run**.

**R5 — what the record knows about shadowing.**
- Every shadowing configuration found exhaustively has `max ĝ ≥ 1/3` (§6.11; register item 30).
- The pairs that shadow are the half-integer family (both fractional parts `1/2`).
- Shadowing triples with small denominators: `(2,4,4)`, `(3,3,3)`, `(3,6,6)`, `(5,5,5)`.
- §6.9: shadowing at flanks comes from walkers sharing small denominators ("wide (4–6 runners sharing one small
  denominator)").
- In the hole, walkers' ratios `x_j/e` usually have large denominators.

**Where this leaves the native question.** The `f = 6` case fails only if every block flank is shadowed by its five
block walkers across `c`'s band run. That is shadowing over a finite run of openings, and the record's shadowing
knowledge is about all openings.

**Phase 3c (map run, design).** Population: the 1,629 configurations of E248 not settled by K0, with E60's condition
recorded first. Any configuration with a reading not divisible by the gcd of the others is closed by
`lonely_of_off_lattice` and is set aside.

Read at each block flank `e`, inside `c`'s band run (openings only):
- the flank's first opening at which every block walker is clear (its index in the run), or *shadowed across the run*;
- for every opening of the run before it, the walkers in the way: by name, reading mod 8, and their ratio's reduced
  denominator `q` relative to `e` and `ĝ`;
- for each flank shadowed across the run, the walkers that do the shadowing, opening by opening, with `(q, ĝ)`. These are
  to be compared with the record's shadowing configurations (small shared denominators, `max ĝ ≥ 1/3`).

**Checks (forced):**
- inside the run `c` is never in the way (R4);
- the earliest first-clear opening over the flanks is the cascade's landing (A.9);
- the full set is lonely there (exact).

**Not read:** stretches, lengths of anything, windows, shares or counts as rates.

**Question this phase answers:** whether shadowing across the run, at the flanks where it happens, has the record's
known shadowing structure (shared small denominators, a fast walker). If it does, the native route to the `f = 6` case is
the shadowing analysis of §6.9–6.11 restricted to a run, and the next step is a derivation there. If it does not, the
reading names the structure that does.

## E253 — 2026-10-01 — phase 3c read: shadowing across `c`'s band run is a near-sharer (62 of 83) or a hand-off (21)

**Map:** v3 §4 Q8; E252 run as designed. Scripts `LonelyRunner/experiments/nN/redo/hole6_shadow_v1.{py,out}` and
`hole6_shadow_v2.{py,out}`.

**Checks: 0 failures.**
- `c` is never in the way inside its band run (R4).
- The earliest first-clear opening over the block flanks is the cascade's landing in every configuration, and the full
  set is lonely there.

**E60 first.** `lonely_of_off_lattice` closes 90 (E235) and 105 (E243) configurations, almost all through `h = 2`: one
block reading is odd and the other six, `c = 1000` included, are even. This is partly an artefact of the sampling:
`c = 1000` in every configuration. Left in the generic class: 719 and 715.

**Shadowing in the generic class.**
- Block flanks shadowed across `c`'s band run, per configuration: none in 676 and 677; one in 42 and 37; two in 1 and 1.
  **Never more than two of the six.**
- At openings blocked before a flank's first clear one, the walkers in the way have reduced denominators `q > 1000` in
  21,618 of 21,865 and 25,495 of 25,706, and `q ≤ 16` in 6 in all. **The record's shadowing structure (shared small
  denominators, §6.9–6.11) does not appear.**
- **Shadowed flanks, read one by one (83):**
  - **62 are shadowed by one walker alone**, in the way at every opening of the run.
    - In every one, the walker's ratio to the flank is `x_j/e = A + ε` with `A` whole and `|x_j − A·e| < 0.3c`.
    - Since `u = 8k + 1 ≡ 1 (mod 8)`, it reads `A + εu` (mod 8): it barely moves.
    - It stays within 1 of a multiple of 8 across the run with `A ≡ 1, ε < 0` (50: just below its leaving edge; `A = 1`
      in 45, a near twin just slower than the flank), `A ≡ 7, ε > 0` (6), or `A ≡ 0` (6).
    - The derived condition ("`A + εu` within 1 of a multiple of 8 for every `u` in the run") agrees with exact coverage
      for every walker of every shadowed flank: 0 disagreements.
    - This is the **near form of the record's dead flank** (an exact slot-sharer, `8 ∣ A`, Theorem 6.8) and of the
      sharer's flank (§6.9). Call it a **near-sharer**.
  - **21 are hand-offs:** several walkers, each in the way at part of the run, none at all of it (listed in the `.out`).

**Derived, and conditional.** Suppose a flank could be shadowed across the run only by a near-sharer. Then the six
flanks could not all be shadowed at once.
- The fastest flank's near-sharer must be a near twin just below it (`A = 1`), since no block reading is faster.
- That twin's own flank needs a near-sharer: another twin below it, or a reading near `A ≥ 7` times it. The chain of
  twins stays within `2c` of the fastest reading, so no reading is 7 times any member of it.
- So the chain's lowest member has a free flank.

The hypothesis fails in 21 cases (the hand-offs), so this is **not** a proof. It names the two structures a proof has to
handle: near-sharers, which the chain argument handles, and hand-offs, which it does not.

**Answer to E252's question.** Shadowing across a run does not have the record's small-denominator structure. It has
the near-sharer structure in 62 of 83 cases and a hand-off structure in the rest.

## E254 — 2026-10-01 — design: do the lower orders' template (v21 §17C) and E60 reach the hole configurations?

**Owner:** *"Let me ask this. All n=3 to 7 were reproved via the framework. Does that not suggest how we could achieve
n=8 without importing other frameworks. We have an overarching frame work that can reprove the others so I feel like
that should assist us in this step of proof we are in? I mean the cascade will work in all those other proofs too."*

**Map:** v3 §4 Q8 and v21 §17. Record first (read): §17A and §17C.
- Orders 3–7 were proved natively in §0's form: a finite case list, each case ending at a named residue-band
  certificate. At order 7 that is `t = K/(7P)` with every `d·K mod 7P` in `[P, 6P]`, Barajas–Serra's prime filtering as
  `unit_filtering` over the units mod 7, with descent by 7 and by 2.
- The template is already carried to order 8 in `OrderEightCasesN` (§17C, `[PROVED]`), *"`OrderSixN` one order up"*:
  `lonely_eight_or_residual` (every whole-number set is lonely or in `EightResidual`).
- E60 (`lonely_of_off_lattice`, 2026-09-26) came after v21 and is not among `EightResidual`'s fields.

The hole route (`Order8SkeletonN`'s five holes, which we have been mapping) and the residual route (§17C) are two case
lists for the same target. Neither has been run on the other's configurations.

**Run.** For every hole configuration read so far, as a whole-number set of seven disparities:
- populations: E233's `f = 3` (2,000); E235's `f = 4, 5, 6` (1,000 each); E243's wide `f = 6` (1,000);
- record the first §17C rule whose condition holds, in `EightResidual`'s field order (common factor, R6 at
  `q = 5, 6, 7, 8`, R1, descent, free flank, R4, R8, first lap, the `−7` opening, rational opening, thirds, fifths,
  sixths, sevenths, ninths, small resolution `D ≤ 64`), and then E60;
- list the configurations in `EightResidual` that E60 does not close.

Field implementations are those of `experiments/nN/eight_residual_count_v5.py` and `v6.py`, copied, since those scripts run
on import.

**Checks.** At each case's named instant the full set is lonely (exact), for every rule whose instant is computed here:
small resolution `(8j + 1)/(8D)`, and the band certificates. A failure would be a fault in the copy.

**Caution recorded in advance.** `c = 1000` in every `f ≥ 4` configuration (E235's sampling), so R6 at `q = 5` and `q = 8`
cannot fire there (`5 | 1000`, `8 | 1000`), and E60's reach through `h = 2` is inflated. Which rule closes a
configuration is case bookkeeping for this sample, not a rate.

## E255 — 2026-10-01 — the lower orders' template already closes every hole configuration we mapped

**Map:** v3 §4 Q8 and v21 §17C; E254 run as designed. Script
`LonelyRunner/experiments/nN/redo/hole_residual_v1.{py,out}`.

**Checks: 0 failures.** Where small resolution fired, the full set is lonely at `(8j + 1)/(8D)`.

**Result.** Every configuration is closed by a §17C rule, all of them proved in `OrderEightCasesN` and axiom-clean.
**None is in `EightResidual`**, so E60 was never reached.

| population | first §17C rule that holds (count) |
|---|---|
| `f = 3` (2,000) | free flank 675, R6 `q = 6` 652, R6 `q = 7` 515, `−7` opening 58, common factor 30, rational opening 27, descent 21, fifths 10, thirds 10, sixths/sevenths/ninths 2 |
| `f = 4` (1,000) | R6 `q = 6` 353, free flank 279, R6 `q = 7` 272, `−7` opening 33, rational opening 18, thirds 12, common factor 11, descent 10, fifths 9, sixths/… 3 |
| `f = 5` (1,000) | R6 `q = 6` 324, free flank 283, R6 `q = 7` 250, `−7` opening 40, thirds 34, rational opening 31, fifths 14, common factor 9, descent 8, sixths/… 7 |
| `f = 6` (1,000) | R6 `q = 6` 315, free flank 295, R6 `q = 7` 259, thirds 57, `−7` opening 27, common factor 16, fifths 14, sixths/… 11, descent 6 |
| `f = 6` wide (1,000) | R6 `q = 6` 364, free flank 274, R6 `q = 7` 253, thirds 40, `−7` opening 21, common factor 14, fifths 12, descent 11, sixths/… 10, small resolution `D = 2` 1 |

(Which rule fires first is bookkeeping for this sample, not a rate. E254 recorded the sampling bias in advance:
`c = 1000` makes R6 at 5 and 8 impossible and inflates E60.)

**What this means.**
1. **The hole route and the residual route meet, and the residual route is ahead.** E232–E253 mapped the cascade inside
   configurations that `lonely_eight_or_residual` already proves lonely, at named instants, by the lower orders' native
   template. Nothing in those entries is wrong; the map stands. But no sampled hole configuration is open.
2. **The open content of the holes is hole ∩ `EightResidual`.** Random sampling at large readings almost never reaches
   `EightResidual`. Its positive fields need every `q ∈ {5, 6, 7, 8}` to divide some disparity, spread above 7, the
   multiples-of-8 shapes `(1,6), (2,5), (3,4), (4,3)` (the last with a non-multiple `≡ 4 mod 8`), and then the failure of
   every certificate family. R6 at `q = 6` or `7` alone closed over half of every population.
3. **What the lower orders' template says the order-8 structure is.**
   - At order 7 the native proof's arithmetic was the units mod 7 (`unit_filtering`), with descent by 7 and by 2.
   - At order 8 the modulus is `8 = 2³`, `φ(8) = 4`, and §17C's fields are organised by the multiples of 8 (descent's
     cost, R4, the free flank).
   - **Phase 3c found the same object independently** (E253): what shadows a flank across a run is a near-sharer,
     ratio near `A` with `A ≡ 0` or `±1 (mod 8)`. That is a near-collision, the near form of a reading `≡ 0 (mod 8)`
     relative to the flank (Theorem 6.27: an exact block is colliding).
4. The record's own open rule in these terms is `PROOF_REQUIREMENTS_v2` §7: *produce `(D, a)` when some difference is
   `≡ 0 (mod 8g)`* (the `L₀` ladder, verified on 31,066 runners, not proved).

**Consequence (M7).**
- Re-aim from the holes to `EightResidual`: the one open statement of §17C, already reduced from the conjecture by the
  lower orders' method, proved in Lean.
- The next map work belongs inside `EightResidual`, by construction (owner, E241): build members at larger readings, run
  the cascade, and read its landings in the sharer terms phase 3c found. The target is the order-8 counterpart of unit
  filtering: a residue-band certificate at a modulus read off the set's multiples-of-8 structure.
- Owner rulings still standing:
  - whether `EightResidual` is the obligation or a sufficient route (§17B);
  - whether first-lap clearance stays (§17C);
  - `c`'s first arc as a place (E246), now moot for the sampled holes.

## E256 — 2026-10-01 — the re-aim at `EightResidual` was done on 2026-09-27 (E117–E118); three routes meet at C1

**Owner:** *"Ok lets try it"* (E255's re-aim: build `EightResidual` members by construction, run the cascade, read the
landings in sharer terms).

**Map:** map v3 §9 C1; log E117–E121, E147–E148, E152–E157. **No run.** Read before designing (F7): the run approved
here already exists.

**What is on disk.**
- **E117** (`residual_members_v4/v5`): members of `EightResidual` with **all 22 fields**, Case B shape, built by
  construction (47 of 400). The largest reading is a multiple of `8·lcm(1…64)` (a collider at every lattice
  `D ≤ 64`); spread 7.1–8.9. The cascade relocates the isolation to a middle reading's second opening `9/(8e)` (44 of
  47), `R* ≤ 2.13`.
- **E118** (`residual_members_C_v1`): Case C members, all 22 fields, 297 of 300 constructions. Shape: **one slow runner
  below a six-reading cluster.** Through the cascade, all are isolated inside the slow runner's first window, with the
  flank a cluster member in 546 of 547.
- **E118 named the open statement C1:** *"the fast cluster's instants … meet the slow runner's first window"*, for a
  cluster of up to six with no common factor. Its proved cases are `FastPair8` and `BlockSplit8` (and `OneFreeEightN`,
  E147).
- **E147–E148** made C1 *"the mechanism of Case B as well as Case C"*.
- E152–E217 attempted it (regimes, coverings, the grid-class regime, `Cover8`, `WideStep8`, the band route).
- **The owner's own statement of the mechanism** (log l.4188–4191, quoted in the E115 context): *"It will be because there
  are two runners in the same slot, which just means it delays the isolation event because the runners need to separate
  from each other"*; *"It's the same mechanism over and over."* The record's l.4195 names it *"the one mechanism that
  delays the isolation"* (`EightResidual`'s `eight` field).

**Three routes meet at one statement.**
- The `f = 6` hole's case, W6(7) (E246), is C1 with a cluster of six.
- `EightResidual`'s constructed members are C1 configurations (E118).
- Cases B and C take C1 as their mechanism (E148).
- E255's re-aim therefore lands where E232–E253 already were. Building residual members again would repeat E117–E118.

**Correction to E255 and the reply that carried it.** "Whether `EightResidual` is the obligation or a sufficient route"
is **answered**, not pending. `lonelyRunnerAt8_iff_residual` proves it is the obligation (map v3 §9 C1; E212's note,
log l.7341). Only first-lap clearance stays pending among v21 §17G's rulings, plus E246's arc ruling.

**What today adds to C1, in native terms (E248–E253):**
- The record's sync and nesting tools do not reach C1's configurations (E248).
- E60 closes the off-lattice ones (E253).
- At the cluster's flanks inside the slow runner's band run, a flank is shadowed by a **near-sharer** (62 of 83: a
  cluster reading whose ratio to the flank is near a whole `A ≡ 0, ±1 (mod 8)`, so it barely moves) or by a
  **hand-off** (21 of 83). Never more than 2 of the 6 flanks are shadowed.
- The near-sharer is the owner's *"two runners in the same slot"* read at a flank. For near-sharers alone, the twin-chain
  argument (E253) shows not all six flanks can be shadowed.

**Consequence (M7).** The next step on C1 is the 21 hand-offs: read and perturb them through the cascade (E67's method)
to see whether a hand-off is a succession of same-slot pairs (the owner's mechanism, one pair after another) or something
else. If it is a succession, the twin-chain argument has a chance to extend to it.

## E257 — 2026-10-01 — design: the 21 hand-offs, read for persistence and perturbed through the cascade

**Owner:** *"yes"* to E256's next step.

**Map:** v3 §4 Q8; C1 (E118); E253's hand-offs. The method is E67's: *"use the cascade pertubate the speeds to find the
mechanisim"*.

**The question, sharpened before running.** E256 asked whether a hand-off is "a succession of same-slot pairs". As
stated that is empty: every walker in the way at a flank opening sits in the subject's slot, so every hand-off is a
succession of occupants. What the owner's mechanism adds is **persistence**: *"it delays the isolation event because the
runners need to separate from each other"*. A walker `x_j` at flank `e` reads `A + εu` (mod 8) at opening `u ≡ 1 (mod 8)`
(E253). It stays in the subject's slot for a block of about `1/(4|ε|)` consecutive openings, and then it has separated.
So the native question is:
- **Persistent succession:** the run splits into a few consecutive segments, each held by one walker throughout, and each
  of those walkers is a near-sharer over its segment (a pair separating, then the next pair); or
- **Flicker:** fast walkers (large `|ε|`) alternating opening by opening, with no persistent occupant.

**Part 1 (read).** For each of the 21 hand-offs (E253, `hole6_shadow_v2.out`), the least number `s` of consecutive
segments into which the run's openings split so that each segment has one walker in the way at every opening of it.
Greedy left to right is exact for this. Per segment: the walker's `(A, A mod 8, ε)`, the segment length in openings, and
`1/(4|ε|)`, its persistence.

**Part 2 (perturb, E67).** For each hand-off configuration, move each block reading by `±1, ±2`, one at a time. Per move:
- whether the flank is still shadowed across the run;
- if so, whether the shadow is now one walker or still a hand-off;
- where the cascade lands (inside `c`'s first arc, and which flank).

Read which reading's move frees the flank, and whether that reading is a segment's occupant.

**Checks (forced):** `c` is never in the way inside its run; the earliest first-clear flank opening is the cascade's
landing, and the set is lonely there.

**Not read:** shares, counts as rates, or lengths of time. Segments are counted in openings (places).

## E258 — 2026-10-01 — the hand-offs read: persistent near-sharers in succession, or alternation near half-integers

**Map:** v3 §4 Q8; C1; E257 run as designed. Scripts `LonelyRunner/experiments/nN/redo/hole6_handoff_v1.{py,out}` and
`hole6_handoff_v2.{py,out}` (with its matched null).

**Checks: 0 failures** (`c` never in the way inside its run; the landing is the earliest first-clear flank opening).

**Part 1, persistence.** Each hand-off was split into the least number `s` of consecutive segments of openings with one
walker in the way throughout each segment. `s` per hand-off: 2 in 5; 3 in 1; 4 in 3; 5 to 17 in 12.
- **The 5 with `s = 2` are the owner's mechanism twice in succession:** a persistent near-sharer, then another. Example,
  flank 35858: a near twin (`A = 1`, `ε = −0.010`) for 20 openings, then a near double (`A = 2`, `ε = −0.011`) for 7.
- **The others mix in alternation:** segments of 1–2 openings (119 in all) whose occupant does not persist. Example,
  flank 24413: walkers at ratios 1.480 and 3.502 alternate for 11 openings, then two near-sharers hold the remaining 8
  (`A = 9`, `ε = 0.055`; `A = 7`, `ε = −0.042`).
- Every segment is within its occupant's persistence `1/(4|ε|) + 1` (137 of 137). That is close to forced; recorded,
  not read as a finding.

**The alternating occupants against a matched null** (`hole6_handoff_v2.out`; exact Farey regions of order 8 for a
uniform fractional ratio). Nearest small-denominator fraction to `frac(x_j/e)`:

| nearest `q` | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| observed (119) | 0 | **36** | 13 | 11 | 9 | 8 | 32 | 10 |
| uniform expectation | 14.9 | **8.5** | 10.6 | 10.2 | 16.3 | 6.8 | 26.8 | 24.9 |

Within 0.01 of the nearest fraction: 49 observed against 51.9 expected. **Only `q = 2` exceeds the null**, at 36 against
8.5. My reading before the null ("near small-denominator ratios" in general) is withdrawn; uniform ratios give that.
Part of the `q = 2` excess is selection: a walker that blocks every other opening steps by about half a lap.
- The persistent occupants (segments of 3 or more) are near whole ratios (`q = 1`) in 17 of 18: near-sharers.

**Part 2, perturbation (E67).** Each block reading of the 21 configurations was moved by `±1, ±2` (504 moves):
- 492 leave a hand-off, 4 turn it into a single shadow, and 8 free the flank;
- **all 8 freeing moves move the flank reading itself**, which changes every walker's ratio at once;
- the cascade lands inside `c`'s first arc after every one of the 504.

At readings around `10⁴`–`10⁵` a unit move changes a ratio by about `10⁻⁴`, so this robustness is expected and is recorded,
not read as structure.

**Reading `[derived from the counts above, with their null]`.** Shadowing across `c`'s band run is made of near forms of
the two exact shadowing structures the record already has:
- **the sharer** (Theorem 6.8's dead flank, `A ≡ 0 mod 8`, and its edge forms `A ≡ ±1`): persistent, for about `1/(4|ε|)`
  openings;
- **the half-integer pair** (§6.11: the only exact shadowing pairs have both fractional parts `1/2`): alternating.

In each, the shadow lasts as long as the deviation from the exact structure allows. That is the owner's E156 statement
read at flanks: *"we can already prove grids globally isolate and then it's just a deviation from grid"*.

**Consequence (M7), for C1.** A proof along this line has three parts:
1. the exact structures. The record has them proved: Theorem 6.8; `card_allowed_two_mul` and `card_allowed_lt` (a mover
   blocks at most half its period, exactly half only at `q = 2`); `class_killer_int`;
2. the deviation. A near structure persists for openings in inverse proportion to its deviation. For a near-sharer that
   means `|x_j − A·e| < 0.3c` across `c`'s run (E253);
3. the six flanks together.
   - The twin-chain argument (E253) shows near-sharers alone cannot shadow all six.
   - The open piece is the alternating structure. At the fastest flank every walker's ratio is below 1, so its whole part
     is 0. A near-half pair there has both readings near `x₆/2`, the class pair `(1/2, 1/2)`, which is not one of §6.11's
     shadowing classes. Whether that blocks the alternation at the fastest flank is the next thing to derive and check.

## E259 — 2026-10-02 — design: phase 3c's flank reading on the open configurations (E118's C1 members)

**Owner:** *"Ok do that making sure you are measuring and deriving the framework and not importing anything"*.

**Map:** v3 §4 Q8 and §9 C1; C1 (E118). The gap this closes: E248–E258 read shadowing on populations that E255 showed are
all already closed by §17C. The open configurations are `EightResidual`'s members of C1's shape.

**Population (record, not new).** E118's Case C members, regenerated exactly (seed 118, its construction unchanged) and
saved by `residual_members_C_list_v1.py`. Every member is re-checked against all 22 fields.
- Mode A: the collider `L·u` (`L = 8·lcm(1…64)`) is the least reading.
- Mode B: the collider is inside the fast cluster.

E118's construction climbs on **membership** (the number of fields passed), not on a hardness score. These are
constructed members, not hunted cases. They exclude E60's class by their own field `no_one_free`.

**Read: E253's and E258's readings unchanged, on every member.** `c` is the least reading; the six others are the
cluster's flanks.
- At each cluster flank `e`, `c`'s band run (`u = 8k + 1 ∈ [e/c, 7e/c]`): the first opening with no cluster walker in
  the way (Theorem 6.14's congruence), or *shadowed across the run*.
- For each shadowed flank:
  - one walker throughout, given as `(A, A mod 8, ε)` with `x_j/e = A + ε`, and `|x_j − A·e|/c`; or
  - a hand-off, with its segments and occupants.
- Alternating occupants' nearest small-denominator fraction, against the same exact uniform null as E258.
- The **fastest flank's** state (free / one walker / hand-off), in preparation for step 2.

**Checks (forced):**
- `c` is never in the way inside its run;
- the earliest first-clear cluster-flank opening is the cascade's landing (E118 recorded one mode B member whose flank
  is in the core; any such member is listed, not forced);
- the set is lonely there;
- all 22 fields hold for every member.

**What is native here, stated before running.**
- *Objects:* flank openings, readings mod `8e` (Theorems 6.8, 6.14), each walker's `A` and `ε` (Theorem 6.8's position
  `k·f + ρ/8`), and persistence (Theorem 6.18's bad-run bound).
- *Not used:* rates as answers, stretches or lengths of time, a window as an object, a score.
- *Counts:* bookkeeping of named places.
- *Null:* any "near a fraction" reading is set against its matched null, as in E258.

## E260 — 2026-10-02 — the open configurations read: the fastest flank is free, or shadowed by one near twin whose chain ends free

**Map:** v3 §9 C1; E259 run as designed. Scripts:
- `LonelyRunner/experiments/nN/residual_members_C_list_v1.{py,out,json}`: E118's members regenerated exactly, 297 + 250.
  All pass every field predicate on re-check: 16 predicates covering the 22 fields, with the count of 7 fixed by
  construction.
- `LonelyRunner/experiments/nN/redo/hole_C1_flanks_v1.{py,out}` and `hole_C1_chain_v1.{py,out}`.

**Checks: 0 failures.**
- `c` is never in the way inside its run.
- The landing is the earliest first-clear cluster-flank opening in all 547 members, so E118's one "flank in core" member
  lands at a cluster flank by this reading.
- Every member is lonely there.

**Measured on `EightResidual`'s C1 members** (the open configurations; E253–E258 read only closed ones):

| | mode A (297) | mode B (250) |
|---|---|---|
| cluster flanks shadowed across `c`'s band run: 0 / 1 / 2 | 242 / 48 / 7 | 242 / 8 / 0 |
| shadowed by one walker throughout | 56, all `A ≡ 1`, `ε < 0` (a near twin just below), all with `\|x_j − A·e\| < 0.3c` | 8: `A ≡ 1, ε < 0` 6; `A ≡ 0, ε > 0` 1; `A ≡ 7, ε > 0` 1 |
| hand-offs | 6 (`s` = 2, 2, 3, 3, 4, 9) | 0 |
| **the fastest flank** | free 287; one near twin below 10 | free 249; one near twin below 1 |

- **The chain, followed in all 11 members whose fastest flank is shadowed** (`hole_C1_chain_v1.out`): each link is a near
  twin (`A = 1`, `ε < 0`), and every chain ends at a free flank, after one link in 10 and after two in 1.
- The alternating occupants in the 6 hand-offs number 15. That is too few to read against a null, so nothing is stated
  about them.

**Derived** `[from TwoWalker.bad_run_le, Theorem 6.18's bad-run bound; proved in `experiments/n8/TwoWalker_v1.lean`, a
development file outside the gated tree (v21 l.1879); the step below is not in Lean]`. Exact form: for a walker
with step `0 < f ≤ 1/2`, in the way at `m + 1` consecutive openings ⇒ `m·f < 2/n = 1/4`.
1. At the fastest cluster flank `e = x₆ ≥ 9c`, `c`'s band run has `L ≥ 3e/(4c) − 1` openings. A walker `x_j` in the way
   at every one of them has `(L − 1)·ĝ_j < 1/4`.
2. Here `ρ_j = x_j/e ∈ (0, 1)`, so `ĝ_j = min(ρ_j, 1 − ρ_j)`.
   - If `ĝ_j = ρ_j`, then `x_j < e/(4(L − 1)) ≤ c·(e/c)/(3e/c − 8) < c` (for `e > 4c`), contradicting `x_j > c`.
   - So `e − x_j < e/(4(L − 1)) ≤ (9/19)c`.
3. **A single walker that shadows the fastest flank across `c`'s band run is a near twin just below it, within `(9/19)c`.**
   The largest gap in the data is `0.27c`.
*Correction, same day:* first written with `ĝ ≤ 1/(4L)` and `(9/23)c`, paraphrasing the bound. Read against
`bad_run_le`'s statement it is `(L − 1)ĝ < 1/4` and `(9/19)c`. The conclusion is unchanged.

**Not derived** (measured only, on these members):
- (b) that the fastest flank is never shadowed by a hand-off: 0 of 547 open members, and none in E253's closed
  populations;
- (c) that the near twin's own flank is free, or continues the chain through near twins to a free flank: 11 of 11.

**Native check.**
- Every object is the framework's own: flank openings, readings mod `8e` (Theorem 6.14), positions (Theorem 6.8), and
  the bad-run bound (Theorem 6.18).
- The members are E118's constructed members, built by climbing on membership.
- No rate, stretch or window is used. The counts are bookkeeping of named flanks.

**Consequence (M7).** On the open configurations, C1's case takes the form **"the fastest cluster flank is free, or the
near-twin chain below it ends at a free flank"**: 547 of 547, with step 1 derived. What a proof still owes:
- (b): the fastest flank's long run is not shadowed by several walkers in turn;
- (c): why a near twin's flank is free (its own walkers are the same readings, met at slightly shifted openings);
- the slow flanks, which the chain argument does not need.

## E261 — 2026-10-02 — step 2: (c) reduces to (b); a truth check of (b) from the record's own theorems

**Owner:** *"ok do it"* (step 2: derive (b) and (c), then check).

**Map:** v3 §9 C1; E260's owed items. Read: v21 §16L (`DoorLargestFlank` `[REFUTED]` at thresholds `1/6` and `1/7`;
the failing sets are not listed in `experiments/nN/rules_at_six_seven_v1.out`), §6.11 (`TwoMover.card_allowed_two_mul`,
`card_allowed_lt`: a mover blocks at most half its period, and exactly half only at `q = 2`), and `bad_run_le`.

**(c) reduces to (b), derived.** Let a cluster `x₁ < … < x_m` sit below nothing faster, with slow runner `c`.
1. Suppose the fastest flank `x_m` is shadowed across `c`'s band run by one walker throughout. By E260 that walker is a
   near twin `x_j = x_m − δ_j`. Its in-way condition at every opening `u` of the run is `δ_j·u/x_m ∈ (0, 2)`; at the
   run's last opening `u ≤ 7x_m/c` this gives `δ_j < 2c/7`. Every reading strictly between `x_j` and `x_m` is within
   `δ_j` of `x_m`.
2. At every opening `u` of `x_{m−1}` inside `c`'s band run (`u ≤ 7x_{m−1}/c`), `x_m` reads
   `x_m·u/x_{m−1} ≡ 1 + δu/x_{m−1}` (mod 8), with `δ = x_m − x_{m−1} ≤ δ_j`. So `0 < δu/x_{m−1} ≤ 7δ/c < 2`: the
   reading is in `(1, 3)`, and **`x_m` is clear at every such opening.**
3. So the full set is lonely at an `x_{m−1}` opening inside `c`'s arc **exactly when** the set without `x_m` is lonely
   there. That is the same question one level down, at the new fastest flank `x_{m−1}`.
4. Recursing: a cluster of one is free (only `c` walks, and it is clear in its run).
   - Readings above the current flank stay clear while their total gap `Δ` keeps `Δ·u/x < 6`. That holds automatically
     for chains of up to three twins (`Δ < 6c/7`). Deeper chains need the cumulative check.
   - The data's chains have depth at most 2 (E260).

**So C1 follows from (b) at every level of the chain** `[derived]`. Here (b) says: *a cluster's fastest flank is not
shadowed across `c`'s band run by several walkers in turn.* (c) is no longer a separate owed item.

**(b), what the record's theorems already say.**
- At the fastest flank every walker's ratio is below 1, so it is never a whole number. By `card_allowed_two_mul` and
  `card_allowed_lt`, a single walker blocks at most half its period.
- So **a shadow of every opening of the fastest flank is necessarily a hand-off.** Single near twins shadow only because
  `c`'s band run is finite (Theorem 6.18's persistence).
- Hence (b) is **false in general** if some six readings at threshold `1/8` have their largest flank shadowed at every
  opening. Put a slow runner `c` below them, with the six scaled so that `x₁ ≥ 9c`, which changes no ratio. The result
  is a C1-shaped set whose fastest flank is hand-off-shadowed across `c`'s run.

**Truth check (exhaustive, exact).** Every six-set `≤ 30` with `gcd 1`. Its largest flank `e`, at every opening
`j < e` (Theorem 6.13's period): is some walker in the way, `d(8j + 1) mod 8e ∉ [e, 7e]` (Theorem 6.14)?
- Report the six-sets whose largest flank is shadowed at every opening.
- For each, form the C1-shaped set: `c = 1` and the six scaled by `K = ⌈9/x₁⌉`. Record:
  - whether the fastest flank across `c`'s run is a single shadow or a hand-off;
  - where the cascade lands (flank and rank);
  - whether the set is in `EightResidual` (E255's classifier).

**Checks:** the residue test agrees with direct evaluation of `circDist` at the opening instants (exact), on every flagged
set.

## E262 — 2026-10-02 — (b) is false for C1-shaped sets in general; every counterexample found is closed by §17C

**Map:** v3 §9 C1; E261 run as designed. Script `LonelyRunner/experiments/nN/redo/fastest_flank_check_v1.{py,out}`.

**Check: 0 disagreements.** The residue test (Theorem 6.14) agrees with direct `circDist` evaluation on all 58 flagged
six-sets.

**Result.**
- Of the 588,559 six-sets `≤ 30` with `gcd 1`, **58 have their largest flank shadowed at every opening** at threshold
  `1/8`. Examples: `(2, 3, 7, 10, 16, 20)`, `(1, 3, 4, 5, 7, 8)`, `(1, 21, 22, 23, 24, 30)`.
- By the half-period mover theorems each of these shadows is a hand-off (E261).
- Each gives a C1-shaped set `(1, K·six)` whose fastest flank is hand-off-shadowed across `c`'s band run: 58 of 58, with
  `s = 31` to `139` segments.
- **So (b), "a cluster's fastest flank is not shadowed by a hand-off", is false for C1-shaped sets in general.** E261's
  recursion therefore does not prove C1 from the walker theorems alone.

**Where the cascade lands in them.** At `c`'s own flank in 32 (the six scaled by `K` with no reading `≡ 0 mod 8`, so
lonely at the bound). At a slower cluster flank in 26: rank 2 in 7, rank 3 in 6, rank 4 in 6, rank 5 in 7.

**All 58 are closed by §17C** (first rule: R6 at `q = 8` 30, free flank 19, R6 at `q = 6` 5, rational opening 4;
`fastest_flank_check_v1.out` lists each). **None is in `EightResidual`.** On `EightResidual`'s
C1 members (E260) the fastest flank was never hand-off-shadowed (0 of 547).

**What this says** `[derived from the counts and the field each set fails]`. (b)'s failures in this range are exactly
configurations that the arithmetic of §17C closes.

*Correction, same entry:* the rule counts were first written from a partial view of the output (32 / 14 / 5 / 5 / 2).
Counted from the full file they are 30 / 19 / 5 / 4.
- The largest group (30) fails `EightResidual`'s `eight` field: no reading is a multiple of 8, so nothing shares the
  subject's slot at the grid.
- In `EightResidual` some reading is `≡ 0 (mod 8)`, which is the owner's *"two runners in the same slot"* again.

So a proof of C1 along the fastest-flank recursion cannot stand on the walker theorems alone. It has to use
`EightResidual`'s arithmetic: the same fields whose failure closes (b)'s counterexamples.

**Consequence (M7).**
- (c) is derived: it reduces to (b) one level down (E261).
- (b) is refuted in general. On the open configurations it holds (547 of 547), and in this range every counterexample is
  closed by §17C.
- **The owed statement is now (b) restricted to `EightResidual`:** *for a set in `EightResidual` of C1's shape, the
  cluster's fastest flank is not hand-off-shadowed across `c`'s band run.* Its proof has to say which field excludes the
  hand-off.
- Two next steps, each native:
  1. a truth check of the restricted statement on more `EightResidual` members, built by E117/E118's construction with
     other seeds;
  2. for each of the 58 counterexamples, which `EightResidual` field it fails, and whether one field (`eight`, the
     slot-sharer) accounts for the hand-off mechanism.

## E263 — 2026-10-02 — design: the restricted (b) tested three ways, all by the record's own construction

**Owner:** *"yes"* to E262's two next steps.

**Map:** v3 §9 C1; E262's owed statement, **(b) restricted to `EightResidual`**: for a C1-shaped set in `EightResidual`,
the cluster's fastest flank is not hand-off-shadowed across `c`'s band run.

**Part 1 (E262 step 1).** E118's construction, unchanged, under 10 new seeds (201–210), both modes. On every member:
- E260's flank reading (`hole_C1_flanks_v1.study`): the fastest flank's state;
- for a shadowed fastest flank, the near-twin chain to a free flank (E260's chain logic);
- every member with its fastest flank hand-off-shadowed is a counterexample and is listed.

**Part 2 (E262 step 2).** For each of E262's 58 C1-shaped sets `(1, K·six)`: every `EightResidual` field predicate it
fails (all 16, not only the first). Is there one field, such as `eight` (8 divides some reading, the slot-sharer), that
all 58 fail?

**Part 3 (the decisive test, found while designing).** The fields depend on the actual integers; the hand-off shadow
depends on the ratios, and survives small relative changes across `c`'s finite run. So each of the 58 shapes is built
toward membership by E118's own method:
- `c = L·u` (the collider, `L = 8·lcm(1…64)`, `u ∈ [1, 19]`);
- the cluster is `K·six` with `K·x₁ ∈ [25c, 175c]`;
- the cluster readings are adjusted by small integers, climbing on the number of fields passed. **The fastest flank must
  stay hand-off-shadowed across `c`'s run at every accepted step.**

Up to 6 restarts per shape, 400 steps each. A member found is a counterexample to the restricted (b); its cascade landing
is read. If none is found, the null is scoped to this construction.

**Checks (forced):**
- every member re-checked against all 16 predicates;
- `c` never in the way inside its run;
- the cascade's landing is lonely (exact).

**Native check.** Objects as in E260. The construction climbs on membership only (E118's objective), under a structural
constraint. Nothing is scored for hardness.

## E264 — 2026-10-02 — the restricted (b) is refuted on `EightResidual`; the fastest flank was not the place, the slowest cluster flank is free in 5,957 of 5,978

**Map:** v3 §9 C1; E263 run as designed. Scripts (all in `LonelyRunner/experiments/nN/redo/`): `restricted_b_v1.{py,out}` (Parts 1–2; its Part 3 hung in the pool and is superseded), `restricted_b_p3_v1.{py,out}` (Part 3, same functions and seeds), `ce6_verify_v1.{py,out}`, `ce6_read_v1.{py,out}`, `free_ranks_v1.{py,out}`, `rank1_exc_v1.{py,out}`.

**Part 1: E118's construction, seeds 201–210, both modes: 5,431 members.**
- Checks: 0 field failures on re-check (16 predicates); 0 check failures in `study`; landing is the earliest first-clear cluster-flank opening in all 5,431.
- Fastest-flank state: free 5,313, one walker 112, **hand-off 6** (seeds 206, 207, 208; mode A).
- **The six, checked independently** (`ce6_verify_v1`, direct `circDist` at every opening of `c`'s run, not the residue test): each is `classify` = "EightResidual, not E60"; `c` is never in the way; the fastest flank is shadowed at all 31–68 openings; the cascade lands lonely at a slower cluster flank (reading index 2–4).
- **Their structure** (`ce6_read_v1`): the second-fastest reading is a near twin (`A ≡ 1`, `ε` −0.003 to −0.007) in the way for 29–67 openings, then a tail of 1–6 openings by other walkers (hand-off of 2 to 4 occupants). The five slower flanks are free in all six.
- **So seed 118's 0 of 547 was a small sample of an event of order 0.1% (6 of 5,431).** E260's "547 of 547" and E262's "holds on the open configurations" were statements about that sample.

**Part 2: the 58 shapes of E262 against all 16 predicates** (`restricted_b_v1.out`).
- Failed by all 58: `rational N|8`, `6,7,9`, `small resolution`, `one free`. Failed by 35: `5,6,7,8`; by 22: `free flank`; by 32: `first lap/-7`; by 51: `thirds/fifths`. 7 distinct failing-field sets.
- So **no single field, and not the slot-sharer (`5,6,7,8`), accounts for the 58**. E262's "first rule" counts (30 / 19 / 5 / 4) are the order of `classify`'s rules, not a mechanism.

**Part 3: the 58 shapes built toward membership** (`c = L·u`, cluster `K·six` with `K·x₁ ∈ [25c, 175c]`, integer adjustments, climbing on fields passed; 6 restarts × 400 steps per shape).
- Check: start states violating the constraint 0 of 348.
- **Constrained** (fastest flank kept a hand-off at every accepted step): **271 of 348 runs reach all 16 predicates; 57 of 58 shapes** (the 58th stalled on `first lap/-7`, a climb result, not a statement about the shape). Every member's fastest flank is a hand-off. Checks on the 271: 0 failures, landing at the earliest first-clear cluster flank, lonely.
- Control (no constraint): 264 of 348, 57 of 58; the hand-off also persists there. Small integer adjustments change the fields and leave the ratios, so the fields are arithmetic of the integers and the shadow is a fact about the ratios.
- **The restricted (b) is false:** `EightResidual` members with a hand-off-shadowed fastest flank exist, and the arithmetic of the fields does not exclude them.

**The place that does hold** (`free_ranks_v1`, `rank1_exc_v1`; seed 118's 547 plus seeds 201–210; 5,978 members):
- every member has a free cluster flank (0 with none);
- the **slowest** cluster flank (rank 1) is free in 5,957 (A 3,288 of 3,291; B 2,669 of 2,687); in the other 21 (rank 1 shadowed by one walker in 10, by a hand-off in 11) **rank 2 is free in all 21**;
- the fastest flank is free in 5,849, one walker 123, hand-off 6.
These are counts by place on constructed members, not a proof.

**Consequence (M7), for map §9 C1.**
- The fastest-flank line (E259–E262: (b), (c), the chain below the twin) was my choice of flank in E259, taken because the flank reading was run there first; the data now say it is not the place. (c)'s derivation (E261) stands as an implication; (b) restricted is `[REFUTED]` on `EightResidual`.
- The owed statement: **for a C1-shaped set in `EightResidual`, the slowest cluster flank is free across `c`'s band run, or it is shadowed and the second-slowest is free.** Cascade-side: the landing is at rank 1 or 2 of the cluster in the 5,978 here.
- What is not yet understood: why the slowest flank clears (what its walkers' ratios `x_j/e₁ ≥ 1` do across `u ∈ [e₁/c, 7e₁/c]`), and the 21 rank-1 exceptions (feature, what forces rank 2's witness, same mechanism or not). These go to map §6 as "not understood" until each has an artifact.

## E265 — 2026-10-02 — design: why the slowest cluster flank clears, and the 21 rank-1 exceptions, read through the cascade

**Owner:** *"We better figure that out"*; *"yes, read both through the cascade"*.

**Map:** v3 §9 C1; E264's owed statement (rank 1 free, or rank 2 free). Two items marked "not understood" in E264: (1) why rank 1 clears; (2) the 21 members whose rank 1 is shadowed: the feature, what forces rank 2's witness, same mechanism or not.

**Objects (Theorem 6.8's position, Theorem 6.14's congruence; no new object).** At flank `e`, opening `u = 8k+1`, a walker `x_j` has reading `ρ_j(u) = x_j·u/e mod 8 = A_j + ε_j·u (mod 8)`, where `x_j/e = A_j + ε_j`, `A_j` an integer, `|ε_j| ≤ 1/2`. It is in the way iff `ρ_j ∈ (−1, 1)` mod 8. Along `c`'s band run `u ∈ [e/c, 7e/c]` each walker's reading is a line in `u` of slope `ε_j`.
- At the **fastest** flank every walker has `x_j/e < 1`, so `(A, ε)` is `(1, −)` (a near twin below) or `A = 0`.
- At the **slowest** flank every walker has `x_j/e₁ ≥ 1`, so `A ≥ 1`, and `A = 1` forces `ε ≥ 0`. No `(1, −)` twin below exists.

**Reading to test (stated before running; I derive it, then check the data against it).**
1. *Single-walker shadow across the whole run.* It needs `|ε|·(u_hi − u_lo) < 2` (the reading crosses a block of width 2 at speed `|ε|`) and a start inside `(−1, 1)` at `u_lo ≥ e/c`. So `|ε|·u_lo` is below 2 and `A mod 8 ∈ {0, 1, 7}` with the sign that keeps the reading in the block (`A ≡ 1`: `ε < 0`; `A ≡ 7`: `ε > 0`; `A ≡ 0`: either). At rank 1 that forces `x_j/e₁ ≳ 6.5`. Check against: every `alone` state by rank on all 5,978 members; also on a population that is not constructed for membership (random clusters), to see whether the reading is about the arrangement and not the construction.
2. *Hand-offs at rank 1.* Express every occupant as `(A, ε)`; split into sweeps (`|ε|` small: a walker crossing a block) and `ε ≈ ±1/2` (the half-integer structure of E257–E258). Count by type.

**Perturbation through the cascade, the 21 exceptions.** For each exception and each cluster walker `j`, shift `x_j` by `δ·e₁` for `δ ∈ {±0.01, ±0.05, ±0.1, ±0.25}` (rounded to integers; `c` stays the least reading). After each shift: rank-1 state, the cascade's landing rank and lonely check. Reported per exception:
- the walkers whose shift frees rank 1 (the shadow depends on their `(A, ε)`);
- whether the landing moves from rank 2 and where;
- at the rank-2 witness opening: every walker's reading `ρ_j` and its margin to the block edge; the shadower's `(A', ε')` at `e₂` against `ε' ≈ ε − A·η` (`η = e₂/e₁ − 1`), i.e. the displacement of the shadower's ratio by the gap between the flanks.

**Checks (forced).** The exact cascade's landing equals the earliest first-clear cluster-flank opening for every perturbed set; `c` never in the way inside its run; lonely at the landing; the reading `ρ_j = (A_j + ε_j u) mod 8` equals `(x_j u / e) mod 8` exactly on every member opening.

**Native check.** Objects are positions, `(A, ε)`, openings and `c`'s run, all the record's. Nothing is scored for hardness; the counts name places. Perturbation follows owner 2026-09-27 (E102/E111).

## E266 — 2026-10-02 — why the slowest flank is shadowed least; the 21 exceptions read; two corrections to E264

**Map:** v3 §9 C1; E265 run. Scripts in `LonelyRunner/experiments/nN/redo/`: `slow_flank_mech_v1.{py,out}` (reading and tests; its Part 3 perturbation filter and landing-rank definition are superseded), `slow_flank_mech_v2.{py,out}` (corrected perturbation and per-rank counts), `one_both_v1.{py,out}`, `members_5978_v1.json`.

**Corrections to E264 (both mine).**
1. *"Cascade-side: the landing is at rank 1 or 2 of the cluster in the 5,978 here."* is **false**. I measured which flanks are free, never where the cascade lands. By the record's convention (the runner `x` with `8xt ≡ 1 mod 8`) the landing flank over the 5,978 is rank 1: 864, rank 2: 920, rank 3: 942, rank 4: 1,050, rank 5: 1,085, rank 6: 1,117; never `c`. Among the 21 rank-1 exceptions: rank 2 in 2, 3 in 6, 4 in 4, 5 in 4, 6 in 5. The cascade lands at the earliest free opening over all flanks; "rank 1 free" is a statement about which flanks have a free opening in `c`'s run, not about the landing.
2. In E265's script the perturbation filter `min > 24c` skipped most mode B shifts, and 20 shifted sets read "cascade ≠ earliest first-clear" because I did not allow the landing at `c`'s own flank. Both fixed in v2 (validity = distinct, `c` least, `c` never in the way; landing read from `trace`). Lonely at the landing asserted for every perturbed set.

**Checks (0 failures).** The line reading `ρ_j = (A_j + ε_j u) mod 8` equals `x_j u / e mod 8` at every opening of every flank of the 5,978 members; `inway` agrees with `ρ ∉ [1, 7]`.

**Derived** (from the line reading alone; `c`'s run is `u ∈ [e/c, 7e/c]`, `u_hi = 7u_lo`). A single walker shadowing a flank across the whole run needs `|ε|·(u_hi − u_lo) < 2` (it crosses a width-2 block at speed `|ε|`), so `|ε|·u_lo < 1/3`, and then `A mod 8 ∈ {0, 1, 7}` with the block-keeping sign: `(1, −)`, `(7, +)`, `(0, ±)`.
- At every flank above the slowest, the commonest such walker is the **twin below** `(A, ε) = (1, −)`; the slowest flank has no walker below it, so `x_j/e₁ ≥ 1` and `A ≡ 1` needs `A ≥ 9`, `A ≡ 7` needs `A ≥ 7`, `A ≡ 0` needs `A ≥ 8`. **A single-walker shadow of the slowest flank is a near-harmonic with `x_j/e₁ > 7`.**

**Measured against it.**
- Members, single-walker shadows by rank: **10** at rank 1; 95, 133, 129, 119, 123 at ranks 2–6. Every rank ≥ 2 shadow is `(1, −)`; every rank-1 shadow has `(A mod 8, sign)` in the allowed set and ratio `> 7` (minimum 7.0017). 0 violations.
- Random clusters (12,000 with `c` never in the way; `c ∈ [10⁶, 10⁷)`, cluster in `[25c, 25c·span)`, span 1.5–40): single-walker shadows 22 at rank 1; 384–428 at ranks 2–6; rank-1 minimum ratio 7.0004; 0 violations. So this is about the arrangement, not about the E118 construction.
- **Hand-offs are level across ranks:** members 11, 12, 10, 7, 8, 6 (ranks 1–6); random 20, 40, 33, 41, 31, 26. The slowest flank has no advantage against hand-offs.
- So the slowest flank is shadowed least (21 members against 107–143 elsewhere) **because the twin-below class is absent at rank 1**; that accounts for the difference in single-walker shadows and for none of the hand-offs.

**The 21 rank-1 exceptions** (`slow_flank_mech_v1.out`, `one_both_v1.out`).
- **10 single-walker:** the shadower is a near-harmonic of `e₁` (`A₁` = 7, 8, 8, 8, 9, 15, 16, 17, 24, 8; `|ε₁|` ≤ 0.0099). At `e₂` its ratio is `r₁/(e₂/e₁)` exactly, and its `A₂` is 2, 7 (`ε₂ = −0.46`), 6, 6, 2, 4, 5, 6, 4, 6: **in none of the 10 is it in a persistent class at `e₂`** (`A₂ ∈ {0,1,7}` with the right sign and `|ε₂|` small). For the same walker to shadow `e₁` and `e₂` persistently, `x_j` must be a near common multiple of both, `e₂/e₁ ≈ A₁/A₂`: the near form of the sharer structure on record.
- **Perturbation:** shifting `e₁` or the shadower frees rank 1 in nearly all shifts; in 9 of 10 the walkers whose shift frees rank 1 (≥ 6/8) are exactly `{e₁, shadower}`. In the tenth (seed 210 B, ratio 8.006) moving the harmonic away leaves rank 1 shadowed **as a hand-off** (12 openings; the other walkers already cover most of them), so there the shadow is not the harmonic's alone.
- **11 hand-offs:** occupants include `ε ≈ ±1/2` walkers (half-integer structure) and sweeps through the block; critical sets are 2 to 6 walkers (for seed 205 A, all six). These are the same kind as the hand-offs at ranks 2–6 (counts above).
- **What forces rank 2's witness: not explained.** In all 21 rank 2 is free; its witness readings have margins from 0.1 to 2.7 from the block edge, nothing special. What is established: rank 2 has two possible persistent shadowers, `e₁` as a twin below (needs the gap `e₂ − e₁ ≲ 2c/7`; in the 21 `e₂/e₁ − 1 ≥ 0.07`, so `e₁` is out) and a harmonic (none in the 10 as above); and rank-2 hand-offs occur (12 members; random 40).
- **A counterexample to "rank 1 or rank 2 free" exists in the random population** (not `EightResidual`): seed 24, `x/x₁ = 1, 1.002, 1.273, 1.526, 1.953, 1.984`; rank 1 a hand-off (4 walkers over 25 openings), rank 2 shadowed by `e₁` as a twin below (`ε = −0.0021`); ranks 3–6 free; the cascade lands at `c`'s own flank (`R = 1.0000`). So "rank 1 or rank 2 free" is **not** a statement that holds in general, and nothing so far shows `EightResidual`'s fields exclude it.

**Consequence (M7), map §9 C1.**
- The owed statement of E264 ("rank 1 free, or rank 2 free") **is withdrawn** as a proof target: it is a count on constructed members, with a general counterexample and no field shown to exclude it.
- What the data support: **some cluster flank has a free opening in `c`'s run** (0 of 5,978 members and 0 of 12,000 random clusters without one), with the cascade landing at any rank 1–6. That is the shape C1's cascade landing takes; whether it needs `EightResidual` is open (random clusters have the landing at `c`'s flank in 2,493 of 12,000, which no member has).
- The persistent classes at a flank are derived and fully accounted for (`(1,−)` below, near-harmonic above, `A mod 8 ∈ {0,1,7}`); what remains unaccounted for is the **hand-off** (mixing) coverage, which is level across ranks. A proof has to say why a run of 6–100+ openings is not covered by hand-offs at *every* cluster flank at once.
- Next, native: (i) construct `EightResidual` members with ranks 1 and 2 both shadowed (E263's Part 3 method, constraint = both shadowed), which tests whether the rank-2 witness is forced by the fields; (ii) read the hand-offs as sweeps and half-integer structures (E257–E258) per flank to find what a joint cover of all six flanks would need.

## E267 — 2026-10-02 — design: ranks 1 and 2 both shadowed on `EightResidual`; the hand-offs and the joint cover of all six flanks

**Owner:** *"yes, run both"* (E266's two next steps).

**Map:** v3 §9 C1; E266's open items: what forces rank 2's witness; what a joint cover of all six flanks needs.

**Test 1 (E263 Part 3's method, a different constraint).**
- *Starts:* random clusters (`c ∈ [10⁶, 10⁷)`, cluster `≥ 25c`), half with a forced near-twin pair at ranks 1–2 (`e₂ = e₁ + g·c`, `g ∈ [0.02, 0.30]`), half unforced; a start is kept when `c` is never in the way and **ranks 1 and 2 are both shadowed** (single walker or hand-off), all openings of `c`'s run read exactly (`inway`, Theorem 6.14). About 4 million samples.
- *Build:* each distinct start scaled to `c' = L·u` (`u ∈ [1, 19]`), cluster `round(ratio·c')`; integer adjustments (E263's moves), climbing on fields passed (16 predicates), **ranks 1 and 2 kept shadowed at every accepted step**; 6 restarts × 400 steps. Control: same starts, constraint removed.
- *Read on each member:* ranks 1 and 2 states; the landing flank (record's convention); lonely; `study`'s checks.
- *Checks:* start states satisfy the constraint after scaling; `c` never in the way; lonely at the landing, exact.

**Test 2 (hand-offs, joint cover).** Objects: the line reading `A_j + ε_j u (mod 8)`, `c`'s run, greedy segments of a hand-off (flank's own).
- (a) Every hand-off flank on the 5,978 members and the random clusters: occupants' `|ε|` weighted by the openings each covers (bins 0–0.05, 0.05–0.15, 0.15–0.35, 0.35–0.45, 0.45–0.5: sweep, mixing, half-integer).
- (b) The state pattern over the six flanks per member and per random cluster (free / one walker / hand-off), and the number of shadowed flanks.
- (c) What a **chain** of persistent shadows needs: flanks `2…m` each shadowed by the twin below needs each gap `e_i − e_{i−1} < c/3` (from `|ε|(u_hi − u_lo) < 2`, `|ε| = gap/e`, `u_hi − u_lo = 6e/c`); I test, on clusters built with twin chains of length 1…5 at the top, which flank patterns occur and whether rank 1 is free whenever flanks 2…6 are all chain-shadowed.

**Native check.** Objects as in E266; construction climbs on membership only under a structural constraint, as E263. Nothing is scored for hardness; no rate is offered as an answer.

## E268 — 2026-10-02 — ranks 1 and 2 both shadowed on `EightResidual`: 287 members; the fields do not force rank 2's witness; the joint cover read

**Map:** v3 §9 C1; E267 run as designed. Scripts in `LonelyRunner/experiments/nN/redo/`: `both_shadowed_v1.{py,out}` (+ `both_shadowed_members_v1.json`), `handoff_joint_v1.{py,out}`.

**Test 1.** 4,000,000 random clusters gave 3,982 with ranks 1 and 2 both shadowed and `c` never in the way (3,974 of them from the forced near-twin pair at ranks 1–2; the 8 unforced ones are the rest). 80 distinct starts scaled to `c' = L·u` and climbed on the 16 predicates; start states violating the constraint after scaling: 0 of 480.
- **Constrained** (ranks 1 and 2 kept shadowed at every accepted step): **287 of 480 runs reach all 16 predicates; 49 of 80 starts.** Rank-1 / rank-2 states: one walker / one walker 211, hand-off / one walker 70, one walker / hand-off 6. The cascade lands at cluster rank 3: 83, 4: 99, 5: 65, 6: 40. Checks: 0 failures, lonely at the landing, landing at the earliest first-clear cluster flank in all 287.
- Control (no constraint): 289 of 480, 49 of 80, the same pattern (so the constraint does not cost membership). Starts that did not reach membership stalled on `6,7,9`, `free flank`, `rational N|8`, `thirds/fifths`, `first lap/-7`, the same fields as E263's.
- **So the fields of `EightResidual` do not force rank 2's witness**, and "rank 1 or rank 2 free" is false on `EightResidual`, with the withdrawal of E266 now confirmed on the open configurations. Every member's shadowed flanks are exactly ranks 1 and 2 (`AAFFFF` 211, `HAFFFF` 70, `AHFFFF` 6); ranks 3–6 free and the landing in them.

**Test 2.**
- *(a) Hand-off occupants.* By openings covered, `|ε| < 0.05` carries 89.9% (members, 54 hand-off flanks) and 90.8% (random, 191); half-integer (`|ε| ≥ 0.45`) 2.0% and 0.7%. By **segments** (a segment is a stretch with one occupant): members `|ε|` 0–0.05: 68, 0.05–0.15: 21, 0.15–0.35: 56, 0.35–0.45: 11, 0.45–0.50: 30; random 263, 109, 174, 33, 36. So a hand-off is a few long sweeps by near-harmonic or near-twin walkers (the openings) together with many one- and two-opening occupants of larger `|ε|` (the segments), including `ε ≈ ±1/2`.
- *(b) Patterns.* Shadowed flanks per set: members 0: 5,372, 1: 551, 2: 53, 3: 2; random 0: 10,042, 1: 1,670, 2: 272, 3: 16. Most are one walker (`A`); hand-offs are 54 and 191 flanks in total. No set has more than 3.
- *(c) Twin chains.* Clusters built with `k` twin links at the top (gaps 0.02c–0.30c, 40,000 each): shadowed flanks reach 5 (k = 4: 561; k = 5: 32,749 sets have flanks 2–6 all shadowed). **Whenever flanks 2–6 are all shadowed (0, 1, 24, 527, 32,749 sets for k = 1…5), rank 1 is free in all of them.** No set with all six shadowed in any population above.

**Derived** (the line reading; no new object). *If the cluster's spread `x₆ − x₁ ≤ 3c` (with `x₁ ≥ 9c`), the slowest flank is free at the first opening of `c`'s run.* At `u*`, the first `8k+1 ≥ e₁/c`, `u* < e₁/c + 8` and `u* ≡ 1 mod 8`, so a walker with `r = x_j/e₁ ≥ 1` reads `ρ = 1 + (r − 1)u* (mod 8)`; `(r − 1)u* ≤ 3 + 24c/e₁ ≤ 3 + 8/3 < 6`, so `ρ ∈ [1, 7]`: clear; `c` is clear in its own run. A chain of five twin links, each gap `< c/3` (the persistence bound of E266), has spread `< 5c/3`, which gives the 100% above.

**What a joint cover would need** `[derived pieces + measured]`.
- Rank 1 needs a near-harmonic of ratio `> 7` or a hand-off (E266). So the cluster's spread is `> 3c` (by the bound above) and the rank-1 cover cannot come from a tight chain.
- Each flank `i ≥ 2` needs a twin below with gap `< c/3`, a near-harmonic, or a hand-off. A single walker can be a near-harmonic of two flanks only as a near common multiple of both.
- Hand-offs are rare and do not combine in the data (≥ 3 shadowed flanks in 2 of 5,978 members).

**Consequence (M7), map §9 C1.**
- (E266's target) "rank 1 or rank 2 free": `[REFUTED]` on `EightResidual` (287 members).
- The surviving form is the cascade's own: **some cluster flank has a free opening in `c`'s run**, the landing at ranks 1–6 (members: 864 / 920 / 942 / 1,050 / 1,085 / 1,117; the 287 here at 3–6). Counts: 0 failures in 5,978 + 287 members and 12,000 random clusters.
- What a proof has to do is exclude a joint cover of all six flanks. Derived: a chain of twins through flanks 2–6 cannot cover (rank 1 is then free by the `3c` bound). Open: covers that mix classes (hand-offs, near-harmonics, twins), and why hand-offs at different flanks do not combine.
- Not run: a search aimed at six shadowed flanks. Nothing in this entry says one exists or does not.

## E269 — 2026-10-02 — map v4 cut and checked; whether the cascade's mechanics need a cover

**Owner:** *"yes, cut map v3 with E264–E268 folded into C1"*; and: *"And do we need cover for the cascade mechanics to be proven?"*

**Map:** none — housekeeping (a map cut and its `compile-diff`) and a question answered from the record.

**Numbering.** `MECHANISM_MAP_v3.md` already existed (cut 2026-10-01, E220, scope E100–E219). Versioning forbids overwriting it, so the new map is **`docs/n8/MECHANISM_MAP_v4.md`** (v3 retained unchanged). Its scope is E220–E268, not only E264–E268: E220–E263 had never been folded in either.

**What v4 adds.** §0: the owner's rulings of E220–E263 (Lean on hold, E222; search the record before asking, E225; the obligation's form, E230; the native-object check, E251; E252, E259) and three session findings. §1: objects (core, block, `g`, flank, walker, band run, line reading, near-sharer, hand-off, C1-shape). §2: I (Levels A–C), J (Level D read in the holes; the lower orders' template, E255), K (the flank at the C1-shape, with the E264–E268 results). §3: R15–R17. §4: Q8 status and **Q9, the C1-shape statement**. §6: F17 (a constructed sample's regularity stated as a law), F18 (the owner's form replaced by a stricter one) and new instances of F1, F2, F3, F4, F5, F7, F9, F16. §8, §9 C16–C23 (and a (v4) note on C1: the question of §17B is answered), §10a (artifacts).

**`compile-diff`** (mandatory before reliance; `docs/n8/MECHANISM_MAP_v4_COMPILE_DIFF_v1.md`). First draft: v3 carried byte-identical except the header and the appended text in C1 and C14; 9 losses, 5 widened scopes, 3 correction gaps, 4 internal conflicts; no grade moved up, no retracted statement re-claimed, one wrong number (the E253 `q > 1000` pair gave one population, not both). The agent's most consequential finds: the `L₀` ladder (verified, not proved) and E230's withdrawals 4 and 5 were absent; E262's result and E266's open question (does the statement need `EightResidual`'s fields) were absent; a dangling reference to an "excision table"; stale v3 owed items. All repaired and checked by grep that the repair phrases are present; every script named in §10a checked to exist.

**The question: do the cascade's mechanics need a cover?** I read "cover" as the joint cover of the six cluster flanks (all shadowed across `c`'s band run); if the owner meant register item 4 ("covering"), the last point applies.
- **The mechanics, no.** Levels A–C (E221–E223) describe every move, passage, bridge and the landing as the earliest free opening (v21 §6.10, sort and scan) without any cover statement; the landing is a place named by the readings.
- **The C1-shape's case, the cover is its statement.** "Some cluster flank has a free opening in `c`'s run" is by definition "the six flanks are not all shadowed there"; excluding a joint cover is that statement, not an extra requirement. Under E230's form any admissible argument counts (by contradiction from an assumed cover, or by naming a flank and opening), but it has to be derived from the framework's objects. What is derived (§2 K): the persistent classes; a single-walker shadow of the slowest flank is a near-harmonic of ratio `> 7`; a twin chain through flanks 2–6 cannot cover (spread `≤ 3c` makes rank 1 free). What is open: covers that mix hand-offs, near-sharers and near-harmonics.
- **It is not logically required by the obligation.** The obligation is `∃ (e, k)` (E230); `c`'s own flank or a later window could serve, and in random clusters outside `EightResidual` the landing is at `c`'s flank in 2,493 of 12,000. Cover exclusion is the form the mechanism takes for this shape in every member read (5,978 + 287), and whether it needs `EightResidual`'s fields is open (Q9).
- **A caution on "covering".** Register item 4 and F15 record that covering as a question's object has been an imported shape (Q7 withdrawn, E215). A cover-exclusion argument is native only when attached to a place; today no place rule exists (the landing is at ranks 1–6 with no rank rule, E264–E268), which is why exclusion by derivation is the remaining route and not a rank rule.

**Consequence:** map v4 is the start point for the next step (map-first). No step is approved. Open per §4 Q9 and §7: the hand-offs per flank as sweeps and half-integer structures; the 21 rank-1 exceptions' rank-2 witness.

## E270 — 2026-10-02 — owner: stop; complete the finite cover; `1…7, 10¹⁰` is not a new arrangement from `1…7, 17`

**Owner** (in sequence, after E269): *"yes we can read the hand-offs per flank first but I think this is good moment to pause and think about what we are doing. We are trying to prove n=8 by showing there are only finite amounts of arrangements and those arrangements can be view in terms of ap/grid providing that all arrangements achieve individual isolation by moving the isolation points depending on the arrangement of the speeds."* Then, on what finite means: *"while there are continuous ability of speeds to change there are only a finite set of arrangements of runners. This is due to several things, first the conjecture itself means that runner 2's speed can not increase more than runner 3's speed without becoming runner 3. The scale invariance so 0.000001...0.000008 is the same as 1m...8m or 1pi...8pi and then the fact grid goes on forever. When you logically work your way through all the conditions, there aren't an infinite set of arrangments."* Then, asked to look at Lean: *"OK if we haven't then we really need to stop and complete that work. 1...7,10000000000, is not a new arrangement from 1...7,17."*

**Map:** v4 §4 Q8 and Q9; §2 F (`Cover8`), §9 C12–C13. **No run.** Housekeeping: the owner's direction and what the Lean says.

**Read in Lean (E270; sources only, nothing rebuilt):**
- `ArrangementShapeN.reduction_iff` (untracked, another session's): any arrangement is exactly an affine rescaling of one ordered shape `0 = x₀ < … < x₇ = 7` (labelling, drift, scale removed; six free values; reference grid labels at most 49). It says it makes no claim that finite grid signatures determine every cascade move.
- `RegimeSkeletonN.lonelyRunnerAt8_of_cover8`: `Cover8 M → LonelyRunnerAt8` for every `M`, no case split; `lonely_of_gridClass8` (1-D Helly on laps). **`Cover8 M` is the one owed statement** (a `Prop`, hypothesis only), checked on populations, none uncovered. Its header carries the owner's three reductions (the lap is free, the scale is a reading's own) and the retired spread split (E166: *"because of scale invariance and infinite grid the spread of 7–24 is irrelevant"*).
- `Order8SkeletonN`: the scale-free hole is listed with "the finite cover not built".
- Without a step bound `M` the covering is the conjecture restated (v3 §5); with `M` a uniform step bound is a time bound (E170, §9 C13).

**Correction to E269's reply (F7).** The reply said the record had no statement of the finite list; `Cover8` is that statement. The file was not opened before the reply.

**Owner's example, as the Lean sees it** (`1…7, 17` against `1…7, 10¹⁰`): they fall in different proved cases: `10¹⁰` is a block of one above `7·7`, closed by R8 (`blockRule8_one`); `17` has every consecutive ratio below 9 and is the scale-free hole `ArrBoundedCovered8 9`, with the finite cover not built. The owner's statement is that they are one arrangement. That identification is the content of the owed work.

**Consequence.** The map's active line is the finite cover; Q9 (the C1-shape) is read as a sub-case of it (a cluster flank opening in `c`'s band run is a class-1 grid instant through `e` with step `≥ c/7`; whether `GridClass8`'s certificate form is what a free opening gives is unchecked). The hand-off reading is paused. Next: a design of the work (the equivalence under which `1…7, 17` and `1…7, 10¹⁰` coincide; finiteness of the classes; the certificate per class), for the owner's approval before any run.

## E271 — 2026-10-02 — design: the finite cover (`docs/n8/FINITE_COVER_DESIGN_v1.md`), for the owner's approval

**Map:** v4 §4 Q8, Q9; §2 F; E145–E148, E256, E270. **No run.** A design written after reading, in the record, E119–E125, E145–E148, E216, E233–E256 and, in Lean, `ArrangementShapeN`, `RegimeSkeletonN`, `Order8SkeletonN`, `GridPairLawN`, `GridNeighbourhoodN`, `APNeighbourhoodN`, `TwoBlockN`, `FastRunnerN`, `EndRunnerN`.

**Finding.** The record had already reduced "finitely many arrangements" to a statement: E145's types are defined by the landing, so finiteness is by construction and "every arrangement has a type" is the conjecture (graded `[reasoned]` there); E146 showed the lap-1 composition predicts the landing cluster in at most 55.17%; **E147's recursion** (split at the largest gap, the full landing is the fast group's own landing in 42,013 of 42,013 in the band and 102,652 of 103,355 above 9) left one condition, that the slow group is clear at a lonely instant of the fast group, which is **E118's C1 statement** (E256: three routes meet there). So the finite-cover work is the C1 statement in full generality, uniform in the distance between the groups. In Lean, `1…7, 10¹⁰` (R8, `blockRule8_one`) and `1…7, 17` (the scale-free hole `ArrBoundedCovered8 9`, "the finite cover not built") are in different proved cases; the owner's statement is that they are one arrangement.

**Design.** Speed-only types (E145's definition without the landing); the recursion step for a block of one uniform in `X`; then blocks of two to six; then the exhaustiveness lemma beside `ArrangementShapeN.reduction_iff`. First proposed run: `{1,…,7, X}` through the cascade, for `X` from 8 to a few thousand and near `10¹⁰`. Decisions for the owner are listed in §6 of the design. Nothing is started.

## E272 — 2026-10-02 — owner: start again from the conditions; the derivation `docs/n8/ARRANGEMENT_CONDITIONS_v1.md`

**Owner:** *"Ok, lets start again. I want you to logically think of the conditions that restrict the arrangement space. The cascade shows how the reduction work out but I think you need to understand why it works. It works because the arrangements are not free and view from the perspective of ap/grid there are only so many different arrangments. Any evenly spaced arrangement, small or large relates directly to AP. So then what are the other types of arrangement clumps with outliers, but clumps if too evenly spaced becomes AP plus grid to capture the outlier. You need to reason this through"*

**Map:** v4 §4 Q8, Q9; E270–E271. **No run;** a derivation in the framework's objects, every non-Lean step marked `[reasoned]`.

**What it says (details in the file).**
- The conditions in the order they cut: order, scale, circle (all in Lean: `ArrangementShapeN`); the infinite grid (a reading matters only through its residue mod 8 against the instant's scale and its deviation; at the class-1 instant a whole reading is blocked iff `≡ 0 mod 8`); tightness at eight (the AP, an exact regular octagon at `1/8`, is the one configuration with no slack).
- A reading against a scale is **free** (`|ε|L ≳ 1/4`: the window outlasts the walker's block, `|ε|` the drift per opening, `L` the openings the window holds), **locked** (`|ε|L ≲ 1/4`: it keeps one slot, the residue `A mod 8`), or **between** (the hand-off). The residue and the sign are discrete; `|ε|L` is the one real quantity and it is bounded on both sides. The size of a far reading enters only through `L` and `ε`.
- Types: evenly spaced is the AP (any scale; whole extra laps invisible: the complete grid); a clump of at most six is a lower order with slack at least `1/56`, its outliers free or locked; a clump too evenly spaced is an AP at its own scale and captures its outliers by its grid; an irregular clump has slack for its outliers; several clumps by the largest-gap recursion (E147).
- `{1,…,7, X}`: an AP and an outlier captured by its grid; `X = 17` is residue 1 (an edge, lonely at `1/8`), `X = 10¹⁰` is residue 0 with both edges occupied (the pinned pair; an exact multiple of 8, `ε = 0`, locked for ever on the AP's own grid, so the isolation leaves that grid). One arrangement type, two residue cases; the size of `X` never adds a case.
- Finite (by the reasoning): clumps, residue and sign per scale, grid class. Not shown finite: the drift quantity `|ε|L` on `(0, 1/4)` and several walkers locking and unlocking in turn (the hand-off), which is E118's C1 statement; E266 derived the locked classes, E268 found at most three of six flanks shadowed in any population read.

**Consequence.** Proposed next (not started): take the speed-only classification of the file's §3 as the object, state the recursion step for two groups at adjacent scales with the residue as the only datum, prove it for a block of one for every `X`, then read the hand-off as a single walker's partial sweep (`|ε|L ∈ (0, 1/4)`) before several walkers. The owner's corrections to the reasoning come first.

## E273 — 2026-10-02 — design: many arrangements through the cascade, to read whether lap and deviation change the mechanism

**Owner:** on E272: *"Wait does the drift quantity actually flow as a requirement? Or are you adding that because it actually needs to be there?"*; and *"You try and make as many different arrangements as you can and you will see they all get simply reduced by the cascade instantly no searching. Its not a different mechanisim for any arrangment, its the same one because there are not true infinite amount of arrangements, just a continuous arrangment which is handled by the deviation."*

**Map:** v4 §4 Q8; E145–E148 (types), E233–E243 (the holes: one structure), `ARRANGEMENT_CONDITIONS_v1.md` §2. M2 class (d), a map run: derivation checks and the oracle check only; output is read, not scored.

**What the question is.** E272's quantity `|ε|·L` (drift per opening times openings in the window) is the deviation read at an instant of lap `K`: at the instant `(8K+1)/(8e)` a reading that deviates from its grid point by `δ` (in grid steps) is displaced by about `K·δ`. It comes from the infinite grid and the deviation (not added), and it is in Lean as the neighbourhood radius `2ρ(14W + 21) ≤ 1`, which shrinks as the laps `W` grow (`GridNeighbourhoodN`). Whether it is a **requirement** of the proof is the owner's question. If the lap is invisible, as the owner holds, the landing's lap `K` should stay low however large `W` is and however large the deviation (up to the neighbour's gap), and the radius shrinkage in the Lean theorem would be an artefact of its bounds. If `K` grows with `W` or with the deviation, the quantity is real.

**Families** (subject = the slowest runner, by `EndRunnerN`; readings are the other speeds minus the slowest; exact integers and fractions; seeded):
- F1 random speeds (scale `10⁶`).
- F2 AP at step `g = 10⁶` with deviations `|e| ≤ ρg`, `ρ ∈ {0.01, 0.1, 0.3, 0.45}`.
- F3 complete grids with laps: residues a permutation of 1…7, `(r + 8N)·g` with `N ∈ [0, W]`, `W ∈ {10, 10³, 10⁶}`, deviations `ρ ∈ {0, 0.01, 0.1, 0.3, 0.45}`.
- F4 a clump of 1 to 6 near-even readings (AP at scale `g`, deviation `ρ`) and the other readings as outliers at scale factors `10, 10³, 10⁶, 10⁹` above it, residues random, including exact multiples of 8.
- F5 two and three clumps at ratios `10 … 10⁶`.
- F6 several readings `≡ 0 (mod 8)` in the grid's units (doubled and captured slots), with and without deviation.

**Recorded per arrangement:** the cascade from the bound (moves, setters), the landing's lap `K` (`8·h·t* = 8K + 1`, `h` the last setter; `K = 0` at the bound) and `R* = 8·d_min·t*`.

**Checks (forced):** the landing is lonely (exact); the landing equals the least clear opening computed without the cascade for the first 200 of each family (A.9).

**Read, not scored:** the maximum of moves, `K` and `R*` per family and per `(W, ρ, factor)` cell, and every arrangement above any bound that appears, listed. A rise of `K` or the moves with `W`, `ρ` or the factor is the finding; a flat maximum is the finding the owner predicts. No rate, share or coverage is stated.

## E274 — 2026-10-02 — many arrangements through the cascade: moves and `R*` do not grow with laps, deviation or scale ratio; the drift quantity is a coordinate, not a requirement

**Map:** v4 §4 Q8; E273 run as designed. Script `LonelyRunner/experiments/nN/redo/many_arrangements_v1.{py,out}`; exact; 74 cells of 300, about 22,000 arrangements.

**Checks: 0 failures.** Every landing is lonely (exact); for every fourth cell's arrangements with a small enough opening count, the landing equals the least lonely opening computed without the cascade (A.9): 0 mismatches.

**Result (maxima per family; each cell's maximum is in the `.out`).**
- F1 random speeds: moves ≤ 7, `R* ≤ 2.66`.
- F2 AP with deviation `ρ` of 0.01, 0.1, 0.3, 0.45 of the step: moves ≤ 11 (at `ρ = 0.01`; 11, 11, 9, 8 down the list), `R* ≤ 5.02`.
- F3 complete grids with laps `W ∈ {10, 10³, 10⁶}` and `ρ ∈ {0, …, 0.45}`: moves ≤ 8, `R* ≤ 3.00`, with no rise in `W` or `ρ`.
- F4 clump of 1, 3 or 5 near-even readings with outliers at scale factors 10 to `10⁹`, deviation to 0.3, residues random (including exact multiples of 8): moves ≤ 13 (one case, `(1, 0.1, 10³)`), otherwise ≤ 9; `R* ≤ 2.12`.
- F5 two and three clump hierarchies at ratios 10 to `10⁶` (scales to `10¹²`): moves ≤ 8, `R* ≤ 1.12`.
- F6 two to four readings `≡ 0 (mod 8)` in the grid's units, with deviation to 0.3: moves ≤ 9, `R* ≤ 3.13`.
In every family the isolation lies in the slowest reading's first block (`R* ≤ 7`; the maximum anywhere is 5.02) and takes at most 13 moves. `R*` is about 1.000 in the clump-and-outlier families (the bound or one to a few moves from it).

**A flaw in E273's design, found on reading.** The landing's lap `K` (`8·h·t* = 8K + 1`, `h` the last setter) was meant to test whether the lap matters. It cannot: when `R* ≈ 1`, `K ≈ h/(8·d_min)`, the ratio of the setter to the slowest reading, so `K` grows with the scale ratio by definition (up to `6·10¹²` in F5) and says nothing about complexity. The measures that can test it are the move count and `R*`, and both are flat.

**Reading.**
- **The drift quantity.** `|ε|L` flows from the infinite grid as a coordinate (a deviation `δ` displaces a reading by about `Kδ` at lap `K`; it is the radius `2ρ(14W + 21) ≤ 1` in `GridNeighbourhoodN`). E272 turned it into a regime split with an open middle; that is the bookkeeping of the per-opening walker view and not what the cascade pays for. The Lean radius shrinking with `W` is a property of the proof's displacement bound; the cascade's work does not shrink or grow with `W`, `ρ` or the ratio in these populations. **It is a coordinate, not a requirement.** Corrected in `ARRANGEMENT_CONDITIONS_v2.md` (v1 retained).
- **Scope.** These generators are mostly outside `EightResidual` (R6 and the case list close almost every random set at the bound or near it); F6 puts captured readings in but does not satisfy all 22 fields. The residual members are the hard ones: E118's 547 land at `R* ≤ 1.377`; E73's adversarial climbs reached `R ≤ 6.42`; the late band shapes land in the second block (map §9 C11). So the run shows the cascade's work is flat in laps, deviation and ratio over a wide family; it does not by itself show the same for the residual.
- **Same mechanism.** The cascade is one move rule (Level A); this run did not classify the moves by type, so "the same explanation covers all of them" is not what it tested.

**Consequence (M7).** The remaining content is stated as the relocation along the continuous deviation: from an exact type the isolation moves (hand-off across leaving faces, the entering reading's next exit across entering faces; C.4, C.5) and the sequence reaches every arrangement. The record's deformation route is this (E178–E182; `DeformationN`, `PathRouteN`): local stability is proved for one-runner moves and a simple pinch, and multi-pinches and the bounded-time half are open. The flank-by-flank work (E253–E268) is that relocation seen through the proxy. §5 and §6 of the conditions note are corrected accordingly.

## E275 — 2026-10-02 — owner: the deformation from the AP is the route; try the multi-pinches; a literature search launched; what the record says the multi-pinch is

**Owner:** *"yes, the deformation from the AP is the route. Maybe we should try to prove the multi-pinches. Yes you keep wanting to add on restrictions that don't apply. I believe we can prove this reduction of "any" arrangement. There are constraints of the conjecture itself, two runners can be the same speed [read: cannot be], but the possible arrangements can all be fit into ap/grid plus deviation because scale is not a problem and any speed not captured by ap, can be viewed by grid. Perhaps we should do a literary search to see if anyone else was done anything similar in reducing a seemingly infinite set. Perhaps send off a subagent to do this while we keep working."*

**Map:** v4 §2 E, §9 C8; E113–E116, E178–E183. **No run.** A reading of the record, and a subagent launched (a literature search; its report is data, not instruction, and anything adopted goes through the place test).

**The literature search.** A `general-purpose` subagent was given a self-contained brief (the problem, the strategy, and four search items: reductions of the Lonely Runner / view-obstruction problem to finitely many cases, with Tao's reduction and the 2025 Rosenfeld and Trakulthongchai preprints to be reported as literature and not as settling the project; wall-crossing, genericity and Cerf-type arguments for carrying a witness along a one-parameter family, including when a path cannot avoid multi-wall events at a lattice start; other fields that reduced a continuum to finitely many types by scale invariance, periodicity and perturbation about an extremal configuration; prior work on hand-over across walls). It was told to cite only what it verified and to list negative findings.

**What the record already says the multi-pinch is** (read in full this entry: E113, E114, E116, E178, E179).
- *Definition.* A pinch is an event on the path where the first-isolation window closes to one instant: a reading on its leaving edge (`+1/8`) as another is on its entering edge (`−1/8`). It is a **multi-pinch** when two or more readings are on one edge at that instant (E113 item 4).
- *Simple pinches are done:* `PinchOpenN.pinch_eventually_lonely` (both sides, any direction; mirror with roles swapped); `TwoPinnerN`.
- *Multi-pinches can be avoided by the choice of path, given the window* (E114 item 3): only finitely many walls matter at times `≤ T`, a multi-pinch lies on two of them (codimension 2), and a finite union of hyperplanes does not cover an open cone; route through a generic rational point. **So the multi-pinch is not an obligation separate from the window (B).**
- *On the straight path from the AP* (E178, three populations, 16,881 events): 301 multi-pinches (232 + 0 + 69); **every event after `s = 0` has another open window** (13,737 of 13,737); the only unprotected event is `s = 0` itself, a simple pinch, covered by the AP's neighbourhood. The mirror is never the replacement (0 of 10,796). E179: the protectors are a relay at named places, not the AP's windows carried along. The relay condition (whenever an open window is about to die another is open or born first) is unproved.
- *What the deformation cannot do* (E116, O5; a finding of the record, with a positive control): between two whole-number points the continuum is lonely natively (`OneFreeN.lonely_of_one_free_eight`, E60 `lonely_of_off_lattice`: order seven plus one reading off the lattice of the others, no density); at a lattice point the window is exactly that point's loneliness (a non-lonely lattice point has nearby instants escaping like `1/ε`). So **closedness of the deformation is the window, which at lattice points is the whole-number statement**, and the multi-pinch carries openness only.

**What a proof of the multi-pinch case would be** (derived from E113–E114; not done): at a lonely whole-number `X₀` whose lonely instant `t₀` has leaving set `Λ` and entering set `E`, with `|Λ| ≥ 2` or `|E| ≥ 2`, a perturbation in direction `w` shifts each leaving reading's departure and each entering reading's arrival to first order. The window reopens at `t₀` iff `max_Λ(departure) ≤ min_E(arrival)`; the mirror reopens iff the reverse system holds; with two readings on one edge both can fail (`τ_a < τ_b < τ_a′`). Then another lonely instant of `X₀` (or one reached by a hand-off) has to be favourable. The statement (A) of E113 is that this never fails for lack of any instant: no lonely whole-number arrangement has only multi-pinch lonely instants (0 of 346,104 sets with readings `≤ 24`).

**Proposed next (not started; for the owner's go-ahead).** Read the 301 multi-pinches of E178 (scripts `deform_pinch_v1`, `deform_protect_v1`): for each, `(|Λ|, |E|)`, the sign pattern of the first-order shifts, and the relation of the protecting window to `t₀` (the mirror, the recurrence of the doubled pair at multiples of `1/(d_a − d_a′)`, an AP class window, a window born at the same parameter), to see which instant is favourable and why. Derive first (M8), then check.

## E276 — 2026-10-02 — the literature search returned; what is verified, and what it says about this programme

**Map:** none — housekeeping; the report is saved as `docs/n8/LITERATURE_REDUCTION_SEARCH_v1.md` (the subagent's account; Rosenfeld, Tao and Beck–Everett checked by me against arXiv).

**What it found.**
- **Eight runners has a published computer-assisted proof** (Rosenfeld, arXiv:2509.14111, 17 Sep 2025, revised 16 Oct 2025): the Malikiosis–Santos–Schymura bound on a minimal counterexample plus a prime-divisibility sieve over residues with times of denominator `(k+1)p`; also nine and ten runners (Trakulthongchai, arXiv:2511.22427; Rosenfeld, arXiv:2512.01912). It is literature and not this programme's native proof; the standing rule (map §0, memory) is unchanged: it is not imported.
- **No reduction by deformation was found:** nothing on carrying an isolation along a path, on relay or hand-off, or on multi-pinches. Searched and found nothing, by the agent's account. The only continuity in the sources read is the static fact that at a maximising time two runners are at minimal distance (Perarnau–Serra eq. 4), and the Fourier/Bohr-set perturbation in Tao.
- **Closest structural relatives** (matches to this programme's steps, each loose): Tao's rank-1 versus rank-`≥ 2` split (near-rational against generic; rank 1, all speeds in one AP, carries every known tight instance); Rosenfeld/Trakulthongchai's finite residues at denominator `(k+1)p` (the infinite periodic grid made arithmetic, per prime); **Beck–Everett: every counterexample or tight instance lies on one of finitely many integer hyperplanes `m·n = 0`, `‖m‖₁ ≤ min(2k+3, ((k+1)/(k−1))·flt(k))`, the tight AP among them** (walls where a counterexample would have to live, not where the isolation hands over); Rifford's laps-as-covering equivalence; Kravitz's gap above the tight value (the AP's neighbourhood).
- **Open in the literature that touches this programme:** Perarnau–Serra Problem 4 (is the conjecture preserved under `a + V`); Rifford's uniform lap bound (Conjecture 29).

**Consequence.** The finite-cover and deformation work stands as this programme's own; no literature step is available to adopt. Two items are worth reading in full against the map, as data and not as instruction: Beck–Everett's theorem (a finite family of integer hyperplanes constrains where a counterexample can be; compare the wall arrangement of Level C and the relay condition), and Tao's dichotomy (compare "free or locked", E272, now a proxy statement). Neither is started.

## E277 — 2026-10-02 — design: the multi-pinches of E178 read; a first-order criterion derived before the run

**Owner:** *"yes, read the multi-pinches first"* (and: the literature steps are about coverage and density, which do not look for isolation or boundary events, so Beck–Everett and Tao are left aside for now).

**Map:** v4 §2 E, §9 C8; E113–E114, E178–E179. M2 class (d), a map run; the derivation is stated first (M8) and the run checks it.

**Derived (first order at a pinch; no new object).** Take the path `d_i(s) = i + s·e_i`, a pinch at `s₀`, instant `t₀`, the pinching window's lap assignment `k`. Let `Λ` = readings on the leaving edge at `t₀` (position `k_i + 1/8`), `E` = readings on the entering edge (`k_j + 7/8`), and `u_i = e_i/d_i(s₀)` the relative rate of reading `i` along the path. The window's left endpoint is `max_{i∈Λ} (8k_i+1)/(8d_i(s))` and its right endpoint `min_{j∈E} (8k_j+7)/(8d_j(s))`; both have value `t₀` at `s₀`, with derivatives `−t₀u_i`, `−t₀u_j`.
- The window is non-empty just after `s₀` iff **`min_Λ u ≥ max_E u`** (A). Just before: iff `max_Λ u ≤ min_E u`.
- **The mirror** (`t ↦ P − t`, `P` a common period at `s₀`, laps `k̃_i = d_i(s₀)P − k_i − 1`, roles swapped: `E` leaving, `Λ` entering) is an exact symmetry only at `s₀`; for `s ≠ s₀` it is shifted by `(d_i(s) − d_i(s₀))P`, which is what breaks the tie. Its window is non-empty just after `s₀` iff **`min_E u ≥ max_Λ u`** (B).
- **Simple pinch** (`|Λ| = |E| = 1`): (A) says `u_a ≥ u_b`, (B) says `u_b ≥ u_a`: at least one holds. This is E113's "exactly one of `t₀`, `1 − t₀` opens" (`PinchOpenN`, `TwoPinnerN`), now with its reason.
- **Multi-pinch:** (A) and (B) both fail exactly when the `u`-values of `Λ` and of `E` **interleave** (`min_Λ u < max_E u` and `min_E u < max_Λ u`), which needs `|Λ| + |E| ≥ 3`; e.g. `u_a < u_b < u_{a′}` with `Λ = {a, a′}`, `E = {b}`. In that case neither `t₀` nor its mirror reopens on that side and another lonely instant has to be favourable.
- A direction `w` that separates the two ranges at every multi-pinch met would make every pinch passable; the interleaving set is open (not a codimension), so it is not avoided by genericity; E114's avoidance is by the choice of path through a generic point, which avoids multi-pinches altogether, and not by orienting the path at them.

**Run (same populations and path as E178; scripts `deform_pinch_v1`/`deform_protect_v1` reused).** For every event with a multi-pinch: `(|Λ|, |E|)`, the reading indices, the `u` values; the exact test of (A) and (B) (the pinching assignment `k` and the mirror assignment `k̃` evaluated by exact `feasible` at `s₀ ± δ`, `δ = 10⁻⁹`) against the criterion; for each interleaving event (neither reopens), the protecting windows (positive width at `τ`): AP-origin (`feasible` for the AP with the same laps), earlier or later than `t₀` in `R = 8·d_min·t`, containing the mirror `P − t₀`, at a recurrence time of a doubled pair (`(τ_p − t₀)·(d_a − d_{a′}) ∈ ℤ`), otherwise. Every protector not in a listed class is read individually (M3).

**Checks (forced):** the criterion agrees with the exact test at every non-tied event (ties listed separately, since first order does not decide them); `c`-in-the-way style checks of E178 (the oracle: cascade landing = first component) carried over; the pinch is single-point at `τ`.
**Not read:** counts as rates. The multi-pinches are listed by place.

## E278 — 2026-10-02 — the shape of Tao's reduction, translated to native objects (no parts imported)

**Owner:** *"Tao's reduction is proved right. I wonder if we can see where the shape my translate without importing any of the parts, or any other infinite reduction"*

**Map:** v4 §4 Q8, Q9; E276 (the literature report). **No run.** A reading of a described shape against native objects. The description of Tao's argument is the subagent's (`LITERATURE_REDUCTION_SEARCH_v1.md`); only the abstract (the reduction to integer speeds of size `n^{O(n²)}`) was checked against arXiv:1701.02048. The proof was not read; nothing of its machinery (additive combinatorics, Freiman homomorphisms, Fourier or Bohr-set estimates) is used.

**The shape (as reported).** (1) Induction on the number of runners. (2) A dichotomy: the speeds lie in one arithmetic progression (rank 1) or not. (3) If not, a projection collapses two readings into one, so the lower order applies with extra margin `1/(n−1) − 1/n`. (4) Stability: un-collapsing moves the clear instant by less than the margin.

**Native counterparts.**
- Induction on runners: orders 3–7 native; R8 (`FastRunnerN`), `FastPair8`, clumps as lower orders. Proved.
- Collapse, lower order, step inside the margin: `MergeSixN`, `SteppingN` and order seven at `1/7` (margin `1/56`) in `RealEightN`'s real-to-whole reduction. Proved. So the real-to-whole reduction (N2) already has this shape.
- Stability for a tight clump: `TrainCollapseN` (`N ≥ 56m`; `56 = 7·8`, the margin's denominator). Stability for separated groups: `SplitChainN`, `SyncBlockN`. Proved.
- Rank 1: the AP and grid neighbourhoods, the complete grid, R6 at `q = 8`. Proved.
- **Not available:** a uniform choice of the collapse such that its error is below the margin. E248 found the `f = 6` hole's blocks between `TrainCollapseN`'s regime and nested windows, with no uniform constant for either.

**The statement the shape suggests** `[reasoned; not examined; to prove]`: for every arrangement, either some collapse of two adjacent readings or clumps into one has error below the lower order's margin (so the lower order with slack carries it), or no such collapse exists and the readings are spread evenly at every scale, so the arrangement lies in the AP/grid neighbourhood. This is the owner's "clumps, if too evenly spaced, become AP plus grid to capture the outlier" stated as a dichotomy with a quantitative first branch.

**A difference to keep.** In the reported argument the finite set is integer tuples up to a height bound, obtained by estimates. Here the infinite periodic grid does that job: beyond a clump's own scale only the residue mod 8 and the deviation matter. And in place of an error estimate the isolation is followed as the collapsed pair is turned back on (the deformation); the un-collapsing of a doubled pair is the doubled-slot step of the multi-pinch (E277, running).

**Consequence.** The open region (E248) is where the first branch has no uniform constant; the dichotomy above, with the constants from `TrainCollapseN` (`56m`) and nested windows (E231's `35m/3`), is the candidate statement. Not started. (Numbering: the multi-pinch results will be the next entry; its script header says E278.)

## E279 — 2026-10-02 — owner: no evenness is needed, only that any arrangement can be locally arranged in an AP/grid style; the local types are finite and the lap never enters

**Owner:** *"No we don't need to show they are even spread, merely that any arrangement can be locally arranged in a ap/grid style"* (on E278's dichotomy, whose second branch asked for evenness at every scale: withdrawn).

**Map:** v4 §4 Q8; E216 (the class instant), E272–E274. **No run;** a derivation from E216's object, `[reasoned]`, not checked beyond the arithmetic below.

**Derived.** Take the grid through a reading `a` with step `s = d_a/n_a`. Every reading is `d = s(n_d + ε_d)`, `n_d` the nearest integer, `|ε_d| ≤ 1/2` (automatic, at any scale). At the class-`c` instant `t = c/(8s)` (`c` a unit mod 8, `c·n_a ≡ 1`, so `a` is on its leaving edge) reading `d` sits at `c·n_d + c·ε_d` in eighths (since `d·t = s(n_d + ε_d)·c/(8s)`). So:
- the deviation is scaled by `c ≤ 7`, not by `n_a` or the lap; this is why E274 found nothing depending on laps or scale ratios when measured at the grid's own scale;
- at class 1, reading `d` is clear iff its residue `n_d mod 8 ≠ 0`, and a residue-1 reading has `ε ≥ 0`, a residue-7 reading `ε ≤ 0` (residues 2 to 6 are always clear): **the condition depends only on residue and sign, not on the size of the deviation**. At other classes `c ≤ 7` the size enters up to the factor `c`.
- So the local types (residue, sign per reading, and the class) are finite, with no height bound and no estimate.

**What it does not give.** Which grid `(a, n_a)` to read the arrangement on is free, and finding one whose type vector is good is Theorem 6.15 (every opening is the class-1 instant of a grid), the obligation. The content is therefore the carrying across walls: the type vector changes only where a reading crosses an edge or a residue boundary (a pinch); the finite local rules at a wall (hand-off on a leaving face, next exit on an entering face: Levels A–C, C.4, C.5) carry the isolation; a multi-pinch is a wall where several readings change type at once. E278's dichotomy and its evenness branch are withdrawn.

**Consequence.** The work is the carrying rule at every wall including the multi ones (E277, running), not a dichotomy or a bound. To confirm with the owner: that this is the intended sense of "locally arranged in an AP/grid style".

## E280 — 2026-10-02 — the multi-pinches read: the first-order criterion holds exactly; interleaving is common; every such event has a margin window, so the multi-pinch matters only at a tight arrangement

**Map:** v4 §2 E, §9 C8; E277 run as designed. Script `LonelyRunner/experiments/nN/redo/multi_pinch_read_v1.{py,out}` (same path, populations and event location as E178; its header says E278, the number was taken by the entry before it).

**Check: the derived criterion (E277) agrees with the exact test.** The pinching window and the mirror window evaluated by exact `feasible` at `s₀ ± 10⁻⁹` against "(A) `min_Λ u ≥ max_E u`, (B) `min_E u ≥ max_Λ u`" (and the backward forms): Case B 922 comparisons, Case C 270, **0 mismatches**; 6 tied events in each (first order does not decide them; listed in the `.out`'s counts, not read).

**The multi-pinches** (same events as E178):
| population | events | simple | multi | by `(|Λ|, |E|)` |
|---|---|---|---|---|
| Case B, every 100th | 8,900 | 8,668 | 232 | (2,1) 128, (1,2) 74, (2,2) 17, (3,1) 8, (3,2) 3, (2,3) 2 |
| late band shapes, every 10th | 2,079 | 2,079 | 0 | none |
| Case C sample | 5,902 | 5,833 | 69 | (2,1) 34, (1,2) 31, (2,2) 2, (3,1) 2 |

**On the lost side** (death: forward; birth: backward):
- Case B: births, neither the instant nor its mirror reopens 118, the mirror reopens 7; deaths, the mirror reopens 78, neither 29. Case C: births neither 11; deaths mirror 56, neither 2.
- So **interleaving** (neither reopens, the first-order unfavourable pattern) occurs in 147 of 232 (Case B) and 13 of 69 (Case C) multi-pinch events: it is common, not exceptional. In the others the mirror reopens, as at a simple pinch.

**Every interleaving event has a positive-width window at `τ`:** 0 of 147 and 0 of 13 without one. The protector windows (Case B 2,447; Case C 1,493): later than `t₀` in `R` in all; at a recurrence time `t₀ + j/(d_a − d_b)` of a doubled pair on one edge in 673 and 376 (the rest not); an AP-origin window in 93 (Case B); none earlier than `t₀`; **no single class** (note: a window containing the mirror `P − t₀` cannot appear in this list, because at `s₀` the mirror window is a single point, not positive width).

**What this says** (`[derived criterion; VERIFIED — these samples]`):
- At a multi-pinch the instant and its mirror can both fail to reopen (the interleaving of the relative rates `u`, only possible when `|Λ| + |E| ≥ 3`), and that happens often; but in no event read is it decisive, because the arrangement at the event is **not tight**: it has a lonely window of positive width elsewhere, and openness there is margin openness (`eventually_lonely_of_margin`), not a pinch rule.
- This is E113's statement (A) seen from the other side. E113 found 6 of 346,104 sets (readings `≤ 24`) with no lonely interval, the tight instances and their rescalings, all with simple pinches. So the multi-pinch is a problem only at a **tight** arrangement (every lonely instant an isolated pinch), and the known tight arrangements have only simple pinches.
- So the carrying rule at a wall has two cases: a non-tight arrangement (a margin window exists: nothing to prove at the wall) and a tight one (a classification question). The multi-pinch is not an open step of its own.

**What a proof now needs** (not started): the statement **(T): a whole-number arrangement with no positive-width lonely window (tight) has only simple pinches** (equivalently, no tight arrangement has a doubled-edge pinch as its only lonely instants). `[VERIFIED — readings ≤ 24, E113]`. A route to (T): characterise the tight arrangements. The literature report (E276) notes Beck–Everett's theorem is about exactly this object (a tight instance, lon `= 1/(k+1)`, lies on a hyperplane `m·n = 0` with small `‖m‖₁`, the AP among them); the owner has set the literature aside as coverage and density, and the object here, the tight arrangement, is the pinch-only one; whether its statement (not its Fourier proof) is of use is the owner's call.

## E281 — 2026-10-02 — owner: it is not the conjecture itself; existence may not be necessary; do walls and hand-off belong, or are they imported? E279's closing bullets withdrawn

**Owner** (on E279's "What this does and doesn't give", pasted): *"Its not the conjecture itself. I've never been sure existence is necessary, you have argued that either existence or exhibit is necessary. Dos it really need walls and handoff? Or is that imported?"*

**Map:** v4 §4 Q8; E145, E230, E279–E280. **No run.** A reassessment.

**Withdrawn:** E279's "finding one whose type vector is good is the conjecture itself" and "the content is the carrying rule at every wall". The first is true only for an unrestricted search over grids (Theorem 6.15, `doors_agree`: "some opening of some reading is lonely" is the conjecture); with the grid, class and instant determined by the readings it is a construction, which is the owner's picture. The second took "deformation" literally as following the isolation through pinch events.

**On existence.** The statement proved is an existence statement, but a proof need not contain a separate existence step: a total rule from a base case with the invariant preserved at each step (transport) is a third form besides existence and exhibit (E230: *"induction, construction"*). Its weak point is totality: for the cascade's relay (the entering reading's next exit) totality is termination, the conjecture in disguise (F4); for a finite table of local types it is a finite check.

**On walls and hand-off.** Derived in the record from the cascade's own definition (E113–E186, Levels A–C), not imported; not shown necessary. They are the language of following an isolation along a path. In a type-and-cell architecture each cell has its named instant (as `gridT` in `GridNeighbourhoodN`) proved lonely on its own region, and walls are only cell boundaries, relevant to exhaustiveness; E280 found a margin window at every multi-pinch read, so no rule at the wall was needed away from tight arrangements.

**What that architecture needs:** (1) types defined from the speeds alone, not from the landing (E145: types defined by the landing make "every arrangement has a type" the conjecture); (2) a named instant per type, loneliness proved locally; (3) exhaustiveness.

**Proposed test (not run):** at the bound the local type is the residue mod 8 and sign of `ε` of each reading on the grid through the slowest reading (E279). Does that type alone fix the isolation's role (setter rank; bound or not) on the E274 families and the residual members? If it does, a table works without walls; if the isolation depends on ratios beyond the type, the grid through the captured reading is part of the type, and whether that chain is finite without being defined by the outcome has to be examined.

## E282 — 2026-10-02 — owner: existence is the grid's global isolation (φ(8)); an arrangement is a deviation from it; run the local-type test (design)

**Owner:** *"I think existence is already proven by the phi(n) law/grid global isolation. That is already proved, now we are saying any arrangement is just a deviation from that. Move the speed and you move the isolation point from the global ideal to a local isolation event."* And: *"Ok yes"* to the local-type test of E281.

**Map:** v4 §4 Q8; E279, E281; `GridNeighbourhoodN`. M2 class (d), a map run.

**Frame.** The complete grid (residues mod 8 all different) is lonely at the class-1 instant for every runner, laps invisible (`GridNeighbourhoodN`, the φ(8) law, proved). The question is what a deviation does to where the isolation sits. The test reads, at an instant, each reading's rounded position as a grid point plus deviation.

**Definitions (exact).** At instant `t`, `P_d = 8·d·t`, `n_d = ⌊P_d + 1/2⌋`, `ε_d = P_d − n_d ∈ [−1/2, 1/2)`, `r_d = n_d mod 8`. Status of reading `d`: **ok** if `r ∈ {2,…,6}`, or `r = 1` with `ε ≥ 0`, or `r = 7` with `ε ≤ 0`; otherwise bad (**r0**: captured; **r1−**: just inside the leaving edge; **r7+**: just past the entering edge). The type `τ(t)` is the vector of the seven statuses. The bound is `t = 1/(8m)`, `m` the slowest reading, so `P_d = d/m`.

**Forced (derived; checked):**
- F1: `d` is clear at `t` iff its status is ok (`‖d t‖ ≥ 1/8`), so the set is lonely at `t` iff `τ(t)` is all ok. At the bound this is the grid through the slowest reading at class 1.
- F2: a bad reading's remaining distance to its exit, in eighths, is `ρ = 1 − ε` (r0), `|ε|` (r1−), `2 − ε` (r7+); its exit is at `t + ρ/(8d)`; the first move's setter is the bad reading maximising `ρ_d/d` (Level A.3).

**Question.** On the E274 families (same seeds) and the 5,978 residual members (`members_5978_v1.json`): does `τ(bound)` fix the first setter's rank, the number of moves, the next type `τ(t₁)`, the landing's setter rank? Groups by `τ(bound)`: purity of each outcome; the mixed groups listed with the data that separates them (M3). **Not read:** counts as rates; a grouping is not offered as a classification (E145: a type defined by the landing is circular).

## E283 — 2026-10-02 — the local type at the bound fixes whether the bound is lonely and, for one bad reading, the first setter; it does not fix where the isolation lands

**Map:** v4 §4 Q8; E279, E281–E282. Script `LonelyRunner/experiments/nN/redo/local_type_v1.{py,out}`; exact; 28,056 arrangements: the E274 families (same cells and sizes; F1 300, F2 1,200, F3 4,500, F4 10,459, F5 2,700, F6 2,619) and the 5,978 residual members.

**Checks: 0 failures.** F1 (a reading is clear at `t` iff its status is ok, so lonely iff `τ(t)` is all ok) on every arrangement; F2 (the first setter is the bad reading maximising `ρ_d/d`, with `ρ = 1 − ε`, `|ε|`, `2 − ε` for r0, r1−, r7+, and its exit time `t + ρ/(8d)` equals the cascade's first instant).

**At the bound (the grid through the slowest reading, class 1):**
- Lonely at the bound: F1 156 of 300; F2 605 of 1,200; F3 2,348 of 4,500; F4 4,542 of 10,459; F5 615 of 2,700; F6 1,381 of 2,619; **residual 0 of 5,978** (every residual member has 1 to 6 bad readings: 1 in 1,469, 2 in 2,396, 3 in 1,506, 4 in 507, 5 in 90, 6 in 10).
- The 18,109 arrangements not lonely at the bound fall in 1,240 distinct types `τ(bound)`.

**What the type fixes** (groups of at least 3 members; 561 groups, 17,227 arrangements):
- **the first setter's rank:** determined in 312 groups; by number of bad readings: `nbad = 1`: 18 of 18 (the single bad reading is the setter); `nbad = 2`: 63 of 135; `nbad = 3`: 193 of 346 (the rest need the magnitudes `ρ_d/d`);
- **the number of moves:** determined in 30 groups; **the next type `τ(t₁)`:** 21 groups; **the landing's setter rank:** 10 groups (37 arrangements). Even with a single bad reading, the landing rank is pure in 0 of 18 groups and the move count in 0 of 18.
- The largest mixed groups: `oooooo0` (the fastest reading captured, all others ok; 1,302 arrangements) lands at ranks 1 to 6 (6: 873, 5: 171, 4: 131, 2: 57, 3: 46, 1: 24) in 1 to 11 moves, with 30 distinct next types; `ooooo0o` (1,127): ranks 1 to 6, moves 1 to 8, 35 next types; `oooooo+` (920): 52 next types, moves up to 13.

**Reading.**
- The signs-and-residues type is exactly the information that decides good or bad at an instant (F1), and with one bad reading it names the first mover. Everything after the first move depends on **magnitudes and ratios**: the next positions are `P′_d = P_d + ρ_c·d/c`, so the next type depends on the comparison of the setter's displacement `ρ_c·d/c` with each other reading's slack to its status boundary. Those comparisons are thresholds in the continuous data: **the walls appear here as thresholds of the transition**, not as an import; they are bundled in the rule "exit the maximiser of `ρ/d`, re-read the type", which is the cascade's step.
- In the single-bad-reading groups (a captured outlier, the others ok: the `{1…7, X}` family and its relatives) the others' `ε` are often exactly 0 on an edge, so the comparison is of `ε` (0 or tiny) with the outlier's displacement `ρ·d/X`: the deviation's size relative to the ratio enters the route, though not the move count (E274).
- So a table indexed by the sign-type at the bound does not fix the isolation; the isolation is fixed by iterating the local rule, and its end (an all-ok type) is what remains to be shown for every arrangement. The owner's frame (existence is the grid's global isolation; an arrangement is a deviation) gives the all-ok type for the exact complete grid; what is asked of the deviation is that the relocation reaches an all-ok type.

**Consequence (M7).** Not the answer the table route hoped for (a role fixed by a finite type at the bound). Open items to read: in the single-captured-outlier groups what decides the landing (the comparison of the outlier's displacement with the edge readings' `ε`); whether the thresholds of the transition are finitely many kinds (each a comparison of one reading's slack with the setter's displacement) so that the chain's types are determined by an ordering of such comparisons rather than by the outcome.

## E284 — 2026-10-02 — owner: mover/exit and "bad reading" are proxies; the re-reading framing is a search; E283's closing paragraph withdrawn

**Owner** (on E283's summary): *"What mover what exit? Are these needed?"*; *"Bad reading? There was an arrangment where the cascade fails to find the isolation point? No then is this a proxy you are adding"*; *"This seems you are looking at like a search?"*

**Map:** v4 §4 Q8; E283. **No run.** A reassessment.
- **Mover, setter, exit** are Level A's terms for what the cascade does (the setter leaves the subject's slot last; its exit is the instant it leaves). They entered E283 because the test tabulated the cascade by local type. They are not needed by the owner's frame (the grid's global isolation, the arrangement as a deviation, the isolation displaced to a local event).
- **"Bad reading"** is the session's label for a reading in the subject's slot, or just on the wrong side of an edge, at the grid's class-1 instant. It is not a failure of the cascade: 0 of 28,056 arrangements failed; all 18,109 not lonely at the bound reached an isolation. E283's purity counts tested the hypothesis that a finite sign-type fixes the landing, not the cascade. The grouping by "bad" is a proxy added by the session.
- **Search.** "Re-reads until all-ok" and "the reason it always ends" is the termination framing (that or when it stops: memory `feedback_n8_cascade_is_the_oracle`, §6 F1). **E283's closing paragraph (what a proof must supply: the reason the re-reading ends; the open items about the chain's types) is withdrawn.**
- **What stands from E283:** the sign-and-residue type decides whether the grid's own instant is lonely (F1, exact); when it is not, the isolation's place depends on the continuous deviations and not on a finite table (a landing rank and move count not fixed by the type, 0 of 18 groups with one reading off). The object is the displacement of the isolation from the grid's ideal instant as a function of the deviations.

**Proposed (not run):** after reading `GridNeighbourhoodN`'s definition of `gridT` (the named instant: the max or min of the two class-1 neighbours' own openings, or the mirror class-7 instant), test on complete grids with whole laps and deviations beyond the proved radius `2ρ(14W + 21) ≤ 1` whether the named instant is still lonely and whether the isolation is still one of the named instants. No moves, setters or termination are used.

## E285 — 2026-10-02 — design: the named instants of the complete grid's neighbourhood, tested beyond the proved radius

**Owner:** *"yes run that test"* (E284).

**Map:** v4 §4 Q8; `GridNeighbourhoodN` (`gridT`, `grid_nbhd_lonely`, `grid_nbhd_exists`); E274. M2 class (d). No moves, setters or termination are used.

**The theorem (read in Lean, not rebuilt).** A complete grid: speeds `v_i = c₀ + u_i + e_i`, `u_i` integers with all residues mod 8 different, `|e_i| ≤ ρ`; `W` bounds `|u_i − u_j|`. For a subject `k`, `A` and `B` the runners with `u_A − u_k ≡ 1` and `u_B − u_k ≡ 7 (mod 8)`; `δ_j = v_j − v_k`, `D_j = u_j − u_k`. If `2ρ(14W + 21) ≤ 1` every runner is lonely at the named instant `gridT(D_A, D_B, δ_A, δ_B)`: with `t_A = D_A/(8δ_A)` (A on its leaving edge), `t_B = D_B/(8δ_B)` (B on its entering edge), for `D_A, D_B > 0` (subject the slowest): `t_A` if `t_A ≤ t_B`, else `7·t_B` (the mirror class). Other sign cases: max, min, or `7·t_A`.

**Run.** Subject = the slowest (`D > 0` throughout). Complete grids: residues of the other seven a permutation of 1…7, `D_i = r_i + 8N_i`, `N_i ∈ [0, N_max]`, `N_max ∈ {10, 10², 10³, 10⁴, 10⁶}`; deviations `ε_i` uniform in `[−ρ, ρ]` of a grid step (exact rationals, scale `10⁶`), `ρ ∈ {0, 0.001, 0.01, 0.1, 0.3, 0.49}`; 400 per cell. Let `q = η(14W + 21)` with `η = max |δ_j − D_j|` and `W = max D`: `q ≤ 1` is inside the proved radius (up to the factor 2 in the theorem's `ρ`), `q > 1` beyond.
Per arrangement (exact): (i) is `gridT` lonely; (ii) is the cascade's landing `t*` equal to `gridT`, one of the named instants `{t_A, t_B, 7t_A, 7t_B}`, or earlier than `gridT` (it cannot be later: the landing is the first isolation, A.9). Reported by decades of `q`.

**Checks (forced):** inside the radius (`q ≤ 1/2`, i.e. `2ρ(14W+21) ≤ 1` with `η ≤ 2ρ`) `gridT` is lonely in every arrangement (the theorem); the landing is never later than `gridT` when `gridT` is lonely; the landing is lonely (exact).
**Read, not scored:** where (in `q`) `gridT` first fails to be lonely; what the failures look like (M3); whether the landing, when it is not `gridT`, is a named instant.

## E286 — 2026-10-02 — the named instant of the complete grid stays lonely about 120 times beyond the proved radius, then fails; the cascade's landing is almost always earlier than it

**Map:** v4 §4 Q8; E284–E285; `GridNeighbourhoodN`. Script `LonelyRunner/experiments/nN/redo/named_instant_v1.{py,out}`; exact; 12,000 complete grids (30 cells of 400: `N_max` ∈ {10, 10², 10³, 10⁴, 10⁶}, `ρ` ∈ {0, 0.001, 0.01, 0.1, 0.3, 0.49} grid steps; subject the slowest). `q = η(14W + 21)`, `η = max|δ_j − D_j|`, `W = max D`; the theorem's hypothesis `2ρ(14W + 21) ≤ 1` is `q ≤ 1/2` here.

**Checks: 0 failures.** The landing is lonely in all 12,000; it is never later than `gridT` when `gridT` is lonely; **inside the proved radius (`q ≤ 0.5`) `gridT` is lonely in 2,008 of 2,008** (the theorem).

**By `q`** (n | `gridT` lonely | landing equals `gridT` | landing a named instant `{t_A, t_B, 7t_A, 7t_B}` | landing earlier than `gridT`):
- `q ≤ 0.5`: 2,008 | 2,008 | 38 | 38 | 1,970; `(0.5, 1]`: 216 | 216 | 9 | 9 | 207; `(1, 10]`: 699 | 699 | 15 | 15 | 684.
- `(10, 100]`: 1,126 | 1,090 | 23 | 24 | 1,089; `(10², 10³]`: 2,106 | 1,720 | 16 | 23 | 2,055; `(10³, 10⁴]`: 1,698 | 1,337 | 2 | 2 | 1,694; `(10⁴, 10⁵]`: 1,583 | 1,203 | 0 | 1; `(10⁵, 10⁶]`: 1,279 | 940 | 0 | 0; `(10⁶, 10⁸]`: 1,285 | 883 | 0 | 0.
- Moves at most 9 throughout.

**Reading.**
- **The proved radius is conservative.** `gridT` is lonely in every arrangement with `q ≤ 61.7` (2,923 of 2,923 up to `q = 10`, and every one of the first 1,126 to 100 except from `q = 61.7` on); the first failure is at `q = 61.7` (`N_max = 10`, `ρ = 0.1`, one move), about 120 times the proved bound. Failures then grow with `q` (e.g. at `ρ = 0.49`, 171 to 186 of 400 in each `N_max` cell; at `ρ = 0.001`, 1 of 400 at `N_max = 10⁶`); at no `q` is the failing share total (883 of 1,285 still lonely at `q` up to `10⁸`). No threshold at a fixed `q`: the same `q` can be lonely or not.
- **The named instant is an isolation, not the first.** The landing equals `gridT` in only a few percent even inside the radius (2,008 inside: 38 equal; 1,970 earlier). The cascade's first isolation lies earlier, because the other readings give earlier windows; `gridT` is the class instant of the unit grid, a witness near `1/8` in grid units. So "the isolation is one of the named instants" is true of the named instant as *an* isolation, not of the first.
- **What it says for the frame.** Where the deviation is small against the grid's step and laps, the global ideal's instant is displaced to a nearby local instant and stays an isolation (E286: out to `q` about 60, against the proved 0.5). Beyond that the unit grid stops being the right description (deviations of order half a step: `ρ = 0.49` is as far from the grid as an arrangement gets) and the isolation is elsewhere; the arrangement is then a small deviation from some other grid (through another reading, another divisor), not from this one.

**Consequence (M7).** The picture "move the speed and the isolation moves from the global ideal to a local event" holds as measured on the named instant over a region about 120 times wider (in `q`) than the Lean theorem proves; the Lean radius's shrinkage with laps is conservative. The question this leaves in the owner's terms: for an arrangement outside this region, which grid (through which reading, at which divisor) is the one it is a small deviation from, and for arrangements whose rounded residues collide (no complete grid) what plays the ideal's role. Not started.

## E287 — 2026-10-02 — owner: the failure is the proxy's, not the cascade's; first isolation is not needed; what a test is for

**Owner** (on E286): *"Failure of the bound but not the cascade right? So do you see what I mean. We keep using proxy and finding where that fails but the cascade doesnt..."*; *"This makes me made. Why does it have to be the first? Nothing in the conjecture or the framework actually needs the first?"*; *"You can test them and find out but again what are you testing if the cascade finds these isolation events?"*

**Map:** v4 §0 (E200: *"I don't like first isolation"*); E286. **No run.**
- **Withdrawn:** E286's comparison columns (the landing equal to `gridT`, a named instant, earlier than `gridT`) and its sentence that the named instant is an isolation "but not the first … only a witness". A lonely instant is all the conjecture asks; first-ness is a by-product (A.9, E200) and was brought in by the session.
- **Stands:** `gridT` is lonely in every one of the 2,923 complete grids with `q ≤ 10` and fails first at `q = 61.7`, about 120 times the proved bound `q ≤ 0.5` (exact loneliness; no cascade involved). The failures are the proxy's; the cascade found an isolation in all 12,000.
- **What a test is for.** The cascade is the oracle that an isolation exists; the proof's content is a rule that names it from the readings. So a meaningful test is of a candidate formula or finite list of formulas by exact loneliness (the cascade not involved); where none is lonely, the cascade is the oracle that shows what formula is missing.
- **Proposed (not run):** for a complete grid each reading `j` has two instants where it sits exactly on an edge with a factor `c ≤ 7` fixed by its residue: `c·D_j/(8δ_j)` with `c·D_j ≡ 1` (leaving edge) and with `c·D_j ≡ 7` (entering edge): 14 candidates (`gridT` is two of them). Test whether one of the 14 is lonely in every complete grid with any deviation and any laps. A candidate theorem with no radius if so.

## E288 — 2026-10-02 — owner: the movement of the isolation point as the proof; "isolation is individual for each runner"; the "must not run off" requirement questioned

**Owner:** *"No, the 14 formula is just trying to prove another proxy. Since existence is proved via ap/grid what we really need to show is that movement of the isolation point by changing the speed moves the isolation point. That would give proof right?"* Then, on the reply that the isolation must not run off along the path: *"I disagree. Isolation is individual for each runner. They are running at different speeds"*.

**Map:** v4 §4 Q8; E116, E280, E286–E287. **No run.**
- The 14-formula test is dropped (a proxy).
- **Reply given:** the movement argument is a proof in this form (a path from an exact grid to the arrangement, the isolation existing and moving at every point, nothing separate to prove). Local movement (Level C): continuous inside a certificate box (rate about `t/h` per unit change of the setter's speed), continuous across a leaving face (hand-off), a jump to the entering reading's next exit across an entering face. Simple pinches are proved; E280 found a margin window at every multi-pinch read away from tight arrangements. The remaining piece, as the session stated it: the isolation must not leave the path (no entering-face jumps without bound).
- **Owner's objection** (recorded; reasoning not yet given): the isolation is individual per runner, and the runners run at different speeds. **Session's understanding, to be confirmed:** time is not shared, each subject's isolation is measured in its own units (`R = 8·d_min·t`) along its own deformation, nothing is carried between runners; every run so far has `R* ≤ 5.02` (E274). The session's reason for raising the bound: if the arrangement at the end of the path is not known to be lonely, local movement along the open path does not give it, and the only failure is that subject's `R` growing without limit as the endpoint is approached (E116: observed only at a non-lonely endpoint, so it is the conjecture failing). The session may have added a requirement the owner's argument does not have: asked for the owner's argument that the grid keeps the isolation within the first blocks of the subject's own scale, or for the intended route if the path need not end at the arrangement.

## E289 — 2026-10-02 — owner: isolation binds only the two neighbours; the other runners need only be somewhere in the other 6/8 of the circle; E288's "must not run off" withdrawn

**Owner:** *"Isolation requires the other runners to be =>1/8 that is all. So if you know the neighbours of for the isolation the other just have to be somewhere in 6/8th of the rest of the circle."*

**Map:** v4 §4 Q8; `GridNeighbourhoodN`; E288. **No run.**
- **Understanding (to confirm):** loneliness binds only the nearest runner on each side; every other runner is farther by definition, so it is enough that the two neighbours are at `≥ 1/8`, the rest lying in the other 6/8. In the grid the neighbours are residues 1 and 7 on the two edges and the other six sit in their own slots with room; `gridT` is the instant fixed by the neighbours' two conditions alone.
- **Movement.** A neighbour's speed change moves the pair's window continuously (`t_A`, `t_B`); a non-neighbour drifting into the 2/8 arc becomes a neighbour (a local change of the nearest runner: the hand-off); a change in any other runner's speed does not move the isolation.
- **Withdrawn:** E288's requirement to bound the number and size of entering-face jumps along the whole path (it came from following every runner through the deformation).
- **Kept in view, not a bound:** the pair's own window recurs within a bounded time (a three-runner statement); the six others lying outside the arc at that moment is what the grid's slots provide and what the deviation relocates.
- **To confirm with the owner:** that this is the movement statement: only the neighbours determine the isolation, a non-neighbour matters only by entering the arc, and then it becomes a neighbour.

## E290 — 2026-10-02 — owner: "I think we already proved it in lean"; the ingredients crosswalk (`docs/n8/MOVEMENT_INGREDIENTS_v1.md`)

**Owner:** *"yes, and I think we already proved it in lean. I wonder do we already have the ingredients they just need to be constructed without adding in wrongly concieved additionals?"*

**Map:** v4 §2 E, §9 C8; E113–E116, E280, E289. **No run;** the Lean sources read (headers and statements), nothing rebuilt.

**Finding.** The owner's argument is in Lean, stated as such: `DeformationN`'s header reads *"the arithmetic progression is globally isolated (the φ(n) law), every arrangement is a deformation of it, and a deformation moves each runner's isolation point without destroying it"*. `PathWindowN.lonelyRunnerAt8_of_window : WindowBound → LonelyRunnerAt8` assembles it one runner at a time from the AP, with `EndRunnerN`; its parts are proved: the base (`GridNeighbourhoodN`, `APNeighbourhoodN`, `GridPairLawN`, `GridClassN`, R6 at `q = 8`), the neighbours as the binding runners (`TwoPinnerN`, `readings_clear`), margin or pinch (`PathRouteN`), movement with margin (`lonelyAt_of_close`) and at a simple pinch both sides (`PinchOpenN`), one free runner off the lattice by order seven (`OneFreeN`, `OffLatticeN`), local hand-off (`SeparationN`, `PinchTransportN`, `CascadeTransportN`). **One hypothesis remains, `WindowBound`, used only in `lonelyAt_of_limit`, the closedness step.**

**What is on record about it** (E116, E280): at a whole-number point the lonely set has period 1, so the window is automatic there; the hypothesis concerns arrangements near it, where nearby instants are lonely at bounded times iff the point is lonely (escape like `1/ε` at a non-lonely point), so `WindowBound` on the moves is the whole-number statement; between whole-number points the continuum is lonely natively. Not in Lean: the multi-pinch case of local stability (E114's route and E280's finding that every multi-pinch read had a margin window).

**The question carried to the owner:** the limit step (if `vₙ → v₀` and the subject is lonely at some instant of each `vₙ`, then `v₀` is lonely): does the neighbour structure of E289 give it without a bound on the instants? No argument is on disk. Nothing is to be added to the construction beyond that.

## E291 — 2026-10-02 — owner: are handoff and movement needed? ask that of everything; the session adds things the argument does not use

**Owner:** *"Handoff and movement. Are they needed? I want you to ask that for everything. You tend to want to add things to make it look like your training data. Plus you want to add "one thing to think about" as being helpful even if it isn't necessary"*

**Map:** v4 §4 Q8; E289–E290. **No run.** The necessity test applied to E290's crosswalk.
- **Needed by the owner's argument:** the base (the complete grid isolates every runner; proved); only the neighbours bind and the rest lie in the other 6/8 (proved: `TwoPinnerN`, `readings_clear`); and that any arrangement is a deviation from some grid to which that applies (the reduction step: not in Lean in general; Lean has complete grids with small deviation and the doubled-slot family).
- **Not shown to be needed:** movement (the isolation moved from the grid's ideal to a local event is the named instant applied to the deviated grid; no path and no separate lemma); hand-off (which two runners are the neighbours at the arrangement's own grid; part of choosing the pair); margin or pinch, openness, simple and multi-pinch, one runner at a time, the path assembly and the window (the continuation method, needed only if the direct statement cannot be proved for every arrangement and a path must carry it past its domain).
- **Caveat from the owner's own words (E113):** *"two runners sharing the same slot takes a bit of time to sort out but in a very predictable and forced way."* If that sorting-out is part of the mechanism it belongs to the direct statement for arrangements with colliding residues; whether it is, is not known.
- **Recorded:** a feedback memory is being drafted (the `memory-drafter` agent) for the standing instruction: before adding any object, term, test, bound or closing suggestion, name the step of the owner's argument that uses it; if none, omit it.

## E292 — 2026-10-02 — owner: try to construct the proof in Lean, keeping to the rules; no Lean written; the statement to prove is not yet determined

**Owner:** *"Ok based on that I want you to try and construct a proof in lean making sure you keep to the rules"* (taken as lifting E222's hold for this task).

**Map:** v4 §4 Q8; E289–E291; `MOVEMENT_INGREDIENTS_v1.md`. **No Lean written; nothing run.** The necessity test (E291) applied to find the statement to prove.
- **On disk and proved:** the base (the complete grid isolates every runner); only the neighbours bind (`TwoPinnerN`, `readings_clear`).
- **Missing in Lean:** *any arrangement is a deviation from some grid to which that applies.* It is not derivable from the two above: it says some grid and lap has the neighbours clear and the rest in their slots at its class instant, which is Theorem 6.15, the conjecture.
- **The path route does not supply it.** Closedness at an arbitrary limit arrangement is the conjecture for that arrangement (if the limit had no lonely instant, openness and the neighbour structure do not contradict it), so the proof has to be direct for every arrangement.
- **Even the neighbour pair depends on the grid chosen:** at the leaving neighbour's opening `t_A`, the entering neighbour is clear iff `frac(b(t_B − t_A)) ≤ 3/4` (its position is `D_B/8 − b(t_B − t_A)`, `D_B ≡ 7 mod 8`): a phase condition on lap times deviation.
- **The determining piece is the owner's:** the rule fixing the grid (reading, divisor, class) for an arbitrary arrangement, including colliding residues and a reading `≡ 0 mod 8` (E113: *"takes a bit of time to sort out but in a very predictable and forced way"*), as a function of the readings. That rule is the Lean statement to prove; without it a Lean file would state a proxy.

## E293 — 2026-10-02 — owner: map on hold (proxies, not the cascade); "the conjecture itself" withdrawn for the route; two runners at the same speed as the contradiction; bridges

**Owner:** *"Yes Im putting the map on hold because you stopped mapping the cascade and started mapping proxies."* On E292: *"I think you are wrong. It is not the conjecture itself. We have proof of isolation, we just show that any deviation from that just displaces the isolation because we can show where and why it goes there."* On the limit arrangement: *"The structure that contradicts it is two runners at the same speed."* And: *"No matter how close two speeds are, they can never be the same speed. As one is always by definition faster, sucessive revolutions we increasing separate them. We already proved this in lean elsewhere."*

**Map:** none (the map is on hold by the owner). **No run.**
- **Withdrawn:** E292's "which is the conjecture itself" for the owner's route. The statement "some opening is lonely" is equivalent to the conjecture (Theorem 6.15); the owner's proof is isolation at the grid (proved) plus a derivation of where and why a deviation displaces it, which is a route and not that statement.
- **What Lean has of the same-speed separation** (read, `Spec/SeparationN.lean`): `sweep_lap_bound`, `sweep_lap_lt`: a sweep step on lap `k` forces `8k(s_a − s_b) < s_a + s_b`, so a pair of distinct speeds hands the isolation down by a sweep on finitely many laps, and only equal speeds could on every lap. Pairwise, sweep steps only.
- **What the record says it does not cover** (E161, E163): bridges (a hand-over to a faster runner on a later lap or a slower one on an earlier lap) carry no per-pair lap bound; at `a`'s exit on lap `k`, `b` is in a window iff `(8k+1)·b/a` is within 1 of a multiple of 8, which recurs; bridge pairs recurred within one chain 26 times (Case B to 24) and 4,298 times (late fine band shapes), at gaps of 1 to 3 laps. In Lean `FAM` (each runner in the way at only finitely many steps) is proved equivalent to the target (`FAM_of_existence`, `doorFAM_iff`).
- **Question to the owner:** how the same-speed separation argument covers bridges as well as sweeps. No argument is on disk.

## E294 — 2026-10-02 — full read of the separation / transport / ideal-reading / pair-law modules; absence claims of E290, E292, E293 withdrawn where they conflict

**Owner:** *"Are you sure you're looking at the full library of the n=8 work?"* then: do it properly, efficiency is not a consideration.

**Map:** none (map on hold). **No run.** Read in full (bodies, not headers), `LonelyRunner/LonelyRunner/LRC/`: `Spec/HandoffDriftN`, `Spec/HandoffResonanceN`, `Spec/LapDeadlineN`, `Spec/CascadeTransportN`, `Spec/SeparationN`, `Cascade/Reading`, `Spec/ProgressionPairN`. Headers of all 242 modules were catalogued earlier; the other bodies are still unread.

**What the bodies state (proved, no `sorry`):**
- `SeparationN.sweep_lap_bound/lt`: a sweep step on lap `k` needs `k < (s_a+s_b)/(8(s_a−s_b))`; distinct speeds hand over by a sweep on finitely many laps (pairwise, sweeps).
- `CascadeTransportN.return_lap_increases` (any iterate of `move`, any number of intervening hand-offs, not only sweeps): a reading blocked at lap `K` at step `i` and blocked again at step `j>i` is blocked on a lap `L>K`. `active_return_lap_increases`, `move_eq_opening_of_only_blocker`, `reading_at_exit` (transport retains the ratio `d/c`, whole laps included).
- `HandoffDriftN`: capture at an opening is the depth interval `(0,2)` (`captured_iff_depth`); a repeated lap-advance pattern `(r,s)` changes depth by `8(s − r·b/a)` per repeat (`depth_repeat`); nonzero drift gives finitely many repeats; perpetual repeat forces `s·a = r·b` (`perpetual_pattern_zero_drift`). **`distinct_pair_recurring_capture`: speeds 7 and 8 (distinct) recur at every `q`**, so for a fixed pattern distinctness alone does not exclude recurrence; zero drift is commensurability.
- `HandoffResonanceN`: a reading that blocks at every replay of a period `P` has `d·P ∈ ℤ` (`persistent_role_integral`); a perpetual schedule puts all its readings on a common time lattice (`persistent_schedule_common_lattice`); `integral_phase_lap_transport`.
- `LapDeadlineN`: exact ledger (`lap`, `slack`, `deadline`), `clear_iff_slack`, `captured_iff_slack`, `lonely_after_shift_iff` (whole-arrangement test from updated ledgers), `group_window_iff/nonempty/width` (slowest sets the opening, fastest the deadline).
- `Cascade/Reading.lean`: the owner's model as a structure. `IdealReading` and `reading` for every arrangement and every gap `D`; `position_in_eighths`, `clear_iff`, `on_ideal_clear`, `nearest_on_ideal_above/below`, `lonely_of_reading`. Its header: "Not stated here: which gap the cascade gives for a given arrangement. `D` is an input."
- `ProgressionPairN.pair_law`: AP deformed within `|d_j − jc| ≤ c/20`: one instant of each pair `(1,7)`, `(3,5)` stays lonely, exactly; "displaced within its pair, never destroyed" (the owner's displacement statement, proved for that neighbourhood).

**Withdrawn / corrected:**
- E290's `MOVEMENT_INGREDIENTS_v1.md` "Not in Lean" section and E293's closing line "No argument is on disk" are withdrawn as stated: they were written from headers of about two dozen modules. What is on disk toward the same-speed separation is the list above.
- Still not established by anything I have read: that the separation argument covers bridges in the sense of excluding recurrence on every lap. `return_lap_increases` covers every move including bridges but gives `L>K` only; `distinct_pair_recurring_capture` is the counterexample for a fixed pattern. The owner's argument for that step is not in the modules read.
- Still not established: the deviation-displaces-isolation statement beyond the `c/20` AP neighbourhood (`pair_law`, `GridNeighbourhoodN`); `Reading.lean` leaves `D` an input.
- Remaining to read in full: `Cascade/Arrangement`, `Cascade/Iteration`, `Cascade/SmallOrders`, `Spec/PinchTransportN`, `Spec/MixedLapOverlapN`, `Spec/CoreDriftN`, `GridPairN`, `GridPairLawN`, `GridNudgeN`, `GridNeighbourhoodN`, `DeformationN`, `PathWindowN`.

## E295 — 2026-10-02 — owner: "so all those tools and you can't construct a proof? … is it actually needed or are we importing it"

**Map:** none (on hold). **No run.** Read in full: `Spec/DeformationN`, `Spec/PathWindowN`, head and `segment_lonely` of `Spec/PathRouteN`.
- **The owner's argument is already constructed in Lean**: AP lonely at `t=1`; move one runner at a time (`PathWindowN.chain`, `chain_succ`); each segment `PathRouteN.segment_lonely` (openness at every lonely instant, margin or pinch, `margin_or_pinch`, `simple_or_multi`; the fixed runners' readings rational, `hrat`); closedness `DeformationN.lonelyAt_of_limit`; `PathWindowN.slowest_of_window`; `lonelyRunnerAt8_of_window : WindowBound → LonelyRunnerAt8` (via `EndRunnerN`). No order of moves and no distinctness along the way is required.
- **One hypothesis is open: `hbound` / `WindowBound`**, the lonely instant stays in a window `[c, T]`. It is used only in closedness (`lonelyAt_of_limit`: a bounded sequence of instants has a convergent subsequence). It is not imported from the literature; it is the "isolation cannot escape to infinity" step of the continuity proof.
- **Contradiction in my own record:** the 974bb3e crosswalk (E290) had this right (one hypothesis, `WindowBound`). E292's "the missing statement is the grid-selection rule" and E293's "no argument on disk" contradict it and are withdrawn; the grid-selection rule is not a hypothesis of any theorem above.
- **Necessity:** `WindowBound` is needed by the path route only to pass to the limit at a segment's closedness point; the cascade does not use it. In a segment only the mover is not rational (`hrat`), the others' clear set is periodic. `WindowBound` as written is uniform over all arrangements with the subject's readings in `[c, C]`, which is wider than one segment needs.
- **To prove (the owner's statement, in segment form):** on a one-mover segment, the lonely instant stays in a window; where the instant goes as the mover's speed changes is the displacement, and it can only leave every window if the mover's speed coalesces with a fixed reading (the same-speed case), which the segment excludes.

## E296 — 2026-10-02 — owner: "prove the window for the one-mover segment, formalise it … then look for what other step is missing from the proof of n=8"

**Map:** none (on hold). One Lean file, built, axiom-checked. No scripts.
- **Formalised:** `LonelyRunner/LRC/Spec/SegmentWindowN.lean` (nested repo). `exists_far_multiple_bounded`, `exists_clear_step_bounded` (the step count of `OneFreeN.exists_clear_step` exposed: `m ≤ 1/(4a)+1`, `a = ‖α‖`), and `lonely_window_of_one_free`: six readings of common period `P` fix `t₇ > 0` (order seven, independent of the mover); for every mover reading `x` with `x·P` not whole the arrangement with the mover at `x` is lonely at some `t ≤ t₇ + P(1/(4a)+1)`, `a = ‖x·P‖`. `#print axioms` = `[propext, Classical.choice, Quot.sound]`; `lake build LonelyRunner.LRC.Spec.SegmentWindowN` clean. Order seven is used as the native `OrderSevenN.existenceAtN_seven`; nothing imported.
- **Withdrawn (E295's last bullet and the previous message):** that the window fails only if the mover coalesces with another reading. It fails to be uniform exactly at the lattice points of the segment (`x·P` whole): `T ~ P/(4a) → ∞` as `a → 0`. Coalescence is not involved.
- **What the segment gives:** every point of a one-mover segment off the lattice is lonely (already `OneFreeN.lonely_of_one_free_eight`), with the window above on any part where `a ≥ a₀ > 0`. At a lattice point every reading is a whole multiple of `1/P`: an integer arrangement after scaling, whose lonely set is `P`-periodic, so a lonely point there is lonely in `(0, P]`.
- **Consequence for the path route:** `lonely_along_path` needs one window over the whole segment, which does not exist near a lattice point. The segment does not need it: loneliness is established off the lattice directly. The only points not covered are lattice points, and the final arrangement `V` of any integer arrangement is one. So the path route reduces real speeds to integer (rational) speeds and says nothing about the integer case. This is the already-recorded `RealEightN` reduction by another route.
- **What is left of n=8, in the framework's terms:** loneliness at an integer arrangement `V` (readings `r₁ … r₇` distinct positive integers). For any chosen mover `i`, the six others' lonely set `F_i` (period 1, containing the order-seven windows around `t₇`, margin `1/7 − 1/8`) against the mover's comb `‖r_i t‖ ≥ 1/8`: the instant needed lies in `F_i ∩ comb`. Nearby non-lattice arrangements are lonely at `t₇ + mP` with the mover carried a quarter to a half lap beyond its `V`-position at `t₇`; that phase is not available at `V`.

## E297 — 2026-10-02 — owner: "apply the grid displacement argument at the integer arrangement"

**Map:** the grid through `D = 1` of an integer arrangement `R = {r₁ … r₇}`; no deviation (`ε_j = 0`). Scripts `experiments/nN/redo/two_adic_grid_v1.py`, `_v2.py` (nested repo).
- **Exact form.** `R` is lonely at `t = k/(8m)` iff every `r_j·k mod 8m` lies in `[m, 7m]`. The lonely set of an integer arrangement is closed with rational endpoints, so if nonempty it contains a rational instant.
- **The `D = 1` grid.** At `t = a/8`, `a` odd, runner `j` sits at `(a·r_j mod 8)/8`: clear iff `8 ∤ r_j`. All four class instants at once. So `Z = {j : 8 | r_j} = ∅` gives lonely at `1/8`. (Derived by hand, not formalised.)
- **`Z ≠ ∅`.** The `Z` runners sit in the subject's slot at every class instant. Refine the grid 2-adically: `v = max ν₂(r_j)`, modulus `2^{v+1}`, `t = k/2^{v+1}`, `k` odd. A runner with `ν₂ = v, v−1, v−2` sits at `4m`, `{2m,6m}`, `{m,3m,5m,7m}` for every odd `k` (`m = 2^{v−2}`): clear. A runner with `ν₂ ≤ v−3` is blocked for the odd `k` that put its odd residue in the central quarter. (Hand derivation.)
- **Oracle check.** `[PROVISIONAL]` n/a (no gate). Exhaustive `N=20` (77,520 sets): no lonely instant on the 2-adic grid for 4,751 (6.1%); random `≤400`: 575 of 20,000 (2.9%). Each of the examined ones is lonely elsewhere (`lonely_any`, `m<200`: all True in the 25 printed). `N=16`: of the 1,153 sets off the 2-adic grid, the first lonely instant in `(0,1]` is an opening `(8K+1)/(8r_e)` in all 1,153, `K ≤ 6`; largest class `(e = slowest, K = 0)`, 298.
- **Not obtained:** a rule giving the instant (which `(e, K)`, or which modulus) from `R`. The argument as applied closes `Z = ∅` and places the `Z` runners; it does not by itself give existence when the low-valuation runners block every odd `k`, nor off the 2-power grids.

## E298 — 2026-10-02 — owner: "Why not in lean?"

No reason: E297 marked the `D = 1` grid facts "not formalised" and stopped. Formalised now: `LonelyRunner/LRC/Spec/IntegerGridN.lean` (nested repo). `clear_rational_iff` (reading `d` clear at `k/(8m)` iff `∀ z, m ≤ |d·k − 8m·z|`), `clear_of_dvd_not_dvd` (`m ∣ d·k`, `8m ∤ d·k`), `clear_two_adic` (`2^e ∣ d`, `2^(e+3) ∤ d`, `k` odd: clear at `k/2^(e+3)`), `lonely8_of_no_multiple_of_eight` (`Lonely8` at `1/8`), `lonely8_two_adic_window` (every valuation in `[e, e+2]`). Built clean; axioms `[propext, Classical.choice, Quot.sound]`. Not formalised: the oracle counts of E297 (script outputs).

## E299 — 2026-10-02 — owner: the cascade shows where the isolation moves and why: the deviation of the speeds from the AP/grid deforms the isolation event; "yes, formalise it"

**Map:** the grid `D = 1` of an integer arrangement; slot residue `ρ = a·x mod 8` at the grid instant `a/8`; the shift `x/c` eighths. **Consequence:** the displacement at an integer arrangement is stated and proved in the deviation's own terms; E297's "rule not obtained" is withdrawn for this displacement (the 2-adic family and the counts are not part of the argument, E297 counts dropped as not needed).
- `LonelyRunner/LRC/Spec/IntegerDisplacementN.lean` (nested repo), built clean, axioms `[propext, Classical.choice, Quot.sound]`.
- `lonely_of_displacement`: `8 ∣ c` (slot 0 at `a/8`); every other reading has slot `ρ ≥ 1` and `ρ + x/c ≤ 7`; then every reading is clear at `a/8 + 1/(8c) = (8K+1)/(8c)`, `K = a·c/8`. Built from `SeparationN.lonely_of_separation`.
- `slower_clear_iff`: for `x < c`: clear at that instant iff `ρ ∈ [1, 6]`; the obstructing slower readings are exactly slot `7` (carried over the entering edge: edge push) and slot `0`.
- `clear_at_exit_iff`: every reading, clear iff `∀ z, c ≤ |x(ac+1) − 8cz|`.
- `lonely8_example`: readings `1,2,3,4,5,7,8` (speeds 1,2,3,4,5,6,8,9 for subject speed 1) lonely at `9/56`, the leaving edge of the reading `7`, which the first displacement (8 leaving at `9/64`) carries into its slot.
- **Not stated:** the displacement of an entering-edge runner (the `7` here) as a general theorem; only its instance.

## E300 — 2026-10-02 — owner: Lean requires a correct statement and code, not what it "looks like"; code the step

**Map:** the cascade's `move` at the grid instant of an integer arrangement. Added to `IntegerDisplacementN.lean` (nested repo), built clean, axioms `[propext, Classical.choice, Quot.sound]`:
- `inWay_at_grid_iff`: `a` odd, a reading is in the way at `a/8` iff `8 ∣ x`.
- `nextOpening_at_grid`: for `8 ∣ x`, `nextOpening 8 x (a/8) = a/8 + 1/(8x)`.
- `move_at_grid`: for `S` positive readings, `c ∈ S`, `8 ∣ c`, `c` least multiple of `8` in `S`, `a` odd: `move 8 (S.image cast) (a/8) = a/8 + 1/(8c)`. The cascade's first move is the displacement of `lonely_of_displacement`, with no band hypothesis.
- `inWay_at_exit_iff`: at `a/8 + 1/(8c)` a reading is in the way iff `∃ z, |x(ac+1) − 8cz| < c`.
Not coded: the next `move` from that instant and the composition to a certificate `(b, k)`.

## E301 — 2026-10-02 — owner: "code the second move and the composition"

**Map:** the cascade's `move` at a state `K/(8m)`; its start `1/(8·d_min)` is `K = 1`, `m = d_min`.
- **Second move and composition already exist as general theorems** (read, `Cascade/Iteration.lean`, `Cascade/ScaleCandidates.lean`, `Spec/Doors.lean`): `move` iterated; `move_eq_self_or_opening`; `iterate_mem_openings` (every iterate below a lonely time is the start or an opening); `lonely_iff_run_ends` (lonely iff the iteration from `1/(8m)` reaches a fixed point, and iff a `Run` ends in a lonely time); `lonely_iff_exists_flank`, `lonely_iff_exists_candidate_scale`; `Flanks.lonely_iff_emod_search` (the congruence certificate); `doors_agree`. Recoding them would duplicate.
- **Correction of E297/E299:** their grid is `D = 1` (instants `a/8`), which is the cascade's own start only when the reading 1 is present (`d_min = 1`, `1/(8·d_min) = 1/8`). For `d_min = m > 1` the ideal gap is `m`, the deviations are `(y mod m)/m`, and the start is `1/(8m)`. `move_at_grid`/`lonely_of_displacement` are exact statements at the states `a/8`; they are on the cascade's path only when `d_min = 1`.
- **Coded (`IntegerDisplacementN.lean`, built clean, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`):** `nextOpening_rational` (blocker `x`, `|x·K − 8m·z| < m`: opens at `(8z+1)/(8x)`), `inWay_rational_iff`, `move_rational_le_iff` (`move ≤ s` iff `K/(8m) ≤ s` and every blocker's opening `≤ s`). These cover every state, in particular the start, with `m = d_min`.
- **What remains of the proof, as a Lean statement:** for every `EightResidual` set, the iteration from `1/(8·d_min)` reaches a fixed point (`lonely_iff_run_ends`, left side).

## E302 — 2026-10-02 — owner: "we can pause the lean here and then attempt to solve this" (the rule from the readings of a residual set to `(b, k)`)

**Map:** the certificate `(b, k)` in the grid-and-deviation form; read `MECHANISM_MAP_v4` §4 (Q9, the central open statement). No run, no Lean.
- **The certificate in deviation form `[derived, by hand]`.** Flank `b ∈ S`, reading `a = b·q_a + r_a` (`0 ≤ r_a < b`), `ε_a = r_a/b`. At the class-1 instant of lap `k`, `t = (8k+1)/(8b)`, `a`'s position in eighths is `(8k+1)(q_a + ε_a) ≡ q_a + ε_a + 8·{k·r_a/b} (mod 8)`: the deviation scaled by the lap count, `8k`, and not by a class `c ≤ 7` (that holds at lap 0 only). It is clear iff `‖(8k·r_a + a)/(8b)‖ ≥ 1/8`. A multiple of `b` (`r_a = 0`) needs `8 ∤ a/b`. For `k` mod `b`, the vector `({k·r_a/b})_a` runs over the cyclic group of order `b` generated by `(r_a/b)_a`; a certificate is a point of that group in the box `∏_a (c_a + [1/8, 7/8])`, centres `c_a = −a/(8b)`.
- **A check of the same shape `[derived]`.** Take the fastest reading `V` as the one free runner and `F` the lonely set at `1/8` of the six slower readings. `V`'s blocked set is open arcs of length `1/(4V)`, period `1/V`. A component of `F` of length `≥ 1/(4V)` is not inside one open arc, so contains a point where `V` is clear. At a `1/7`-lonely instant of the six, `F` contains a window of length `1/(28·r_6)`, so `V ≥ 7·r_6` suffices: this is R8 exactly.
- **Not done:** the rule. Nothing here names `(b, k)` for a residual set.

## E303 — 2026-10-02 — owner: "do that on a residual set … the cascade achieves the isolation, we need to figure out how it does it"

**Map:** the cascade on the residual set `S = (1,2,3,5,7,12,16)` (readings from the subject; subject speed `s > 0`, e.g. speeds 1,2,3,4,6,8,13,17 for `s = 1`); `[VERIFIED — exact Fractions]` residual by the fields of `OrderEightCasesN` as in `eight_residual_count_v1.py`. Script `LonelyRunner/experiments/nN/redo/residual_anatomy_v2.py`, output `.out`.
- **Grid `D = 1`:** slots `1,2,3,5,7,4,0`; at `1/8` only `16` (slot 0) is in the way. The cascade: `1/8 → 17/128 → 9/56 → 17/96 → 9/40`, setters `16, 7, 12, 5`, each the sole blocker, laps `2, 1, 2, 1`; lonely at `9/40 = (8·1+1)/(8·5)`. Certificates `(b,k)`: `(5,1), (7,5), (12,3), (12,9)`; the cascade lands on the least instant.
- **Each move shifts every reading `x` by `x·s` eighths** (`s = 8Δt = 1/16, 25/112, 11/84, 23/60`). Carried in: `7` (at the slot-7 edge, 7.000 → 7.438: `slower_clear_iff`), `12` (4.750 → 7.429: shift 2.679 > 1, not slot-predicted), `5` (6.429 → 7.083). At `9/40` the positions are `λ·x mod 8`, `λ = 8t = 9/5`: `1.8, 3.6, 5.4, 1.0, 4.6, 5.6, 4.8`, all in `[1, 7]`; with `D = 5`: `q + 9ε`, `ε = r/5 ∈ {1/5, 2/5, 3/5, 0, 2/5, 2/5, 1/5}`.
- **What the data show:** the first step is the slot description (one deviant, `16`; the next carried reading is the slot-7 reading). From the second step the shifts `x·s` exceed one eighth for `x ≥ 5`, so the carried reading is set by the lap-scaled deviation, not the slot. In `λ` the lonely set is the complement of `∪_{x,j} ((8j−1)/x, (8j+1)/x)`.
- **Not derived:** why the chain ends at `5`, or a rule for `(b, k)`; one set.

## E304 — 2026-10-02 — owner: "there is a lot of work done previously on residual; check we don't already have something to reuse, rebuild or remake"

**Map:** none. Read: `docs/n8/PROOF_PLAN_ORDER8_v2.md` (all), `RESIDUAL_GAP_v1`, `RESIDUAL_ANGLE_v1`, `RESIDUAL_NO_STATIONARY_v1`, `MECHANISM_MAP_v4` §4, log E117–E120, `experiments/nN/residual_members_v4/v5.out`, `eight_residual_count_v6.out`, headers of `residual_fields_v1.py`, `eight_residual_anatomy_v1.py`.
- **Correction of E303.** `residual_anatomy_v1.py` used the first fields of `eight_residual_count_v1.py` only (ladder, spread, descent, free flank, R4, not-fast, first-lap, `−7`); the current `EightResidual` has 22 fields (rational openings `N ≤ 9`, resolutions `D ≤ 64`, fast pair, block split, one free reading). `(1,2,3,5,7,12,16)` is residual under the old fields only. **Under the current fields no 7-subset of `[1, 40]` is residual** (`eight_residual_count_v6.out`: not cleared by any `D ≤ 64`: 0 in `[1,30]` and `[1,40]`). E303's tag "residual" is withdrawn; its cascade and table stand as the cascade on that set.
- **Existing and reusable.** (1) Field predicates: `LonelyRunner/experiments/nN/residual_fields_v1.py` ("the 22 fields as predicates, for reuse"). (2) Member generators and outputs: `residual_members_v4/v5` (B1: largest reading a multiple of `8·lcm(1…64)`, 47 of 400 constructions with all 22 fields, spread 7.1–8.9, least live lattice `L0 = 67`, grid part empty in 42 of 47, cascade 1–5 moves, flank a middle reading at lap 1 in 44 of 47) and `residual_members_C_v1` / `_C_list_v1.json` (C1: a slow runner below a six-reading cluster, 297 of 300, `R* ≤ 1.377`). (3) Categories at the AP scale `d_min` (E117, E118): B1 (fastest runner lapped once into the subject's slot, spread 7–9; `collision_band_v1`: least lap 1 in 1,644,119 of 1,717,540 sets, at most 6) and C1. (4) Lean: `TwoBlockN` (`lonely_eight_of_blocks`, `lonely_eight_of_pairwise_laps`, `exists_big_gap`, `b1_remainder`), E119's comb-sliding frame (`log d + log 8t ∈ F`). (5) Earlier residual studies (Sept 7–12): extremisers `{1,3,4,5,7,11,24}` and `{1,4,5,6,7,11,16}` with `M = 2/15` at `t = 7/15` (witness denominator 15, outside the ladder); the denominator route is equivalent to `|G| > 0` (`N_d/d → |G|`); the `Σα` bound is an equality at `E*`; extreme runners are residual twice as often as interior (`RESIDUAL_NO_STATIONARY_v1`). (6) `PROOF_PLAN_ORDER8_v2` WP3 and WP4 are this task: build members by shape, perturb through the cascade, name the landing `(e, K)` from the readings.
- **Duplicated by me this session:** the cascade-on-a-set anatomy (E117 and `rung_landing_v1` did it on the 47 members), and the residual definition (partially). The pre-use grep of O2/O3 was skipped again (cf. O6).

## E305 — 2026-10-02 — owner: "redo the anatomy on the real members"

**Map:** the cascade on real `EightResidual` members, in `R = 8·d_min·t` and `ρ_x = x/d_min`; each reading's position is `R·ρ_x mod 8` eighths. Members: 47 B1 (`residual_members_v5` generator, re-checked against the 22 fields) and 547 C1 (`residual_members_C_list_v1.json`). Scripts and outputs: `LonelyRunner/experiments/nN/redo/anatomy_members_v1.{py,out}` (positions, shifts, landing in the `q, ε, {kε}` form) and `_v2.{py,out}` (zone chain). Exact Fractions. Shown: B1 #0, 1, 3, 5, 7 and C1 #0, 1, 2 (not a survey).
- **Zones.** Reading `x` blocks `R` in `Z(x,j) = ((8j−1)/ρ_x, (8j+1)/ρ_x)`, `j ≥ 0`. The cascade from `R = 1` jumps to the right end of the zone containing it; the landing is the first `R ≥ 1` in no zone. `[derived, by hand; checked on these members]`. Two zones of consecutive readings `ρ_x < ρ_y` at lap `j` overlap iff `ρ_y/ρ_x ≤ (8j+1)/(8j−1)` (`SeparationN.sweep_lap_bound` is this condition: `sa(8k−1) < sb(8k+1)`); `9/7` at lap 1 (`exists_big_gap`, E119), `17/15` at lap 2.
- **B1 (fastest `ρ ∈ (7, 9)`):** every landing has its setter at position exactly `1.000` and every other reading in `[1, 7]`. The chain is lap-1 zones of the upper block `ρ ∈ (4.6, 8.8)`, entered at the previous end: #7 `rank 7 lap 1 → rank 5 lap 1 → rank 4 lap 1 → rank 3 lap 1 → rank 7 lap 2`, `R* = 2.0943`, overlaps `0.138, 0.006, 0.244, 0.009, 0.081`; #1 two zones, #3 three, #5 two, #0 one. It ends where the next zone starts later than the last end; in #7 `rank 6 lap 2` starts at `2.186` and its ratio to `rank 7` is `1.183 > 17/15`.
- **C1 (`d_min` below a six-reading cluster, `ρ ∈ [26, 96]`):** one move, one zone of a cluster reading at lap 6 to 11 (`R* = 1.0052, 1.0131, 1.0138`), inside the slow runner's first window; zone half-width `≈ 1/ρ` is the whole move.
- **What the chain says, in the owner's terms:** the isolation moves while the next zone overlaps the last; it stops at the first pair of zones that do not overlap and that no third reading's zone fills. Distinct speeds separate zones at later laps (`(8j+1)/(8j−1) → 1`), which is `sweep_lap_bound`.
- **Not derived:** why no third reading's zone fills the first gap, for every residual member (the pairwise-laps statement `TwoBlockN.lonely_eight_of_pairwise_laps` gives a lonely `R` once laps with all pairs overlapping-free are chosen; it does not choose them). This matches E117–E120 for B1 and E118 for C1; the zone table and the `(8j+1)/(8j−1)` criterion are the additions.

## E306 — 2026-10-02 — owner: "AP, as in every grid, has global isolation at 4 instants, not one; check, and if 4 we have the mechanism of the deformation"

**Map:** the lonely set of the AP and of complete grids over one period; exact. Script and output `LonelyRunner/experiments/nN/redo/grid_isolation_count_v1.{py,out}` (reading `a` clear on `[(8k+1)/(8a), (8k+7)/(8a)]`, intervals intersected and merged exactly).
- **AP `1..7`:** exactly four lonely instants per period, all isolated points, `1/8, 3/8, 5/8, 7/8` (measure 0). `c·AP` (`c = 3, 5, 7`): `4c` isolated points per period, i.e. four per `1/c`. `[VERIFIED — exact]`
- **Complete grids** (residues mod 8 exactly `{1,…,7}`, laps `< 4`; 16,384 sets): the four `a/8`, `a` odd, are lonely in all 16,384 (asserted for each; consistent with `isolation_iff_coprime`, `card_coprime_eq_totient`, which prove it in general). In all but 2 of them (all but 1 distinct set with 4 points and no interval, the AP) there are also lonely intervals of positive length; they come in mirror pairs `t ↔ 1 − t`, one or two between consecutive pinned points. Examples: `(1,2,3,4,5,6,15)`: points `1/8, 3/8, 5/8, 7/8` and six intervals, measure `13/240`; `(1,2,3,4,5,7,14)`: points and two intervals, measure `1/35`; `(9,2,3,4,5,6,7)`: points and `(1/16, 7/72)` with its mirror. So a grid has the four pinned instants always, and more when its readings carry extra laps.
- **Connection to the cascade's start `[derived, by hand]`.** In `R = 8·d_min·t` the four class instants of the `d_min` grid are `R = 1, 3, 5, 7`; the cascade starts at `R = 1`. A reading `ρ = 8 + ε` (the lapped fastest of B1, `|ε| < 1`) sits at `a·ε` eighths at class `a`: the deviation scaled by the class. It blocks `R = 1` and leaves the slot at class `a` when `a·|ε| ≥ 1`. This is the owner's "deviation scaled by the class" as an equation.
- **Not checked:** that the real members are near a grid in the sense of `pair_law`'s `c/20`; their readings (`1, 1.5, 2.9, 3.1, 3.8, 8.0, 8.5`, `#0`) are not.

## E307 — 2026-10-02 — owner: formalise "deviation scaled by the class" briefly; check how the cascade moves each of the four instants as the speeds change; mid-turn: "if 0.7 is the AP gap, don't the rest fall on grids/dmin?"

**Map:** the four class instants `R = 1, 3, 5, 7` (`R = 8·d_min·t`) of the AP `1..7`, tracked under deformation; `LonelyRunner/LRC/Spec/ClassDeviationN.lean`; scripts `four_instants_track_v1.{py,out}`, `grid_gap_scan_v1.{py,out}` (exact; `redo/`).
- **Lean** (`ClassDeviationN.lean`, built clean, axioms `[propext, Classical.choice, Quot.sound]`): `circDist_class_deviation` (a reading `d·(8n + ε)` at the class instant `t = a/(8d)` has `circDist = circDist(a·ε/8)`, any lap `n`), `class_blocked` (`|a·ε| < 1`), `class_clear_of_band` / `_neg` (`1 ≤ ±a·ε ≤ 7`), `lapped_fastest`.
- **The `D = 0.7` question `[VERIFIED — exact decimals, member #0]`:** `ρ/0.7 = 1.43, 2.18, 4.11, 4.48, 5.40, 11.50, 12.16`; deviations from the nearest multiple of `D`: `0.43, 0.18, 0.11, 0.48, 0.40, 0.50, 0.16` (max `0.495`): not near a grid. Best `D ∈ [0.2, 1.3]` for #0 is `0.3125`, max deviation `0.246`, idx mod 8 `3,5,1,2,4,2,3` (collisions); for B1 #1, #3 the best `D ≈ 1.0, 1.16` with max `0.21, 0.25`; for C1 #0, #1 `D ≈ 0.92, 0.88` with `0.115, 0.138`. A finer `D` gives a smaller deviation (Dirichlet) but its class instants lie at `R = a/D`, `≥ 3.2` for `D = 0.3125`, beyond the landing `R* = 1.1185`.
- **The four instants under `ρ_7: 7 → 8.5`, others at the AP (`P1`)** `[VERIFIED — exact run; thresholds derived by hand and matched]`:
  - `a` is blocked by the lapped fastest exactly when `|a·(ρ_7 − 8)| < 1`, i.e. `ρ_7 ∈ 8 ± 1/a`: `a = 1: (7,9)`, `3: (7.667, 8.333)`, `5: (7.8, 8.2)`, `7: (7.857, 8.143)` (the table's displacements start and stop at those `s`).
  - **Pair structure (`ProgressionPairN`):** at class `a` the reading `a` is on the leaving edge and the reading `8−a` on the entering edge. A rightward displacement of `a` is stopped at the exit of the entering reader, `R = a + 2/(8−a)`: `R = 3.4` for `a = 3` (reader 5) and `5.667` for `a = 5` (reader 3), constant over the `s`-range in the table; `a = 1` → `1.2857` (reader 7), `a = 7` → `9` (reader 1).
  - **`a = 1` under `ρ_7 > 7`:** `R = 1` is destroyed and `R = 7` survives (`pair_law`). The re-formed isolation sits at the first gap of the zone chain from `R = 1`: at `9/ρ_7` (exit of 7's lap 1) once `ρ_7/ρ_6 ≥ 9/7`, i.e. `ρ_7 ≥ 54/7 = 7.714` (table: `0.161` at `ρ_7 = 7.75`, `0.059` at `8.5`, both `= 9/ρ_7 − 1`); for `ρ_7 ∈ (7.3, 7.7)` at `17/ρ_7` (lap-2 exit of 7: `1.329` at `7.3` is `17/7.3 − 1`) and then at `9/4 = 2.25` (exit of reading 4, gap with reading 3 since `4/3 > 9/7`: `1.250` at `7.6`); for `ρ_7 ∈ (7, 7.2)` it jumps to `R = 3` (`+2`).
  - `P2` (`ρ_4: 4 → 4.6`): the instants at `a = 1, 3, 5` do not move; `a = 7` is displaced from `ρ_4 ≈ 4.45`, `a = 9` from `4.36`; `P3` (AP → B1 #7): all four displaced at once, `R = 1` by `0.65–1.9`, ending at `1.094` (not `R* = 2.094` of the member: the target's `R=1` instant sits at `1.094`, a different lonely component).
- **Not done:** the same tracking along the path of a real member from its nearest grid; a derivation of the gap positions for general `ρ`; `P3`'s components are not matched to the four.

## E308 — 2026-10-02 — owner: "I look at speeds, you look at the gaps"; the cascade turns an arrangement into grid plus deviation; "I suspect we are not always keeping to the first isolation event of the ideal if it is pushed"

**Map:** the four class events of the AP, as zone tangencies, under `P1` (E307). **Presentation rule from now on:** give speeds (`s, s+1, …`), say "the fastest runner's speed", not `ρ_7`; readings only when the speed is stated beside them.
- **Each of the AP's four events is a tangency of two zones `[derived, by hand; matches the exact tables]`.** In `R = 8·d_min·t`, zone `Z(ρ, j) = ((8j−1)/ρ, (8j+1)/ρ)`. At the AP (`ρ = 1..7`): `R = 1` is where `Z(1,0)` (ends at 1) meets `Z(7,1)` (starts at `7/7 = 1`); `R = 3`: `Z(3,1)` ends at 3, `Z(5,2)` starts at `15/5 = 3`; `R = 5`: `Z(5,3)` ends at `25/5 = 5`, `Z(3,2)` starts at `15/3 = 5`; `R = 7`: `Z(7,6)` ends at `49/7 = 7`, `Z(1,1)` starts at `7`. The leaving reader is `a` and the entering reader is `8 − a` (`ProgressionPairN`). Deformation moves the edges as `(8j±1)/ρ`; the tangency opens into an interval iff `a·ρ_{8−a} ≤ (8−a)·ρ_a` and closes (overlap) otherwise: `pair_law`.
- **The first event is not always kept (`P1`, speeds `s, s+1, …, s+6` and the fastest runner moved from `s+7` to `s+8.5`):** (i) fastest `s+7 < … ≲ s+7.29` (`51/7`): `R = 1` is destroyed and the landing is the ideal's event `R = 3`, unmoved; (ii) `s+7.29 … s+7.71`: no ideal event; the landing is a gap of the zone chain at `17/ρ_7` (lap-2 exit of the fastest), then at `9/4` (exit of reading 4); (iii) from `s+7.714` (`54/7`) to `s+8.5`: the landing is at `9/ρ_7` (exit of the fastest's lap-1 zone), the gap born when `Z(7,1)` and `Z(6,1)` separate (`ρ_7/ρ_6 ≥ 9/7`), at `R = 1.1667` at birth, not a continuous displacement of `R = 1`. The pinned readings give the same picture for the others: `R = 3` is blocked for `ρ_7 ∈ (7.667, 8.333)` and displaced to `3.4 = 3 + 2/5`; `R = 5` for `(7.8, 8.2)` to `5.667 = 5 + 2/3`; `R = 7` for `(7.857, 8.143)`.
- **Not done:** the same split for deformations of more than one runner; whether (ii) and (iii) are one family of gaps with the ideal's events as special cases.

## E309 — 2026-10-02 — owner: "do the same tracking for a deformation of two runners for all sorts of arrangements; notice that if we keep those runners the same and move the other we don't change the isolation point of the frozen runners"

**Map:** two readings (movers) deform linearly, the others frozen; `R = 8·d_min·t` in the base unit; landing = first lonely `R`. Scripts and outputs `LonelyRunner/experiments/nN/redo/two_mover_track_v1.{py,out}` and `two_mover_frozen_v1.{py,out}`; exact Fractions. Bases: AP (speeds `s+1 … s+7`), grids `(1,2,3,4,5,6,15)`, `(1,2,3,4,5,7,14)`, `(9,2,3,4,5,6,7)` (`d_min = 2`), `3·AP`; 90 runs (all 21 mover pairs twice for the AP, six random pairs twice for each other base). Descriptive; no rate is claimed.
- **Frozen runners `[VERIFIED — asserted in every one of the 90 runs, every step]`:** `L(V(s)) = L(frozen) ∩ L(movers)` (each reading's clear set depends on that reading only), and the landing always lies inside a component of `L(frozen)`. The list of components of `L(frozen)` is fixed for the whole path; the movers only select which components contain a lonely point. In the six AP runs with the fastest runner moving (`two_mover_frozen_v1.out`) the landing visits the frozen components in one order: the component at `R ≈ 1` (displaced by the movers), then `R = 3` (or `R = 5` when reading 3 is a mover), then the frozen gap just before `R = 7/3` (`2.25–2.333`; `2.2078` and `2.2667` when 4 or 3 move), then the first component again at `9/ρ_7` (`1.0588 … 1.1538`).
- **AP, movers both within readings 2–6 and above the smallest reading (18 runs):** the landing stays within `0.5` of `R = 1` at every step in all 18. (The other two runs in that range have a mover sent to `0.3`, below `d_min`, which changes `d_min`.) The first event depends on the pair `(1, 7)` (`pair_law`), so movers elsewhere leave it, as the tangency picture says.
- **AP, the fastest as a mover (12 runs):** in 9 the landing leaves the first event at some `s` (to `R = 3`, then the gap at `2.25`, then back near `R = 1`), the one-mover pattern of E308. **The smallest reading as a mover, not the fastest (10 runs):** 3 keep the first event throughout; the others change `d_min`'s scale.
- **Other bases:** the landing stays at the base's first component in most runs and hops among that base's own components in the rest (`two_mover_track_v1.out`); the extra lonely intervals of the grid `(1,2,3,4,5,6,15)` give additional components to hop between.
- **Not done:** deformation of more than two runners; a statement of which frozen component the landing picks in terms of the movers' edges.

## E310 — 2026-10-02 — owner: "track deformation of three and four runners the same way … build a map of how the cascade works so we can show changing the speed forces the proven global isolation to happen somewhere else"

**Map:** three and four movers; the frozen runners' lonely set `L(frozen)` fixed (components `C0, C1, …` in order of `R`); each component is the landing or blocked by named zones `Z(ρ_m, j) = ((8j−1)/ρ_m, (8j+1)/ρ_m)` of the movers. Scripts and outputs `LonelyRunner/experiments/nN/redo/multi_mover_map_v1.py` (`_k3.out`, `_k4.out`) and `multi_mover_count_v1.py`; exact Fractions; bases as E309; 79 runs × 31 steps = 2,449 steps for each of `k = 3, 4`.
- **Asserted at every step `[VERIFIED]`:** the frozen set is unchanged along the path; the landing lies in a component of it; `L = L(frozen) ∩ L(movers)`. **No step has an empty lonely set in `(0, 9.5]`** (`multi_mover_count_v1`: 0 of 2,449 for `k = 3` and for `k = 4`). Deepest skip: 5 frozen components blocked before the landing (`AP`, movers `#1,#3,#7`, `s = 0.03`; `AP`, movers `#1,#2,#3,#6`, `s = 0.4`).
- **What the map entries look like** (`_k3.out`): `AP`, movers `#2,#6,#7` → `[2.52, 7.11, 5.92]`: for `s ≤ 0.90` the landing is in `C0`; for `s ≥ 0.93` `C0` is blocked by `#6 lap 1` and `#7 lap 1`, `C1` by `#6 lap 2`, `C2` by `#2 lap 1`, and the isolation lands in `C3`. Movers `#1,#2,#3` → `[0.9, 2.54, 3.67]`: `C0` blocked by the lap-0 zones of `#1,#2,#3` (the smallest readings now sit at `0.9`), landing in `C2`, then `C3` at `s = 0.87`, then `C1`. Each skipped component is blocked by named zones with explicit edges `(8j±1)/ρ`.
- **First component `C0`, blocked by which mover (counts of run-steps over all bases, `k = 3` / `k = 4`):** reading `#1` (the smallest, its lap-0 zone as it moves) 259+217+60 / 300+203+180; reading `#7` (the fastest) 171+145 / 173+180 (AP, `3·AP`); `#6` 87+55 / 76; the others less. Reported as a description of the map, not a rate of anything.
- **What the map says:** the isolation proven at the AP (and at every grid) never leaves the frozen runners' own components; the movers' zones select which component holds a lonely point, hopping in an order fixed by the zone edges.
- **What it does not say:** why some component of `L(frozen)` is always left unblocked. That is the existence statement again; `0` empty steps in `4,898` is a measurement.

## E311 — 2026-10-02 — owner: "you jumped; we are supposed to be mapping how the cascade locates the isolation point; keep mapping"

**Map:** the cascade's own path under deformation of `k = 1…4` runners, and on the real residual members: per move, the blockers, the setter, and how each new blocker got in (`carried` = clear at the old state, shifted by `ρ·ΔR` eighths; `returned` = a blocker that left and re-entered at the next lap). Scripts and outputs `LonelyRunner/experiments/nN/redo/cascade_path_map_v1.py` (`_k1…_k4.out`), `cascade_path_pins_v1`, `cascade_path_members_v1`; exact Fractions; AP and three grids, 30 runs × 31 steps per `k` (1,860 paths each; deformations of `−1.5 … +2.5` in units of `d_min`).
- **Paths with no move** (`R = 1/ρ_min` already lonely, the ideal's first event unmoved): 1,577 of 1,860 (`k=1`), 1,199 (`k=2`), 1,301 (`k=3`), 1,102 (`k=4`). Longest path: 14 moves.
- **First move's setter** is a deformed runner in 185 of 283 (`k=1`), 459 of 661, 420 of 559, 467 of 758 (`k=4`); at moves 2 and 3 of the single-mover runs every setter is frozen (210 of 210): the deformed runner blocks `R = 1` and leaves, and frozen runners carry the chain.
- **Every new blocker is carried in**; none returns for `k = 1, 2, 3`; 4 returns in about 4,000 carries for `k = 4`.
- **Single deformed runner, move 1:** the carried blocker is the reading pinned on the entering edge at `R = 1` (position exactly 7) in 35 of 37. Example (speeds `s+1 … s+5` frozen, the runner at `s+6` moved to `s+8.07`, the runner at `s+7` frozen): `R = 1` blocked by the moved runner (its lap-1 zone), exit `R = 1.1152`; there the frozen runner at `s+7` is carried (position 7.00, shift 0.81 eighths); its exit `R = 9/7 = 1 + 2/7` is lonely. For more movers, readings at position 6.0 are carried too (119 of 328 at `k = 2`), by the larger shift.
- **Shift sizes of the carried blockers (`k = 1…4`):** at move 1, below one eighth in 51 of 152 (`k=1`) and 103 of 470 (`k=2`), the rest `1–3` eighths (a few `≥ 3`); from move 2 on, below one eighth is rare (0 of 60 at move 2 for `k=1`; 22 of 354 for `k=2`): carry-in is lap-scaled, not slot-scaled.
- **Real members** (`cascade_path_members_v1.out`): B1 (47): 1–5 moves, setter at move 1 of rank 6 in 20, 5 in 12, 7 in 10; carried 35 by `1–3` eighths and 15 by `< 1` at move 1; 0 returned; last setter on lap 1 in 44 and lap 2 in 3. C1 (547): 1–7 moves, the first setter a cluster reading of any rank 2–7 (188, 125, 87, 66, 44, 37), carried shifts `1–3` 243, `≥ 3` 160, `< 1` 57 at move 1; 23 returned in all; last setter on laps 4 to 46.
- **Not done:** the carried blocker at moves `≥ 2` as a zone of the chain (`Z(b, j)` starting before the previous exit), per class; the returned blockers of C1 (a blocker that left and re-entered) in terms of lap.

## E312 — 2026-10-02 — owner: "keep testing until you know how every move works … no arrangement change that you don't know how the cascade will deal with"; mid-turn: "it seems like double handling … maybe just accounting"

**Map:** the cascade's move sequence along a linear deformation of `k` runners, as the order type of the zone edges `σ = (8j−1)/ρ`, `ε = (8j+1)/ρ`. Scripts and outputs `LonelyRunner/experiments/nN/redo/transition_catalogue_v1`, `effective_crossings_v1` (the rule), `effective_crossings_run_v1`, `effective_prefix_v1`, `effective_debug_v1`; exact Fractions.
- **On "double handling":** the move out of a given state (blockers = the zones containing `R`, setter = the zone with the largest end, carried = zones whose start the exit passes) is the cascade's definition; re-deriving it is accounting. What is not a restatement is the rule for how the path changes when the arrangement changes: it is a statement about a whole family of arrangements, which a run of the cascade on one arrangement is not.
- **Which edge crossings change the move sequence `[VERIFIED]`:** 329 observed changes over 7 bases (AP, three grids, three mixed rational arrangements; `k = 1…4`) all coincide with a predicted start–end or end–end crossing; start–start crossings were never needed (156 of 229 changes are not explained by them, all 229 by the other two kinds); start–end alone leaves 51 unexplained, end–end alone 151.
- **The rule (path `R_0 … R_n`, `R_0 = 1/ρ_min` = the largest `j = 0` end, `R_{i+1} = ε` of the setter `A_i`):** the move sequence changes exactly at: A `σ_Z = R_i`, `i < n`, with `ε_Z > R_{i+1}` (Z outlasts the setter); A′ `σ_{A_i} = R_i` (the setter stops blocking); B `ε_Z = R_n`, `σ_Z < R_n`, `j ≥ 1` (Z straddles the landing); C `ε_Z = R_{i+1} = ε_{A_i}` with Z a blocker at `R_i` (setter swap); D `ε_{A_i} = R_i` (the move has length 0); `σ_Z = R_n` always. Start–start crossings and every other start/end crossing are silent. The start state `R_0` may be defined by any runner that is the smallest at the crossing.
- **Test:** 600 random linear deformations (12 bases incl. wide, clumped and random readings; `k = 1…6` movers; random `s_0`): the rule's earliest effective crossing after `s_0` equals the cascade's next change in 598; the other 2 are an effective crossing at `s = 1` exactly, not observable by sampling (the first version, with the rule missing D, the `j = 0` case of B, and the start-state definer, matched 80/90, 173/180, 585/600).
- **Locality `[VERIFIED]`:** at 170 effective crossings the move sequences just before and after share a prefix of exactly `i` moves (types A, A′, B, D: 153) or `i − 1` moves (type C, setter swap: 17), none other: the path is unchanged up to the state the crossing involves and recomputed from there.
- **Not done:** the update of the tail after a crossing as a rule (it is the cascade continuing from the new state); the same test for non-linear deformations; Lean statements of the five crossing types.

## E313 — 2026-10-02 — owner: "test the tail update rule next … when it jumps or hops … scale invariance and the never-ending grid … reduce the types of arrangements"

**Map:** the lonely set `L(s)` = the gaps of the union of the open zones `Z(ρ_b, j) = ((8j−1)/ρ_b, (8j+1)/ρ_b)`; the isolation spot = the left end of its first component. Scripts and outputs `LonelyRunner/experiments/nN/redo/tail_update_v1`, `hop_is_gap_event_v1`, `ap_single_mover_map_v1` (`.out`); exact Fractions.
- **Tail `[VERIFIED]`:** over 1,493 effective crossings (10 bases, `k = 1…4`): the landing `R*` is continuous in 855 (57%); a forward hop in 344, a backward hop in 294 (median size 0.13 / 0.12; 90th percentile 0.61 / 0.84; 11 forward and 22 backward hops exceed 1; largest 6.2). When the landing changes, the new path shares no state with the old tail in 637 of 638: the tail is a new cascade from state `R_i`, not a modified old tail. The landing's flank (mover/frozen) before → after takes all four combinations (e.g. backward hops frozen → mover 86, mover → mover 68, frozen → frozen 13): hops do not go to frozen edges only.
- **A hop is a birth or a death of a component of the lonely set `[VERIFIED — 1,716 effective crossings, 0 exceptions]`:** the landing is continuous in 1,065; a forward hop is exactly the death of the first component (length → 0 at a start–end tangency) in 335; a backward hop is exactly the birth of an earlier component in 316; no other kind occurs. The spot slides while its component persists. The AP is the arrangement where all four components are tangencies of length 0 (the pair law: under deformation one of each pair `(a, 8−a)` is born with positive length and the other dies).
- **One deformed runner of the AP, complete for `ρ ∈ (0.35, 14)`, all seven runners (`ap_single_mover_map_v1.out`):** (1) the class event `R = a` (`a = 1, 3, 5, 7`) is lonely iff `a·ρ mod 8 ∈ [1, 7]` for the moved runner (`ρ` its new reading): event 1 dies exactly for `ρ ∈ (7, 9) + 8ℤ`, event 3 for `8 ± 1/3`, event 5 for `8 ± 1/5`, event 7 for `8 ± 1/7`. (2) For a moved runner with reading `ρ ∈ (1, 7)` the landing is `R = 1` unchanged, every runner `m ≥ 2`. (3) With the mover in the subject's slot (`ρ ∈ (7, 9)`) the landing depends on the runner: mover = reading 6: `9/7` (the entering reader's exit); 5: `3/2`; 4: `9/5` on `(7, 25/3)` then `17/ρ`; 3: `17/7`; 2: `3` on `(7, 23/3)`, `25/7` on `(23/3, 25/3)`, `3` on `(25/3, 9)`; 7: `3` on `(7, 51/7)`, `17/ρ`, `9/4` on `(68/9, 54/7)`, `9/ρ` on `(54/7, 9)`. At `ρ = 8` (a multiple of 8 beyond the AP) all four class events are dead and the landing is `9/8, 9/7, 3/2, 9/5, 17/7, 25/7` for the mover = reading `7, 6, 5, 4, 3, 2` (all explained by the lap-1 zone chain of the frozen AP runners, then the lap-2 zone of reading 7, then lap 3). (4) A mover with `ρ ∈ (15, 17), (23, 25), (31, 33)` (two to four laps) has no hop: `R* = (8j+1)/ρ`, its own exit, because a lap-`j ≥ 2` zone ends at most `1 + 2/(8j−1)·…` before the next frozen zone starts (`17/ρ ≤ 1.133 < 7/6`); the lap-1 case `(7, 9)` has four regimes.
- **Reductions seen:** (a) at a class instant only `ρ mod 8` of each reading matters (the lap is invisible); (b) two zones of consecutive readings `x < y` at lap `j` chain only if `y/x ≤ (8j+1)/(8j−1)`, `9/7` at lap 1, `17/15` at lap 2, `→ 1`, so chains, hence hops, are confined to the lowest laps; (c) a reading `ρ` has no zone before `R = 7/ρ`: it is clear on `[1/ρ, 7/ρ]`, so slower readings do not enter a path that ends before `7/ρ`.
- **Not done:** the same catalogue for two deformed runners of the AP; for the grids with extra laps; whether the types in (b) give a finite list.

## E314 — 2026-10-02 — owner: "we have heaps of tokens"; keep mapping (two deformed runners; grids; reduction of types)

**Map:** the landing in the plane of the new readings `(ρ_a, ρ_b)` of two deformed runners of the AP (others at readings 1..7, `d_min = 1`). Script and output `LonelyRunner/experiments/nN/redo/ap_pair_map_v1.{py,out}` (7 pairs, 64 × 64 cells, exact Fractions at the cell centre).
- **Cross structure `[VERIFIED — the maps]`:** `R* = 1` (the ideal's first event unmoved) everywhere except the strips where a deformed runner sits in the slot band `ρ ∈ (7, 9) + 8ℤ` at `R = 1`; each map is a cross of such strips (vertical = runner `a` in the band, horizontal = runner `b`). On an arm with one runner in the band the landing is the single-runner catalogue (E313) of that runner; the other runner changes it only where its own lap-1 zone enters the chain (e.g. readings 6 and 7, `ρ_7 ∈ (5.5, 6.4)` inside `ρ_6 ∈ (7, 9)`: landings `3.000`, `2.25–2.33`); the square where both are in the band has its own plateaus (`2.250`, `3.000`, `3.459`, `3.497`, `5.000`).
- **Region geometry:** plateaus where the flank is frozen (constant `R*`) and bands where it is a mover (`R* = (8j+1)/ρ`, varying along one axis); boundaries are straight lines through rational points (the homogeneous linear equalities of `HandoffDriftN`). A bounded window has a finite number of cells.
- **What the grid's scale invariance does and does not give:** the status of every integer-`R` event depends only on `ρ mod 8` of each reading (laps invisible), so on the class events `ρ → ρ + 8` changes nothing. It does not carry over to the landing when it is not a class event: the fastest runner with reading in `(7, 9)` has four regimes (E313); with reading in `(15, 17)`, `(23, 25)`, `(31, 33)` it has none (`R* = (8j+1)/ρ`). The zone width `2/ρ` and the chain condition `y/x ≤ (8j+1)/(8j−1)` make the structure near `R = 1` depend on the speeds, not only on `ρ mod 8`.
- **Not done:** the grids with extra laps as the frozen set; a classification of the chain type by lap level; the three-runner version of the strip structure.

## E315 — 2026-10-02 — owner: categorise arrangements by RESULT; find many different arrangements; keep mapping the cascade, not a proxy

**Map:** the cascade's own output, no derived quantity: the path signature `((rank of the setter among the sorted readings, lap), …)` and the landing; readings normalised to `d_min = 1`; exact Fractions. Scripts and outputs `LonelyRunner/experiments/nN/redo/result_classes_v1`, `result_discovery_v1`.
- **Sample:** 6,347 arrangements (random log-uniform, AP deformed, complete grids with extra laps and deviation, clump + outliers, the 47 B1 and 300 C1 members): 719 distinct paths. Number of moves 0 / 1 / 2 / 3 / 4 / 5 / 6+: 2,712 / 2,033 / 948 / 398 / 139 / 69 / 48.
- **Same result, different arrangements:** the result "R = 1 lonely" (no reading's position `ρ mod 8` in `(−1, 1)`) is shared by 2,712 arrangements of all four families. Single-move results such as `5.1` (243: random 126, clump 68, grid+laps 44, B1 2) have the one reading of rank 5 in the slot band `ρ ∈ (7, 9)` and every other reading clear at its exit `9/ρ_5`; the box of the class is `ρ_(5) ∈ (7.01, 8.98)`, `ρ_(6), ρ_(7) ≥ 7.13`, the rest below `6.8`. `7.1 6.1` (117): `ρ_(7) ∈ (7.04, 9)`, `ρ_(6) ∈ (5.61, 7)` (overlap `ρ_6 > 7ρ_7/9`).
- **The B1 members:** 22 results in 47 members, all lap-1 staircases in descending rank (`6.1 5.1` 10, `5.1 4.1` 5, `6.1` 4, `6.1 4.1` 4, …), the longest `7.1 5.1 4.1 3.1 7.2` and `5.1 4.1 3.1 7.2 6.2`.
- **Discovery curves (distinct setter-rank results after n = 100 / 200 / 400 / 800 / 1600):** AP deformed `14, 20, 30, 36, 42`; near-chain `7, 9, 14, 16, 18`; scaled AP `9, 10, 12, 16, 24`; clump `20, 30, 38, 49, 63`; random `21, 32, 44, 70, 111`; grid + laps `26, 43, 70, 101, 159`; integers ≤ 40 `34, 50, 77, 125, 193`; rational `28, 39, 63, 88, 145`. The AP-based and near-chain families flatten; the others keep adding rare long paths.
- **Longest paths** (6–13 moves) are near-AP or near-grid arrangements: scaled AP `1, 2.005, 2.975, 4.01, 5.013, 6.01, 7.018`: 11 moves `7.1 6.1 5.1 4.1 7.2 3.1 5.2 7.3 2.1 7.4 5.3`, landing `R* = 4.9875` (the AP's third event displaced); integers `(5,12,19,23,29,32,40)/5`: 11 moves, `R* = 4.47`; rational: 13 moves.
- **Links between consecutive setters `[VERIFIED on 2,717 links; derived]`:** `(rank down, lap same)` 1,400; `(rank up, lap +k)` 1,000+; `(rank down, lap −k)` 330+; never `(rank up, lap ≤ 0)` nor `(rank down, lap + )` nor the same rank. Derived: if `ε_x = (8j+1)/ρ_x` lies in the zone `((8j'−1)/ρ_y, (8j'+1)/ρ_y)` then `ρ_y < ρ_x ⇒ j' ≤ j` and `ρ_y > ρ_x ⇒ j' > j` (a slower reading cannot enter at a higher lap, a faster one cannot enter at the same or a lower lap).
- **Not done:** grids with extra laps as the frozen set in the strip maps; the three-runner version of the strip structure; the defining inequalities of a result class (chain overlaps, and for each visited state the other zones' relation to the setter's end).

## E316 — 2026-10-02 — owner: do the grids with extra laps and the three-runner strips; plan to try more arrangements; exhaustion is acceptable with a log of look-alikes

**Map:** one deformed runner with a complete grid (residues `1..7` mod 8, extra laps) as the frozen set; three deformed runners of the AP; the exhaustion plan. Scripts `LonelyRunner/experiments/nN/redo/grid_single_mover_map_v1`, `strip3_v1`, `inert_equivalence_v1`, `symbolic_cells_v1` (running); docs `docs/n8/EXHAUSTION_PLAN_v1.md`, `docs/n8/ARRANGEMENT_EQUIVALENCES_v1.md`.
- **Grids with extra laps `[VERIFIED — exact]`:** with the frozen set a complete grid, event 1 (`R = 1`) dies exactly for the moved runner's reading in `(7, 9) + 8ℤ`, as for the AP. The displaced landing is set by the frozen reader with residue 7 (the pinned entering reader at `R = 1`, position exactly 7): any rightward move of `R` puts it in its zone, so the landing is at least `1 + 2/ρ_E`. AP: `ρ_E = 7`, `9/7 = 1.2857`; grid `(1,2,3,4,5,6,15)`, `ρ_E = 15`: `17/15 = 1.1333` (mover reading 6, `ρ ∈ (7.941, 9)` and `(15,17)`); grid `(1,2,3,4,5,6,23)`: `25/23 = 1.0870` (mover `ρ ∈ (8.28, 9)`); grid `(1,2,3,4,5,7,14)`: `9/7`. Extra laps on the entering reader shrink the displacement (`2/ρ_E`).
- **Three deformed runners of the AP `[VERIFIED]`:** no runner in the band (`ρ mod 8 ∈ [1, 7]` for all three): the landing is `R = 1` in all 1,070 cases. Exactly one in the band (983): the one-runner catalogue (the same runner moved, the others at the AP) predicts the landing in 229; the landing is lower in 625 and higher in 129, because the other movers have removed or replaced the pinned readers that fix the AP's chain. Two in the band (306) and three (39): landing above 1. So the strip structure of the first event holds in three dimensions, but the landing inside a strip is set by the frozen readers at their positions, not by the AP.
- **Inert readings `[VERIFIED — exact]`:** 7,719 inert readings in 1,500 arrangements (about 5.1 of 6 per arrangement); 61,752 replacements by values clear at the visited states: the state sequence unchanged in all.
- **Plan:** symbolic enumeration of the cascade tree over polyhedral cells in a lap window (EXHAUSTION_PLAN_v1); equivalence log started with seven entries and the inert check.

## E317 — 2026-10-02 (autonomous run; owner away) — enumeration by cells, extremes, the cluster window, exceptions

**Program (owner):** run autonomously until tokens run out or (a) a definitive finite list of arrangements and (b) a complete understanding of the cascade; keep logs; a thorough summary of what is proven versus open is to follow; the finite list may be achievable (scale, variation and the conjecture's own constraints reduce the arrangements). **Status of the aim:** neither (a) nor (b) is reached; what follows is evidence and its limits.
- **Enumerations (exact cascade as the check):** `symbolic_cells_v1.py` (cells split by every clear/blocker window; stopped after 20,200 nodes, 11,448 leaves at 2,056 s, depth 29: too fine); `path_tree_v2.py` (branches on the setter and on possible straddlers only; window `ρ_7 ≤ 9`; running: 22,000 nodes, 7,945 terminal, depth 29, 0 cut at 1,426 s); `path_tree_v3.py` (the same, storing every node for the partition test) and `path_tree_check_v1.py` (the test: random arrangements and LP witnesses walk the tree; at each node exactly one child or a landing). Depth 29 means paths of at most 28 moves in this window.
- **Float artefact found and removed:** the first extreme search reported "401 moves" (my cap at 400): exact arithmetic gave 2–18 moves. A position that rounds to `0.9999999…` at its own exit keeps a runner "blocking" and the loop never advances. Fixed by an edge tolerance and exact confirmation of every reported extreme (`extremes_deep_v1.py`).
- **Hardest arrangements in the one-lap window `7 < ρ_7 ≤ 9` (exact, two seeds, 60 restarts × 3,000 iterations each):** maximum number of moves 28 (both seeds); maximum landing `R* ≈ 11.95` (11.6 and 11.95): readings near `(1, 2.37, 3.15–3.3, 4.2–4.3, 5.2–5.3, 5.8–5.9, 7.45–7.67)`: a deformed AP, deviations 0.2–0.5. The landing is beyond one period of `d_min` (`R = 8`).
- **Cluster window (the slow runner below six readings; `q` = (first lonely `R'` of the six readings at or after `c`)/`c`; the slow runner is clear for `R ∈ [1, 7]`, i.e. `R' ∈ [c, 7c]`):** adversarial sup `q` found: `c = 9`: 1.48 (spread ≤ 7) and 1.35 (≤ 25); `c = 16`: 1.31, 1.24; `c = 30`: 1.18, 1.17; about `1 + 5/c`. Tight clusters (equal spacing `d`): `q ≤ 1.71` for `d = 0.002 … 0.2` and `c = 9 … 1000`. Never near 7. If this holds for all six-reading sets it settles "a slow runner below a fast cluster" without the slow runner's later windows; it is a statement about six readings only (Window Lemma W6), tested, not proved.
- **Exceptions:** `EXCEPTIONS_LOG_v1.md` (X1–X8). X6: a predicted crossing did not occur when the smallest runner changed identity at the same instant as an exact coincidence `ρ_6 = 9ρ_1`: a touch, not a crossing.
- **Hop tangencies by lap (`hop_laps_v1.out`, 383 hops):** the most frequent death or birth is the start state `R_0` (end of the lap-0 zone) meeting the start of a lap-1, lap-3 or lap-2 zone of a slower-or-faster reading (reading entering the slot band); interior tangencies are zone end `(A, j)` meeting zone start `(B, j')` with `A` faster and `j' ≤ j`, or `A` slower and `j' > j`: the link rule.
- **Running now:** cluster threshold over `c = 1.5 … 9`; hard-set search (largest `ρ_7` subject to `R* > T`, `T = 2 … 9`); extremes in windows 17, 25, 49; path tree v2 and v3 for `J = 1`.

## E318 — 2026-10-02 (autonomous) — why `R ≈ 12`: the class events of the hardest arrangements

**Owner:** *"I have long suspected that R = 12 is the max. But I'm not sure why."* **Map:** the hardest arrangements found in the one-lap window (E317): `R*` = 11.95, 11.93, 11.62, 10.86, … and the class events (integer `R`) that survive in them. `LonelyRunner/experiments/nN/redo/sup_refine_v1.py` and inline checks; exact positions.
- **The landing is the left end of a component that CONTAINS `R = 12`** in the two best arrangements: six other readings alone have lonely components `[11.678]`, `[11.946, 12.059]`, `[13.020, 13.100]`, … and `[11.928, 12.040]`, `[12.668, 12.732]`, … ; with `d_min` clear at `R = 12` (position `12 mod 8 = 4`, the middle of its second clear window `[9, 15]`). The landing sits just before 12 (`11.946`, `11.928`): it is the displaced event.
- **Class events (integer `R`) that survive in the four hardest arrangements:** `[12, 31, 35, …]`, `[12, 34, 39, …]`, `[14, 19, 38, …]`, `[14, 23, 25, …]`: the first surviving class event is `a = 12` or `a = 14`: an EVEN event.
- **Why the odd events die, for all laps (derived):** at an odd `a` the readings `y` (AP values `1..7`) sit at `a·y mod 8`, all distinct and nonzero; the reading with `a·y ≡ 1` (leaving edge) is `y ≡ a` and the one with `a·y ≡ 7` (entering edge) is `y ≡ −a (mod 8)`. Event `a` needs `aδ_{y≡a} ≥ 0` and `aδ_{y≡−a} ≤ 0` (mod the lap), the SIGNS of the deviations `δ_y = ρ_y − y` of one pair; the same sign condition holds for `a`, `a + 8`, `a + 16`, …. In the hardest arrangements `δ_7 > 0`, `δ_3 > 0`, `δ_5 > 0` kill the classes `a ≡ 1, 3, 5 (mod 8)` for every lap; the class `a ≡ 7` dies by magnitude (`7δ_2 = 2.6 > 1` at `a = 7`).
- **Why 12 can survive:** `a = 12 ≡ 4 (mod 8)`: the odd readings sit at `12y mod 8 = 4` (the middle of the clear arc, tolerance `|12δ| ≤ 3`) and the even readings at 0 (the subject's slot), so the event needs `12δ_2, 12δ_4, 12δ_6 ∈ [1, 7] (mod 8)` and `|12δ_3|, |12δ_5|, |12δ_7| ≤ 3 (mod 8)`: in the best arrangement `δ_2 = 0.37, δ_4 = 0.20, δ_6 = −0.20 (≡ +0.47 mod 2/3)` and `δ_3 = 0.15, δ_5 = 0.22, δ_7 = 0.45 (≡ −0.22)`: all satisfied. `a = 4` needs `δ_4 ≥ 0.25` (fails at 0.196); `a = 20` would need even-reading deviations in a narrower window.
- **Not derived:** that `R* ≤ 12` always; the exact value comes from the exhaustive tree (running: LP supremum of `R` over every node of the one-lap tree).

## E319 — 2026-10-02 (autonomous) — the one-lap window by exhaustive tree: finite; exact supremum of the landing `26433/2209`

**Map / method:** `LonelyRunner/experiments/nN/redo/path_tree_par.py` (symbolic cascade over polyhedral cells, parallel; branches on the setter and on possible straddlers; node supremum of the state `R` by LP over the closure) and `sup_exact_v1.py` (follows the maximising path, recovers the vertex exactly with sympy). Window `1 = ρ_1 < ρ_2 < … < ρ_7 ≤ 9` (every reading within one lap).
- **Result `[VERIFIED — floating-point LP with exact checks; see the caveat]`:** the tree is FINITE: 27,517 nodes, 9,651 terminal, deepest path 29 (28 moves), 0 branches cut at depth 60, 1,001 s on 8 workers. Every arrangement of the window has a lonely instant; the cascade lands at `R* ≤ 11.966047985514`.
- **Exact supremum of the landing over the window: `26433/2209 = 11.9660479855…` (`2209 = 47²`, `26433 = 27·11·89`).** The maximising path is the 27-move chain `7.1 6.1 5.1 4.1 7.2 3.1 6.2 5.2 2.1 4.2 6.3 7.4 5.3 3.2 6.4 4.3 5.4 7.6 2.2 1.1 5.6 4.5 2.3 5.7 6.8 4.6 7.11`; the supremum is the minimum of `ρ_7` over the closure of its cell, a vertex of the polytope, `ρ = (1, 16715503/7123545, 47/15, 726761/173745, 47/9, 15463/2673, 2209/297)` (`ρ_7 = 7.4377`; the landing is `89/ρ_7`, lap 11). It is a limit of arrangements (the closure), a rigid tangent system. So in this window the maximum landing is `11.966…`, close to but not 12 (owner's suspicion: 12).
- **Partition and soundness checks `[VERIFIED]`:** 256 exact test arrangements (250 random in the window and six of the hardest known) were carried down the tree: at every node each lies in at most one child, and if in none the exact cascade lands there; every node's path is the prefix of its exact path; 0 violations.
- **Caveats (not closed):** (i) the LP is floating point with tolerance `1e-9`; a very thin cell could be pruned wrongly; the 256 tests do not exclude it; an exact certificate for every pruned branch (a rational Farkas multiplier) is owed; (ii) the node supremum is over closures; (iii) the window is `ρ_7 ≤ 9`; arrangements with a larger reading are not covered by this tree (the searches for `R* > 7` with `ρ_7 > 9` found none).
- **Next:** `J = 2` (`ρ_7 ≤ 17`), running (`path_tree_par_J2.out`).

## E320 — 2026-10-02 (autonomous) — the two-lap window by exhaustive tree; lap compression; searches beyond

- **Two-lap window `ρ_7 ≤ 17` `[EXHAUSTIVE, floating-point LP with exact checks]`** (`path_tree_par.py 2 3 9`, 2,832 s on 9 workers; `path_tree_par_J2.out`): the tree is FINITE: 343,070 nodes (12.5 × the one-lap window), 117,070 terminal, deepest path 29 (28 moves), 0 branches cut at depth 60; **the supremum of the landing over the window is again `26433/2209 = 11.966048` (same path, same cell as the one-lap window)**; 0 violations of the partition and soundness checks on the 256 exact test arrangements. So the extra lap added cells and no later landing.
- **Lap compression fails `[CHECKED]`** (`lap_compression_v1.py`): lowering one reading above 9 by a whole lap makes the landing later in the original in 4,922 of 31,585 pairs (largest excess 2.53, `A = (1, 2.9165, 5.0142, 6.5207, 7.0257, 8.4438, 11.5524)`: `R*(A) = 3.908`, `R*(A′) = 1.380`). The window `J` cannot be reduced to `J − 1` by removing laps.
- **Searches beyond `[SEARCH]`:** hill-climbs from lap-added copies of the extremal arrangement reach only `R* = 6.81` (window 17), `6.94` (25), `9.99` (33, an arrangement with `ρ_7 = 7.02`, inside the one-lap window); no landing above `11.966`.
- **Draft summary:** `docs/n8/CASCADE_ACCOUNT_v1.md` (written before the two-lap run; §4a to be filled).
- **Running:** sensitivity of the one-lap tree to the cell-thickness threshold (`TT = 1e-6`, `1e-12`).

## E321 — 2026-10-02 (autonomous) — the extremal vertex is tangent to the edges of `d_min`'s second clear window

The maximising vertex of the one-lap tree is `ρ = (1, 16715503/7123545, 47/15, 726761/173745, 47/9, 15463/2673, 2209/297)` (E319). `47 = 8·6 − 1`. At the vertex: the lap-6 zone of reading 5 (`ρ_5 = 47/9`) STARTS at `(8·6−1)/ρ_5 = 9`, the END of `d_min`'s first tooth `(7, 9)`; the lap-6 zone of reading 3 (`ρ_3 = 47/15`) starts at `47/ρ_3 = 15`, the START of `d_min`'s second tooth `(15, 17)`. So the rigid vertex binds against both edges of `d_min`'s second clear window `[9, 15]`, inside which the landing `89/ρ_7 = 26433/2209 = 11.966` falls (the window's middle is 12). Reading, `[derived from the vertex; the general statement is not proved]`: in the hardest arrangement the six other readings tile `d_min`'s second window from its left edge `9` up to `11.966`, a little under half of its length 6; the owner's `R = 12` is the middle of that window. Where the tiling stops is set by tangencies with the window's two edges and the fastest reading at lap 11.

## E322 — 2026-10-02 (autonomous) — threshold sensitivity of the one-lap tree; three-lap run started

- **Cell-thickness threshold `[CHECKED]`:** `path_tree_par.py 1` with `TT = 1e-6`, `1e-9`, `1e-12` (`path_tree_par_J1_TT*.out`): identical in all three: 27,517 nodes, 9,651 terminal, deepest 29, supremum `11.966048`, path the same. No cell has slack between `1e-12` and `1e-6`; a cell below `1e-12` would be missed by all three (exact certificates owed).
- **Three-lap window `ρ_7 ≤ 25`:** `path_tree_par2.py 3 3 10` running (frontier of 12,640 subtrees at depth 3 built in 104 s; an earlier attempt with 4 levels was stopped: its serial frontier was 45,540 subtrees and took 585 s). `path_tree_par2` also records, per threshold `T`, the largest `ρ_7` over nodes whose state can exceed `T`: if every cell with a state above 7 has `ρ_7 ≤ 9`, late landings are confined to the one-lap window.
- `CASCADE_ACCOUNT_v1.md` updated for the two-lap result and the threshold check.

## E323 (2026-10-02, 22:4x) -- language of the one-lap tree (window rho_7 <= 9), from stored terminal cells

**Map:** cascade path = word over letters (setter rank, lap); the tree enumerates the words the cascade can produce when rho_7 <= 9.
Artifact: `LonelyRunner/experiments/nN/redo/terminals_J1.pkl`, `language_J1_v1.out`, `path_tree_par3_J1.out`.
- 9,651 terminal cells carry 6,705 distinct words (several cells share a word, differing in the landing range); 17,399 prefixes; lengths 2..29 (mode 22); alphabet 47 letters, laps up to 11.
- Within every word, a rank that recurs always does so on a strictly higher lap (0 exceptions in 9,651), matching the link rule for the repeated setter.
- NOT a Markov language: successor set depends on more than the last letter (42 of 47 last-letters have more than one distinct successor set); mean successors 6.6 / 3.0 / 2.2 for context length 1 / 2 / 3. The words are therefore not a regular grammar on the last move; the cell geometry (the LP) carries the state.
- Sup landing 11.966048 unchanged; late landings (state able to exceed T) have rho_7 closure at most 9.0 for T = 3..9, and 8.70 / 8.37 / 7.86 for T = 10 / 11 / 11.5.
**Consequence:** the one-lap map is a finite list of 9,651 cells / 6,705 words, not a grammar; no state-reduction found. Three-lap tree still running (9,975+/12,640 subtrees, 0 violations).
