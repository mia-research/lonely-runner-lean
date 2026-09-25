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
