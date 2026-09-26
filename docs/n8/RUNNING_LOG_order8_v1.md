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
