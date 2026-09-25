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
