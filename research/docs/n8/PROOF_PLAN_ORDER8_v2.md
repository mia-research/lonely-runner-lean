# Order eight: plan to complete the proof (v2, the residual route)

2026-09-27. Supersedes `PROOF_PLAN_ORDER8_v1.md` (kept unchanged). Owner's decision (chat, 2026-09-27): write the plan
on the residual route, with the target "every residual set is lonely", split at `24·d_min` into Case B (certificates)
and Case C (open). Running record: `docs/n8/RUNNING_LOG_order8_v1.md` (E104 is the review this plan follows from; E105
records this plan and its loss check). Lean paths are relative to `LonelyRunner/LonelyRunner/`, experiments to
`LonelyRunner/experiments/`. This draft was repaired against a `compile-diff` loss report before its first commit.

**Method.** v1's owner direction stands: *"any gap can be closed by taking the type of arrangement, permuting it via the
cascade to map what and how the deformation works."* Sharpened by the owner on 2026-09-27 (E102): **the cascade is the
oracle.** It finds the isolation of any arrangement; the work is to extract the mechanism it uses. On any exception to a
stated rule, perturb the exception through the cascade; if an explanation and the cascade disagree, the explanation is
wrong. Every statement in this plan names **where** the isolation is for a stated class of arrangements, checkable
against the cascade (memory `feedback_n8_cascade_is_the_oracle_2026_09_27`). Each open case is worked: map, law, lemma,
proof (v1's four steps).

---

## 1. Why the route changes

Two reductions are proved in Lean, axiom-clean (Spec gate PASS 2026-09-27, 1,624 declarations):

| route | statement | what it owes |
|---|---|---|
| v1 | `EndRunnerN.lonelyRunnerAt8_of_slowest`, then `SlowestSkeletonN.lonelyRunnerAt8_of_cases T`: the conjecture from `CaseB8 T ∧ CaseC8 T`, Case A by R1 (`lonely_eight_of_spread`, `ratio_condition`) | Cases B and C on **every** set of seven distinct positive whole-number readings |
| **v2** | `OrderEightN.lonelyRunnerAt8_iff_residual` (both directions): the conjecture holds **exactly when every `EightResidual` set is lonely at `1/8`** | the same, but **only on residual sets**: the sets on which every proved opening has failed |

Route v2 owes strictly less, and it is an equivalence, so nothing is lost by taking it. `CaseB8` and `CaseC8` stay
registered OWED in the tree as sufficient routes, off the path.

## 2. The target

```
LonelyRunnerAt8  ⇔  ∀ R, (∀ d ∈ R, 0 < d) → EightResidual R → Lonely8 R        [PROVED, Lean]
```

`EightResidual R` (`Spec/OrderEightCasesN.lean`, `structure EightResidual`) keeps a set of seven positive whole-number
readings only if all of the following hold (each exclusion is a proved rule that isolates the set otherwise):

- **Size and factor:** seven readings; one odd; no common factor (a common factor is removed by the halving induction,
  `lonely_eight_nat_of_residual`).
- **Ladder:** some reading divisible by each of 5, 6, 7 and 8 (so no `1/q`, `q ≤ 8`).
- **Spread:** `7a < b` for some pair (so R1, Case A, fails).
- **Descent:** the non-multiples of 8 cost at least 8.
- **Flanks:** no free flank; the shifted flank fails; `not_fast`: **no reading is more than 7 times every other**
  (`∀ V, ∃ s ≠ V, V ≤ 7s`; one-sided, so the least reading may lie far below all the others); no first-lap clearance
  `d·(8k+1) ∈ [e, 7e]` at any reading `e` and any `k`; no `−7` opening.
- **Rational openings:** no rational opening `RationalOpening8 S N (e/N) i` at any reading `e` with `N ∣ e`, for
  `N ∣ 8` (that is `N = 1, 2, 4, 8`), `N = 3`, `N = 5`, `N = 6, 7, 9`: together every `N` from 1 to 9.
- **Resolutions:** no `ResolutionClears8 S D j` for any `D ≤ 64` and any `j` (`D` need not be a reading). A case
  boundary, not a claim (`OrderEightCasesN.lean` §2g; MANUSCRIPT_v21 §17C).
- **Separation of scale:** no fast pair (two readings each at least 9 times every other); no block split (a block with a
  common factor at least 28 times every reading outside it).

## 3. What the residual already excludes, in the framework's views

**The converse step.** A field negates a class condition, and the Lean lemmas prove class ⇒ lonely only
(`band_of_class`, `lonely_eight_at_rationalOpening`). The converse holds by the same arithmetic: at the instant
`i/N + 1/(8NM)` the reading is `M·c + r` with `0 ≤ r < M` modulo `8NM` (`rationalOpening_reading`), so the reading lies
in the band `[NM, 7NM]` exactly when `c ≥ N` and (`c < 7N`, or `c = 7N` with `r = 0`): the class condition. So
`RationalOpening8 S N M i` holds exactly when every reading is clear at `i/N + 1/(8NM)`, and likewise
`ResolutionClears8 S D j` exactly when every reading is clear at `(8j+1)/(8D)`. `[PROVED — in the text; the converse,
e.g. classClear_iff_band, owed in Lean (WP2)]`.

With it, the explicit views of E86–E100 are inside the residual's fields `[PROVED — in the text, on the converse above]`:

| view (Lean lemma) | its instant | excluded by |
|---|---|---|
| the bound, exact grid form | `1/(8·d_min)` | rational opening, `N = 1`, `i = 0`, at `e = d_min` |
| ladder `a/q`, `q ≤ 8`, any `a` coprime to `q` | `a/q` | the fields `five`, `six`, `seven`, `eight` (6 covers `q = 2, 3`; 8 covers `q = 4`): a reading divisible by `q` sits on a whole lap at `a/q` |
| rung R1 forward (`rung_r1_nat`, `2 ≤ q ≤ 8`) | `a/q + 1/(8m)`, `m` the least multiple of `q` | rational opening at `e = m`, `N = q`, `i = a` (`q = 9` would also be excluded, by `no_six_seven_nine`) |
| rung R1 backward (`rung_r1_backward`) | `a/q − 1/(8m)` | the mirror: for whole-number readings lonely at `s` iff at `1 − s` (`GrandReturnN.lonely_mirror`, `lonely_add_int`), and `1 − (a/q − 1/(8m)) = (q−a)/q + 1/(8m)`, the forward rung |
| grid nudge forward (`nat_nudge_forward`, `grid_nudge_forward`) | `a/8 + 1/(8·d₀)`, `8 ∣ d₀` | rational opening at `e = d₀`, `N = 8` |
| grid nudge backward (`grid_nudge_backward`) | `a/8 − 1/(8·d₀)` | the mirror, to `(8−a)/8 + 1/(8·d₀)` |
| half lap (`half_lap_r1`) | `1/2 + 1/(8m)` | rational opening, `N = 2` |
| reverse R1 (its hypothesis form) | `9/(8e)`, others in `[e/9, 7e/9]` | `no_first_lap` at `k = 1` (`e ≤ 9d ≤ 7e`) |

So adding those views as new fields would add nothing. This corrects the session's own recommendation in chat after
E104 (to add them as exclusions); E104 itself makes no such recommendation. What the residual does **not** yet exclude:
- the next opening `9/(8e)` of a reading `e > 64`, in its exact (modular) form. At readings `≤ 24` this family is
  E100's second largest (63,806 of 346,104 cascade landings); all of those have `e ≤ 24`, so they are excluded by the
  resolution field, and the figure is the family's frequency, not a count of anything the residual leaves;
- rational openings with `N ≥ 10` at a reading `e > 64`;
- the flank sum (`FlankSumN`), whose opening index is not named.

**Where a residual set's isolation is** `[PROVED — in the text, on the converse above; Lean owed (WP2)]`. By Theorem 6.15
(`ScaleCandidates.lonely_iff_exists_candidate_scale`, existential), a whole-number set lonely at some instant is lonely
at some opening `(8K+1)/(8e)` of some reading `e`. Writing `g = gcd(K, e)`, that opening is the rational opening
`i/N + 1/(8e)` with `N = e/g`, `M = g`, `i = K/g`. The residual excludes it when `N ≤ 9` or `e ≤ 64`. Hence:

> **If a residual set is lonely, it is lonely at some opening `(8K+1)/(8e)` of a reading `e > 64` whose rung
> denominator `e/gcd(K, e)` is at least 10; equivalently, every lonely opening of a reading of a residual set has these
> two properties.**

This is the place the mechanism has to reach for residual sets. In the exhaustive data up to 24 the cascade's landing
has `e/gcd(K, e) ≥ 10` in 107,049 of 346,104 sets (`redo/rung_landing_v1.out`: 108,428 above 8, of which 1,379 at
`q = 9`), so rung denominators of that size are ordinary landings.

## 4. The case split on the residual

| case | condition on a residual set | status |
|---|---|---|
| A | `d_max ≤ 7·d_min` | **empty**: the `spread` field (this also subsumes v1's WP5 B3, widening A: the first-lap and `−7` rules are residual fields; further widening is WP5) |
| **B** | `7·d_min < d_max ≤ 24·d_min` | **VERIFIED, not Lean**: the climb-cell certificates cover every real reading set in this band (event by `R = 15`; E49–E52, E66; `climb_cells_v3_B9_bands2`, `_B12_S9_bands2`, `slabs_band1.log`); positive control `band1_control_v1` 38 of 38, covering `S ≤ 9`; no late climb with `S > 2993/273` is known, so the slabs above rely on the same code path |
| **C** | `d_max > 24·d_min` | **open** |

The B/C boundary is fixed at 24 by the owner's decision; v1's WP6 (extend the slabs past 24, `run_slabs_band1.sh`)
remains an option, not a planned step.

What is known about each:
- **Members exist.** The residual is empty on every 7-subset of `[1, 40]` (`nN/eight_residual_count_v6.out`), but it is
  infinite. E10 constructed 22 scale-free members (`nN/residual_members_v4.out`; `v3` found none: the smallest reading a
  multiple of `8·lcm(1…64)`, the rest hill-climbed through every field then in force); their `d_max/d_min` is 7.12 to
  8.83, so all are **Case B**, and each clears at the first live lattice `D = 67`. Whether they satisfy the fields added
  since E10 is owed a check (WP3).
- **No Case C residual member is known.** E10's separated families (a fast pair; a fast block with a large common factor)
  are now excluded by `no_fast_pair` and `no_block_split`. A Case C residual set has spread above 24, no reading more
  than 7 times every other, no pair 9 times faster than the rest, and no block split. Because `not_fast` is one-sided,
  the least reading may still lie far below the others (for example `d_min = 1` with the rest in `[100, 700]`).
- **Stale item closed.** Handover v4 §5.6's residual sets `(2,12,15,21,32,34,38)` and `(4,7,8,15,29,36,37)` are in
  `[1, 40]`, so not in the current residual; the cascade isolates them at `R* = 34/21` and `36/29` (E104).

## 5. Work packages

**WP1 — the skeleton on the residual (Lean, small).**
- Register `ResidualB8` (residual, `d_max ≤ 24·d_min`) and `ResidualC8` (residual, `d_max > 24·d_min`) as OWED Props.
- Prove `LonelyRunnerAt8 ⇐ ResidualB8 ∧ ResidualC8` through `lonelyRunnerAt8_of_residual`, with the `spread` field
  discharging Case A.
- *Check:* Spec gate PASS; `#print axioms` on the new top theorem shows only the three.

**WP2 — where a residual set's isolation is (Lean).**
- The converse of §3: `classClear_iff_band` (the class condition iff the reading lies in `[NM, 7NM]`), and the matching
  iff for `ResolutionClears8`.
- §3's statement: if a residual set is lonely, it is lonely at an opening `(8K+1)/(8e)` with `e > 64` and
  `e/gcd(K, e) ≥ 10`; and the target restated: a residual set is lonely iff some reading `e > 64` has a lap `K` with
  `e/gcd(K, e) ≥ 10` and `ResolutionClears8 S e K`.
- *Output:* the residual statement in the cascade's own terms (a reading's own candidate scale).

**WP3 — the test bed: residual members, exact.**
- Re-check E10's 22 members against the current `EightResidual` fields (exact, every field), and record the cascade's
  landing `(e, K)` for each.
- Build members by shape, in both cases: the owner's shapes of the gap vector (v1: (a) evenly spaced, (b) clumped with
  outliers, (c) evenly spaced with a clump) as well as E10's separation-of-scale constructions; Case B (spread 7 to 24)
  and Case C (spread above 24, no fast pair, no block split). Record each landing and its rung denominator
  `e/gcd(K, e)`.
- *Output:* the arrangements the remaining proof is about, with every landing known. If Case C has no members that can
  be built, record exactly which fields stopped the construction.

**WP4 — the mechanism on the members (the owner's method).**
- Perturb each member through the cascade: one runner and two runners at a time (v1 WP2), exact rational steps, and
  one-parameter paths.
- Record where the isolation moves, which runner opens it (`e`) and on which lap (`K`), and which runner closes the cell.
- Rules already seen, to test there: the colliders at the bound decide that the isolation moves, the runner nearest the
  entering edge decides where (E104); a repeat is a timing coincidence about one speed unit wide (E98); the spread
  against 8 sets how far (E96–E97); late events have a close pair not including the subject (E54/E55,
  `late_gap_ratio_v1`).
- *Output:* a rule naming the landing `(e, K)` from the readings, for the residual class. Every exception is perturbed
  in turn.

**WP5 — new exclusions that shrink the residual (Lean).**
- The next opening at every reading, exact form, uncapped in `e`: `no_next_opening : ∀ e ∈ S, ¬ ResolutionClears8 S e 1`
  (its lemma is `lonely_eight_of_resolution` at `D = e`, already proved).
- Rational openings at `N = 10 …` a stated cap (a case boundary).
- The flank sum as a field, if WP3 shows it acts on members.
- Each: the field, its discharge in `lonely_eight_or_residual`, the gate, and its effect on the WP3 members.

**WP6 — Case B into Lean.** As v1 WP5: B1, certificate export (each pruned cell a Farkas vector, each event cell a
witness instant, checked as generated files as `PinnedBatch` did; measure the size first), or B2, the law (the
band-0/band-1 structure, E41 and E47). Restricted to residual sets if that makes the export smaller; the certificates
themselves cover every set in the band.

**WP7 — Case C.** From WP3–WP4: the rule for where a Case C residual set's isolation lands, stated as a lemma about the
readings, proved in Lean. Tools on disk:
- nested windows (`SplitChainN.nested`, and `SplitChainN.lonely_of_split` with its window `3/(4g₁)`), the train collapse
  (`TrainCollapseN`, ratio 56), the free phase (`SyncBlockN`), and `CoreDriftN` (E65–E66);
- v1's sub-cases C-sep (separated levels) and C-compact (a tight clump) now overlap residual fields already proved (fast
  singleton, fast pair, block split), which is why they are tools here rather than cases.

**WP8 — Lean hygiene (from E102).**
- Owed lemmas: reverse R1 in its exact form, the bound-grid lemma, `Lonely8` wrappers for the whole-number view forms.
  The fields cover their instants (§3), so these serve the mechanism statements, not the residual.
- Docstrings: `ProgressionPairN` asserts the surviving interval `[a²/(8·d_a), a(8−a)/(8·d_{8−a})]` with only its left
  endpoint proved; `SlowestSkeletonN` (line 11) says Case B is verified at `T = 22`, where E66 gives 24.
- The fact "within `1/8` of `m/8`, `m mod 8 ∈ 2…6`, is clear" is proved three times (`ProgressionPairN`, `GridPairN`,
  `GridNudgeN`); refactor to one lemma.

## 6. v1 items and their fate

| v1 item | fate in v2 |
|---|---|
| §1 slowest-runner reduction (`EndRunnerN`) | proved; route v1, off the path (§1) |
| §2 Case A (R1) | proved; empty on the residual (§4) |
| §2 B/C boundary 22, "moves up as the slabs run" | now 24 (E66); fixed by the owner's decision; extension optional (§4) |
| §2 "every clump elsewhere falls in A or B" (E54/E55, `late_gap_ratio_v1`) | a route-v1 rationale; the late-event pattern is carried as a WP4 rule |
| §3 Case C window reduction (core `{g₁}` by `lonely_of_split`, window `3/(4g₁)`, closes where `(3/4)·s₂ ≥ K`) | measured in E56 (`case_c_map_v1`: 1.297 laps, 12% of room); the wait, not a window, is the object (E67–E68); the lemma stays a WP7 tool |
| §3 C-sep, C-compact | WP7 tools; overlap residual fields |
| §3 C-even, the window constant `K₆` (E31: `κ ≤ 2.76`) | superseded: worked in E57–E65 (`CoreDriftN` proved), E57's block law refuted in E68; E67–E68: "the object to bound is `n_d`, not a window". Not carried as an open item |
| WP1 skeleton | resolved by `SlowestSkeletonN` (route v1); v2's WP1 is its residual form |
| WP2 map Case C (families (a)–(c), one and two runners) | carried into WP3–WP4 |
| WP3 `block_window`, `lonely_of_split` generalised | superseded with C-even (above) |
| WP4 Case C assembled | WP7 |
| WP5 B1, B2 | WP6 |
| WP5 B3 (widen A) | subsumed: first lap and `−7` are residual fields; further widening is WP5 |
| WP6 slabs | done to 24 (E66); extension optional |
| WP7 tight points (`TwoPinnerN`, only if the deformation theorem becomes load-bearing) | carried as a conditional item: needed only if a deformation argument is used |

## 7. What "done" means

`LRC.Spec.LonelyRunnerAt8` is proved in Lean with no hypotheses, `#print axioms` shows exactly
`[propext, Classical.choice, Quot.sound]`, and the Spec gate passes with its Prop register clean. Until then the top
theorem carries `ResidualB8` and `ResidualC8` as explicit OWED hypotheses, so the gap is always visible.

## 8. Working rules

- **Exact arithmetic only** (`Fraction`, `gmpy2.mpq`); no floating point in any decision.
- **The cascade or the Boundary Set Method** for every isolation: zones open, clear set closed; cells decided by
  interior points, boundary points separately.
- **Every speed positive; no runner is ever stationary**, including when restating a reading set.
- **The cascade is the oracle** (Method, above); state where the isolation is, not only that or when it stops.
- Caps (`D ≤ 64`, `N ≤ 9`, `R ≤ 15`) are case boundaries, not claims.
- Long runs under `caffeinate` from a script file (never inline multiprocessing on macOS), with checkpoints, a progress
  file, and early positives written at once.
- Every enumeration gets a positive control that can fire; every zero is reported with its control.
- Every script and output saved and committed; the running log gets a dated entry per result.
- Grades: PROVED / VERIFIED / EMPIRICAL; no difficulty labels. New versions, never overwrites.
