# Order eight — the narrowings, tools and objects in hand, examined

2026-09-25, v1. Written after the two cloud sessions of 2026-09-25 (`mia-research/lrc-n8-lean`,
branches `claude/vibrant-mayer-tb6aag`, `claude/n8-pair-moduli-tests`,
`claude/manuscript-paper-cleanup-ropemz`, now merged into the local `LonelyRunner/`). Read against
`PROOF_REQUIREMENTS_v2.md`, whose contract governs: **a proof is a rule that returns `(D, a)`,
`t = a/(8D)`, `a ≡ 1 (mod 8)`, valid for every configuration, or a finite set of such rules whose
side conditions are exhaustive.**

Premise of this review (owner, 2026-09-25): the proof will not take the shape anyone expects. So
every object that a proof might be built on is checked for (i) whether it is an equivalence or a
narrowing, (ii) what a narrowing discards, and (iii) whether evidence cited for it is a mechanism or
a proxy. Nothing here ranks difficulty.

Grades: `PROVED` (Lean, axiom-clean, or a short exact argument written out), `VERIFIED` (exhaustive
on a stated range), `EMPIRICAL` (sampled), `ASSERTED`. Every figure names its artifact.

---

## 1. What is owed, exactly

`LRC.OrderEightN.lonelyRunnerAt8_of_residual` (`LRC/Spec/OrderEightCasesN.lean:805`):

> for every `R : Finset ℕ` of positive integers with `EightResidual R`, there is `t > 0` with
> `1/8 ≤ circDist (d·t)` for every `d ∈ R` ⟹ `LRC.Spec.LonelyRunnerAt8`.

`existenceAt8_iff_residual` makes the hypothesis **equivalent** to `LRC.Spec.ExistenceAt8`
`[PROVED]`. Nothing in the chain got easier: every link is an `↔` or a proved sufficient
reduction with a proved converse.

## 2. The chain of narrowings, link by link

| # | narrowing | form | what it discards | grade |
|---|---|---|---|---|
| N1 | arrangement → difference set (`LonelyRunnerAt8` ⇐ `ExistenceAt8`) | sufficient; converse holds mathematically (a 7-set is realised by an endpoint subject; smaller sets by order 7) but is **not stated as an `↔` in Lean** | the arrangement: gaps, neighbours, which subject. `Target.lean:471-477` records the owner's 2026-09-18 ruling that `ExistenceAt8` is **not the target and is off the path** | PROVED (sufficiency) |
| N2 | real → whole numbers (`existenceAt8_iff_congruence`, `existenceAt8_of_nat`) | `↔` | nothing: rank ≥ 2 merges to ≤ 6 readings, order 7 clears at `1/7`, stepping carries the instant back | PROVED |
| N3 | common factor divided out; `card ≤ 6` by order 7 | `↔` (strong induction on the sum) | nothing | PROVED |
| N4 | case list → `EightResidual` (18 fields) | `↔` | nothing formally | PROVED |

**Finding 1 (framing, not a gap).** The whole order-eight reduction the cloud sessions built runs
through N1, the difference-set form the owner took off the path on 2026-09-18. Logically this is
harmless (N1 is sufficient). The consequence for proof shape is real: a proof of the residual
statement **cannot use anything about the arrangement**, only the seven integers. If the proof's
shape turns out to need cross-subject structure (the same eight speeds serving eight subjects),
the residual formulation hides it. This needs an owner decision: is the residual the
obligation, or a sufficient route to it?

## 3. The residual as an object

`EightResidual` is a **conjunction of negated rules**. Its fields split into two kinds:

- **Positive arithmetic** (usable by any proof): `card = 7`; one odd element; no common factor;
  some element divisible by each of `5, 6, 7, 8`; `7a < b` for some pair; no element more than
  seven times every other; the cost of the non-multiples of 8 is at least 8, which leaves the
  shapes `(#mult 8, #non-mult) ∈ {(1,6), (2,5), (3,4), (4,3)*}`.
- **Negated certificate families** (usable only by a proof that goes through those same
  families): `no_first_lap`, `no_minus_seven`, `no_free_flank`, `no_rational_opening`,
  `no_thirds`, `no_fifths`, `no_six_seven_nine`. Each says "every instant in this named family is
  blocked".

**Finding 2.** Against the `(D, a)` contract: the rational opening `t = i/N + 1/(8e)`, `e = N·M`,
is `t = (8iM + 1)/(8e)`, i.e. `(D, a) = (e, 8iM + 1)`. So the rational-opening family is exactly
the contract **restricted to numerators `a ≡ 1 (mod 8M)`**, with `N` counting the candidate
numerators at resolution `e`. At `N = e` (`M = 1`) it is the unrestricted contract, which
`OrderEightCasesN` itself records as "Theorem 10 itself" `[PROVED — the reading identity
rationalOpening_reading]`. The small-`N` fields are pigeonhole budgets over `φ(N)` units.

**Finding 3 (proxy).** The window counts (12,309 → 0 on `[1,30]`, 91,523 → 7 on `[1,40]`,
`eight_residual_count_v5.out`) measure how many small sets a finite list of `N` covers. The `N`
needed grows with the window (the 7 sets left on `[1,40]` need `N = 12, 15, 16`). A fixed finite
list of `N` therefore does not close the residual, and the counts are not progress toward a proof
`[VERIFIED on [1,40]]`. This is the §4 warning of `PROOF_REQUIREMENTS_v2` in a new form: a family
that becomes complete only as `N → e` is the obligation again.

**Finding 4 (object consistency).** The seven sets left in `EightResidual` on `[1,40]` are all
among the 28 "hard sets" of session 2 (`order5_transfer_v1.out`) `[VERIFIED]`. That is expected
from the definitions: the hard sets fail the `q ≤ 8` rule at the least multiple of `q`, and the
current fields include every `N ≤ 9` at every flank. So results on the 28 bear on the residual.
The converse does not hold: 21 of the 28 are certified by the later fields.

## 4. Tools: equivalences, sufficient routes, and density

### 4a. Canonical forms: equivalences, which neither narrow the problem nor advance it

| tool | statement | grade |
|---|---|---|
| DoorFlank / flank opening | lonely ⇔ lonely at some `(8j+1)/(8e)`, `e` a disparity | PROVED (`doors_agree`) |
| mirror centre | lonely ⇔ lonely at some `K/(d+d')`, `d, d'` disparities (possibly equal) | PROVED (`MirrorCentreN.exists_lonely_mirror_meeting`, every order, real disparities) |
| cascade fixed point | the cascade's fixed point is the earliest lonely instant on its lattice | VERIFIED on 6,436 sets (`cascade_first_check_v1`); Theorem 11(b) |

Each turns "a time exists" into "one of finitely many named times works". None bounds *which*
one. **The mirror form is not of the contract's shape**: `K/(d+d') = 8K/(8(d+d'))` has
`a ≡ 0 (mod 8)`. It reaches the contract only through the cell that contains it, whose left end
is a flank opening. It is a locating tool, not an output.

### 4b. Sufficient routes, and where each stops

| route | what it needs | status |
|---|---|---|
| **length step**: drop `d_max`; the six have a cell `≥ 1/(4 d_max)` | a lower bound on the six's longest cell | only proved bound is from order 7's slack, `≥ 1/(28 d₆)`, which is R8 (`d_max ≥ 7 d₆`). Six-only form fails on 801 of 38,760 six-sets of `[1,20]`, least ratio 0.3 at `(1,2,5,6,7,8)` (session 2; **reproduced here**: longest cell `3/320`) |
| **fast pair**: at `K/(d+d')` the pair reads `x, 1−x` and acts as one runner; two consecutive meetings in a core cell | a lower bound `c/max(C)` on the five-core's longest cell, then `d + d' ≥ (2/c)·max(C)` | see Finding 5 |
| **rung budget**: blocked units `< φ(N)` at a rung | per-rung count | PROVED (`lonely_eight_of_rung_budget`); holds at some rung for 12,257 of 12,309 on `[1,30]`; the rest need links (`ladder_budget_v1`) |
| **sign rule** (small deformations of the AP) | `k + e_k`, boundary runners move outward | exact on 20,000 cases (`ap_sign_rule_v1`); scope: near-AP only; the 193 sets the length step misses are **not** near-AP (`two_sides_profile_v1`) |

**Finding 5: the "robust order-six lemma" is false as stated, and the route it supports reaches
none of the hard sets even if it were true.** Session 1's next step 2 proposed that five
disparities always have a lonely cell at `1/8` of length `≥ 1/(4·max)`, tight at `(1..5)k`, on
the evidence of 20,000 random 5-sets of `[1,40]` (a 3% sample of `C(40,5)`).

- Exhaustive over the 139,246 primitive 5-subsets of `[1,30]`, exact in fractions: **20 fall
  below 1/4**. The minimum is **`5/32`**, at `(1,3,4,5,7)` and `(1,4,5,6,7)`; the progressions give
  exactly `1/4` `[VERIFIED — experiments/nN/five_cell_floor_v1.out, with an independent
  2,000,000-point grid check of the minimiser]`. `fast_pair_v1.out` line 6 already printed the
  value (`core cell x max(core): min 0.156`) on the 1,586-set cores. The summary took the
  random-sample minimum instead.
- A uniform lower bound **is** proved: order six clears five disparities at `1/6`, and the slack
  `1/6 − 1/8` on both sides gives a cell `≥ 1/(12·max)`, i.e. `c ≥ 1/12` `[PROVED — two lines]`.
  So the true constant lies in `[1/12, 5/32]` on this evidence.
- With a uniform constant `c`, the fast-pair rule needs `(d+d')/max(C) ≥ 2/c`. On the 28 hard
  sets the best pair (ratio ≤ 3) reaches only **2.19 to 7.63**. Needed: 8 at the false `c = 1/4`,
  12.8 at `c = 5/32`, 24 at the proved `c = 1/12`. **Certified: 0/28, 0/28, 0/28**
  `[VERIFIED — experiments/nN/fast_pair_constant_v1.out]`.
- So the 28/28 in `fast_pair_v1` came from **those particular cores having long cells**, not from
  any bound that holds for all cores. Both sessions reach the same wall from different sides:
  **no uniform lower-order bound reaches the hard sets; what they need is a set-specific one.**
  Session 2 phrased the missing lemma as an inverse statement (short isolation forces structure).
  This finding supports that phrasing and removes the uniform alternative.

### 4c. Density: what the null tests established

The residual sets are lonely on at least `0.039` of a period (median `0.109`) on `[1,40]`
(`family_null_v1.out`). Any family of about 50 or more instants spread across the period then
succeeds on most sets by density alone.

| family | family succeeds | same-size null | verdict |
|---|---|---|---|
| rule (`q ≤ 8`, flank = least multiple) | 2998/3000 | 2687 uniform `t`; 2837 random numerators, same denominators | **beats both nulls: structure** |
| top-pair mirror `k/(d₆+d₇)` | 2994/3000 | 2991 uniform | density |
| extra laps on the rule's flank, `r ≤ 1` | 25/28 | 27/28 random openings, same flanks | density |
| extra laps, `r ≤ 2` | 27/28 | 27/28 | density |

**Finding 6 (cross-session).** Session 2 reports "all 1,436 hard sets certified at lap `r ≤ 2`"
(`any_lap_v1`) and proposes the extra lap as the second side of the two-sided cover. Session 1's
`lap_null_v1` shows random openings of the same flanks do as well. The two results were produced
in separate containers and never compared. Read together, the lap extension is density, not a
mechanism. Separately, `PROOF_REQUIREMENTS_v2` §8 row 1 removes laps from the contract: `(D, a)`
is the whole output. **The lap-based next step should not be pursued as a mechanism.**

**Finding 7 (scope of the measure ban).** `PROOF_REQUIREMENTS_v2` §2 rules measure and density out
for two reasons. The first, that the AP's reading is isolated points, is **scoped to sets
containing a tight instance**. The AP is certified by R1 and is not in the residual, and the
residual on `[1,40]` has least lonely measure `0.039 > 0` `[VERIFIED on [1,40]]`. The second
reason is independent and stands whatever the scope: a measure bound names no instant (§4). This
is recorded so the first reason is not cited beyond its scope. It is **not** a proposal to reopen
measure. That is the owner's ruling to make.

## 5. What the evidence says about the shape of a proof

These are constraints the artifacts impose. They are not predictions.

1. **Not a fixed finite family of resolutions.** The `N` needed grows with the window
   (Finding 3). A rule set with bounded `N` has non-exhaustive side conditions.
2. **Not a uniform lower-order bound.** Dropping the fastest runner, or merging a pair, reduces
   to a quantitative lower-order statement. Every uniform version examined fails to reach the
   hard sets (Finding 5; six-only at 0.3). The structure has to come from the particular set.
3. **Not density.** Families of size ≥ 50 succeed by density (Finding 6). A family counts as
   evidence of mechanism only when it beats a same-size null. So far one does: the rung-selection
   rule's numerators (2,998 against 2,837).
4. **Where structure has been seen.** On the hard sets, the largest runners' consecutive laps
   organise the lonely cells: 52% of cells are bounded by the two largest disparities against 18%
   for ordinary sets (`player_census_v1`); the runner that closes one cell reopens the next one lap
   later (`consecutive_cells_v1`). This is the one hard-set observation that is neither density
   nor a restatement. `EMPIRICAL`, 28 sets.
5. **The one open rule in the framework's own terms is still `PROOF_REQUIREMENTS_v2` §7**: produce
   `(D, a)` when some difference is `≡ 0 (mod 8g)`. The `L_0` ladder was `VERIFIED` on 31,066
   runners with largest resolution 13. The residual fields `eight` and `no_common_factor` place
   every residual set inside that case. **The relation between the `L_0` ladder and the
   rational-opening fields has not been worked out.** Both are `(D, a)` rules at a chosen
   resolution. The ladder moves `D`; the fields fix `D = e` and move `a` within the `N` classes.
   This is the most direct link between the manuscript line and the Lean line, and nobody has
   drawn it.

## 6. Corrections to carry into the session records

| where | said | correct | artifact |
|---|---|---|---|
| order-8 summary, "What the experiments established", last row; next step 2 | five-set core's longest cell `≥ 1/(4·max)`, "tight at (1..5)k" | false: min `5/32` at `(1,3,4,5,7)`; proved floor `1/12` | `five_cell_floor_v1` |
| order-8 summary, next step 2 | with the lemma, R8 for a mirror pair "becomes a proved rule" | would be a proved rule, but at any uniform `c ≤ 1/4` it certifies 0 of the 28 hard sets | `fast_pair_constant_v1` |
| Prop 11 summary, next steps | "try the `q ≤ 8` rule with the extra lap as the second side" | extra laps match random openings (27/28 vs 27/28) | `lap_null_v1` |
| Prop 11 summary, open gap | the missing lemma "looks close to the core of the conjecture" | a difficulty verdict (CLAUDE.md §5); strike it. The fact: no uniform cell bound reaches the hard sets | Finding 5 |
| stack size | `--tstack=1000000` (`lakefile.toml` on two branches) vs `262144` (Prop 11 summary) | the local sync left `lakefile.toml` unchanged, pending owner approval (CLAUDE.md §10) | — |

## 7. Owed, and the owner's call

- **Owner:** is `EightResidual` (difference-set form) the obligation, or a sufficient route to
  the arrangement target (Finding 1)?
- **Owner:** does `no_first_lap` stay? Its nativeness was already in doubt at commit time
  (`OrderEightCasesN` header).
- Work out the relation between the §7 `L_0` ladder and the rational-opening fields (§5 item 5).
- The two `[1,40]` residual sets with `δ < 1/7` are still unnamed. The run lost its last lines.
- `ap_sign_rule_v1` has not been independently re-derived. It rests on 20,000 cases.
