import LonelyRunner.LRC.Cascade.Arrangement
import LonelyRunner.LRC.Cascade.Flanks
import LonelyRunner.LRC.Cascade.SmallOrders
import LonelyRunner.LRC.Cascade.FourDifferences

/-!
# The frozen target

**This file is a specification, not part of the cascade artefact.**  It is deliberately outside
`LRC/Cascade/`, so the gate's check [4] — that nothing in the artefact names Existence until it is
proved — keeps its meaning.  Nothing here is claimed; these are `Prop`s, not theorems.

Its purpose is procedural.  The requirement for Existence at order 8 moved seven times in one session,
and each move happened at the moment the question "is this a proof?" was asked and answered by judgement.
Stating the target as a Lean `Prop` makes that question decidable instead: a proof is a term of this
type, with the gate clean.  A different statement is not a correction, it is an amendment, and needs a
recorded decision.

`ExistenceAt8` and `ExistenceAt8_cascade` are proved equivalent below, so neither can be substituted for
the other as a redefinition of the goal.
-/

namespace LRC.Spec

open MomentIterationN Flanks ChainBounds NearestState

instance : Fact (2 ≤ 8) := ⟨by norm_num⟩

/-- **The target, in differences.**  Every subject with at most seven positive speed differences has a
lonely instant at threshold `1/8`.

> **AMENDED 2026-09-18 — no longer the target.**  The target is `LonelyRunnerAt8`, the conjecture
> itself, recorded below.  `ExistenceAt8` is kept because it **suffices**
> (`lonelyRunnerAt8_of_existence`) and because everything proved against it still transfers.  It is
> not the target because it demands machinery the conjecture does not:
>
> * `Finset ℝ` forces decidable equality on `ℝ`;
> * it **collapses duplicates** — `|v i - v k|` can coincide for two runners — so the indexing, and
>   with it the arrangement, is destroyed before any proof starts;
> * `card ≤ 7` admits difference sets of `card ≤ 3` that **no arrangement produces**, which cost a
>   separate theorem (`exists_lonely_of_card_le_three`) the conjecture never asked for;
> * the gaps, the AP structure, the coupling across the eight subjects and "the subject and its two
>   neighbours" all live at the **arrangement** level and are not expressible in `ds` alone.
>
> Equivalence was not a reason to keep working in it: equivalent statements can demand different
> machinery, and this one offers strictly less structure to work with. -/
def ExistenceAt8 : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ 7 → ∃ s : ℝ, 0 < s ∧ Lonely 8 ds s

/-- **The target, in the cascade.**  §6.7's own wording: the determinator from the bound reaches a fixed
point. -/
def ExistenceAt8_cascade : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ 7 → ds.Nonempty →
    ∀ m ∈ ds, (∀ d ∈ ds, m ≤ d) →
      ∃ N : ℕ, move 8 ds ((move 8 ds)^[N] (1 / (8 * m))) = (move 8 ds)^[N] (1 / (8 * m))

/-- **The two statements of the target agree.**  From `lonely_iff_run_ends`; so the goal cannot be moved
by preferring one wording to the other. -/
theorem target_forms_agree : ExistenceAt8 ↔ ExistenceAt8_cascade := by
  constructor
  · intro h ds hpos hcard hne m hm hmin
    exact ((lonely_iff_run_ends (n := 8) hpos hm).1).mp (h ds hpos hcard)
  · intro h ds hpos hcard
    rcases Finset.eq_empty_or_nonempty ds with rfl | hne
    · exact ⟨1, by norm_num, by intro d hd; simp at hd⟩
    · obtain ⟨m, hm, hmin⟩ := ds.exists_min_image id hne
      exact ((lonely_iff_run_ends (n := 8) hpos hm).1).mpr
        (h ds hpos hcard hne m hm (fun d hd => hmin d hd))

/-- **The flank form.**  Also equivalent, by `lonely_iff_exists_flank`. -/
def ExistenceAt8_flank : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ 7 → ds.Nonempty →
    ∃ e ∈ ds, ∃ k : ℕ, Lonely 8 ds (flankOpening 8 e k)

theorem target_flank_agrees (h : ExistenceAt8_flank) : ExistenceAt8 := by
  intro ds hpos hcard
  rcases Finset.eq_empty_or_nonempty ds with rfl | hne
  · exact ⟨1, by norm_num, by intro d hd; simp at hd⟩
  · obtain ⟨e, he, k, hk⟩ := h ds hpos hcard hne
    exact ⟨flankOpening 8 e k, flankOpening_pos (hpos e he) k, hk⟩

/-! ## the single remaining link

The framework proves every step of the chain from the bound to the target except one. Collected here so
the remaining obligation is a statement, not a description.

* the relocation step        `MomentIterationN.move_eq_self_or_opening`, `nextOpening_at_scale`
* the growth of N relocations `SmallOrders.nearest_reading_recurrence` —
      `m * (move)^[N] b ≤ (1/n) * ∏_{j<N} (Q j + 1/n)/(Q j − 1/n)`
* capped instants give arrival `SmallOrders.exists_fixed_of_capped`
* arrival is the isolation     `MomentIterationN.first_isolation_as_zone_run` — Lonely, least, and a `Run`
* arrival ⟺ lonely somewhere   `MomentIterationN.lonely_iff_run_ends`

**Where the framework's exhibition requirement is discharged, since this file is where a reader
looks for the target.**  `FRAMEWORK_CONJECTURE_v1` §3 asks for *"the rules, written down, with their
conditions shown exhaustive"*, and says existence is not what is being asked.  That requirement is
**already met, by definitions rather than by any theorem here**:

    move n ds t       = ds.fold max t (fun d => if inWay n d t then nextOpening n d t else t)
    nextOpening n d t = ((⌈d·t − 1/n⌉ : ℝ) + 1/n) / d

Both are explicit expressions.  The rule is exhibited; nothing about it is chosen or asserted to
exist.  So there is **no second, stronger "naming" target** to aim at beyond the ones below, and
`CascadeCapped` is the whole residue — an existence statement *about a written-down rule*, which is
what §3 permits and not what it bans.

A caution for anyone tempted to state the naming form as a `Prop`: `∃ f : Finset ℝ → ℝ, …` is not
it.  That asserts a naming function exists, and classical choice proves it equivalent to
`ExistenceAt8` (checked).  Exhibition is a property of a **definition**, and proof irrelevance means
Lean cannot lift it into a statement at all.  `docs/n8/NAMING_VS_EXISTENCE_v1.md` has the argument.

So a uniform cap on the cascade's instants would suffice. `CascadeCapped` states it; the theorem below is
the composition.

> **AMENDED 2026-09-20 — `CascadeCapped` is no longer the obligation of record.**  It is retained,
> with both directions still proved, as **one sufficient route among several**.  See the amendment
> block below for what replaced it and why. -/

/-- **The cascade's instants are uniformly capped.** For every subject there is a bound above every
iterate from the bound. -/
def CascadeCapped : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ 7 → ∀ m ∈ ds, (∀ d ∈ ds, m ≤ d) →
    ∃ U : ℝ, ∀ N : ℕ, (move 8 ds)^[N] (1 / (8 * m)) ≤ U

/-- **The reduction, in one line.**  A uniform cap on the instants gives the target.  Nothing else is
owed: every other link is already proved in the artefact. -/
theorem existence_of_capped (h : CascadeCapped) : ExistenceAt8 := by
  rw [target_forms_agree]
  intro ds hpos hcard hne m hm hmin
  obtain ⟨U, hU⟩ := h ds hpos hcard m hm hmin
  have hb : (0 : ℝ) < 1 / (8 * m) := by
    have := hpos m hm; positivity
  exact exists_fixed_of_capped (n := 8) hpos hb hU

/-- **And the converse**, so this is the obligation restated, not weakened: once the cascade arrives, the
iterates stabilise, so they are bounded by the arrival value.  Since 2026-09-20 this pair is recorded
as **one sufficient route**, not as the obligation — see the amendment block below. -/
theorem capped_of_existence (h : ExistenceAt8) : CascadeCapped := by
  intro ds hpos hcard m hm hmin
  rw [target_forms_agree] at h
  obtain ⟨N, hfix⟩ := h ds hpos hcard ⟨m, hm⟩ m hm hmin
  refine ⟨(move 8 ds)^[N] (1 / (8 * m)), fun K => ?_⟩
  rcases le_or_gt K N with hKN | hKN
  · have e : (move 8 ds)^[N] (1 / (8 * m))
        = (move 8 ds)^[N - K] ((move 8 ds)^[K] (1 / (8 * m))) := by
      rw [← Function.iterate_add_apply]; congr 1; omega
    rw [e]; exact iterate_ge (n := 8) ds _ _
  · obtain ⟨i, rfl⟩ : ∃ i, K = N + i := ⟨K - N, by omega⟩
    exact le_of_eq (FourDifferences.iterate_stable (n := 8) hfix i)

/-! ## AMENDED 2026-09-20 — the obligation of record has no iteration in it

**Decision (author, 2026-09-20).**  The obligation of record is the **iteration-free** form:

    LRC.Spec.DoorFlank          (Spec/Doors.lean, arrangement level, proved ↔ by `doorFlank_iff`)
    ExistenceAt8_flank          (this file, difference-set level, ↔ by `target_flank_iff` below)
    ScaleCandidates.lonely_iff_exists_candidate_scale   (Theorem 6.15, the same statement in scales)

Read in scales: *some candidate scale `e/(8k+1)` is clear for every disparity*.  A disparity `e` and
an index `k`, both read off the arrangement.  **No quantifier over time, no iteration, no cap, and no
bound on how many of anything.**

`CascadeCapped`, `ExistenceAt8_cascade`, `FiniteActiveMembership`, `DoorArrives`, `DoorCapped` and
`DoorFAM` are **retained with every proof intact**, and are now recorded as *sufficient routes*
rather than as the obligation.

**Why the amendment.**  The conjecture asks for loneliness at **some** time.  It therefore carries no
obligation about *when* an instant falls or *how many* steps reach it — `MANUSCRIPT_v17.md` §6A row
two bans exactly such a bound, and §6.10 states outright that finding the first instant is not the
obligation.  The iteration wordings nevertheless import one: to discharge `CascadeCapped` is to
supply a cap, and a cap is a bound on how far a run goes.  That is an obligation the conjecture never
had, and stating the target that way is what put every attempt on a route that needs one.

**What it costs, stated plainly: nothing is easier.**  All of these are `↔`, so the amended target is
exactly as hard as the one it replaces.  No bound is supplied here and none is claimed.

**What it changes.**  Under the iteration form the obligation is one indivisible claim with no
partial credit, and every route to it needs a measure on the run — which `docs/n8/
PROGRESS_ACCOUNTING_LIMIT_v1.md` shows is pinned at `7/4` by the round-robin the run actually
performs.  Under the amended form the obligation is *exhibit `(e, k)`*, which is `MANUSCRIPT_v17.md`
§6.7's rules-with-conditions form; `Construction8.ratio_condition` (Theorem 4.8) is already such a
rule, with `k = 0`.  Each rule covers a class, the reach is a number, and no cap appears anywhere.
**A bound on `k` is not required for a proof** — §6.10's measured ceiling `k ≤ 6` is explicitly
recorded there as measured and not proved, and the amended obligation does not rest on it.

**Evidence that the iteration form was costing rather than buying** (`MANUSCRIPT_v17.md` §6.10,
`[VERIFIED — exact]`): on `(27, 70, 107, 137, 159, 188, 344, 393)` the cascade takes 28 moves to the
earliest instant while the smallest clear opening index at any flank is 6; on
`(1, 31, 75, 97, 128, 160, 176, 225)` it is 23 against 4; across 20,000 subjects in `S ∈ [7,8]`, mean
2.16 moves against mean `k` of 1.04.  Proposition 6.1 guarantees the instants agree, so the `(e, k)`
form reaches the identical instant without the sort.

**Superseded designations.**  `ExistenceAt8` ceased to be the target on 2026-09-18 (block above);
`CascadeCapped` ceased to be the obligation of record on 2026-09-20 (this block).  Neither statement
is withdrawn and no proof is affected.  See `docs/n8/CAP_DEFECT_v1.md`,
`docs/n8/PROGRESS_ACCOUNTING_LIMIT_v1.md` and `docs/n8/JOINT_REFRAME_v1.md`. -/

/-! ## the discharge criterion, fixed in advance (2026-09-20)

**This block fixes what counts as discharging the obligation, before the work, so the question is
decidable rather than judged.**  It is recorded at the author's instruction, against the failure this
file was created for: the requirement for Existence moved seven times in one session, each time at the
moment "is this a proof?" was asked and answered by judgement.

**The obligation is discharged by exactly two declarations, and nothing else may be asked for.**

    -- (1) the witness map, written down
    def witness : (v : Fin 8 → ℝ) → (k : Fin 8) → ℝ × ℕ := …

    -- (2) the theorem that it works
    theorem witness_lonely (v : Fin 8 → ℝ) (hv : Function.Injective v) (k : Fin 8) :
        LonelyAt v k (Flanks.flankOpening 8 (witness v k).1 (witness v k).2) := …

From those, `DoorFlank` follows for every arrangement and subject, and
`LRC.Spec.lonelyRunnerAt8_of_doorFlank` — **already proved** — yields a term of type
`LonelyRunnerAt8`.  A witness map may equally be given per-subject on the difference set, or as a
finite case split with each case's `(e, k)` named; the shape is free, the two obligations are not.

**The mechanical check, and the whole of it.**  A term of type `LRC.Spec.LonelyRunnerAt8` whose
`#print axioms` reports at most `[propext, Classical.choice, Quot.sound]`, in a tree with no `sorry`,
no `native_decide`, no `unsafe` and no `admit`, **is a proof of the lonely runner conjecture at eight
runners.**  Nothing further is owed: not a cap, not a bound on `k`, not a count, not a coverage
percentage, not a termination argument, not a treatment of the real case as a separate obligation
(every statement on the path is over `ℝ` already — `docs/n8/DOOR3_v1.md` §4), and not an account of
why the formula works beyond the proof that it does.

**Three things that are not that, named now so that saying so later is not a moved goalpost.**  Each
is a defect in (1) or (2) as already written above, not an additional standard:

* **A map verified on samples is not (2).**  However many arrangements it clears, that is a test.
  (2) is a theorem quantified over every injective `v` and every `k`.
* **A map with unhandled cases is not (1).**  A partial map, or a case split whose cases are not shown
  exhaustive, leaves (2) unstatable.
* **A map defined as "the least `(e, k)` that works" is not (1).**  It is `Classical.choice` applied
  to the conclusion; `∃ f : Finset ℝ → ℝ, …` is provable **from** `ExistenceAt8` (checked — see the
  caution above and `docs/n8/NAMING_VS_EXISTENCE_v1.md`), so it establishes nothing.

Anything else raised against a candidate must be a concrete failure of (1) or (2), named at a
specific declaration or a specific arrangement.  "Not yet a proof" with no such site is not a finding. -/

/-- **The flank form is the target**, both directions.  `target_flank_agrees` above gives one way;
this is the equivalence, and it is the difference-set statement of the amended obligation. -/
theorem target_flank_iff : ExistenceAt8 ↔ ExistenceAt8_flank := by
  constructor
  · intro h ds hpos hcard hne
    exact (Flanks.lonely_iff_exists_flank (n := 8) hpos hne).mp (h ds hpos hcard)
  · exact target_flank_agrees

/-! ## a fifth wording: Finite Active Membership

Proposed as an *internal bridge* to Existence: along the cascade from the bound, each difference is
in the way at only finitely many steps.  The argument offered for it is sound — seven finite sets
have a finite union, and a non-terminating cascade has some runner in the way at every step, so `ℕ`
would embed in that union.  `cascade_of_FAM` below is that argument, formalised.

`FAM_of_existence` is the converse, and it is the point: **FAM is equivalent to the target, not
weaker than it.**  So "prove FAM" is a restatement of the obligation, not a reduction of it.  The
mechanism underneath is `Iteration.nextOpening_le_move` — one move clears every runner in the way,
so a runner's lap strictly increases between successive activities, and its active set is finite
exactly when its lap is bounded, which is exactly `CascadeCapped`. -/

/-- **Finite Active Membership.**  Each difference is in the way at only finitely many cascade steps. -/
def FiniteActiveMembership : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ 7 → ∀ m ∈ ds, (∀ d ∈ ds, m ≤ d) →
    ∀ d ∈ ds, {j : ℕ | inWay 8 d ((move 8 ds)^[j] (1 / (8 * m)))}.Finite

/-- **FAM gives the target.**  Seven finite active sets have a finite union; a cascade that never
reaches a fixed point has someone in the way at every step, so `ℕ` would sit inside that union. -/
theorem cascade_of_FAM (h : FiniteActiveMembership) : ExistenceAt8_cascade := by
  intro ds hpos hcard hne m hm hmin
  by_contra hno
  push Not at hno
  have hact : ∀ j : ℕ, ∃ d ∈ ds, inWay 8 d ((move 8 ds)^[j] (1 / (8 * m))) := by
    intro j
    rcases move_eq_self_or_opening (n := 8) ds ((move 8 ds)^[j] (1 / (8 * m))) with hfix | ⟨x, hx, hw, -⟩
    · exact absurd hfix (hno j)
    · exact ⟨x, hx, hw⟩
  have hfin : (⋃ d ∈ ds, {j : ℕ | inWay 8 d ((move 8 ds)^[j] (1 / (8 * m)))}).Finite :=
    Set.Finite.biUnion ds.finite_toSet (fun d hd => h ds hpos hcard m hm hmin d hd)
  have huniv : (Set.univ : Set ℕ) ⊆ ⋃ d ∈ ds, {j : ℕ | inWay 8 d ((move 8 ds)^[j] (1 / (8 * m)))} := by
    intro j _
    obtain ⟨d, hd, hw⟩ := hact j
    exact Set.mem_biUnion hd hw
  exact Set.infinite_univ (hfin.subset huniv)

/-- **And the target gives FAM**, so the two are equivalent and FAM is not a weaker obligation. -/
theorem FAM_of_existence (h : ExistenceAt8) : FiniteActiveMembership := by
  intro ds hpos hcard m hm hmin d hd
  rw [target_forms_agree] at h
  obtain ⟨N, hfix⟩ := h ds hpos hcard ⟨m, hm⟩ m hm hmin
  refine Set.Finite.subset (Set.finite_Iio N) ?_
  intro j hj
  by_contra hjN
  simp only [Set.mem_Iio, not_lt] at hjN
  obtain ⟨i, rfl⟩ : ∃ i, j = N + i := ⟨j - N, by omega⟩
  rw [Set.mem_setOf_eq, FourDifferences.iterate_stable (n := 8) hfix i] at hj
  exact absurd (lonely_of_fixed hpos hfix d hd) (not_le.mpr hj)

/-- **So FAM is exactly the target.**  Machine-checked, so the claim that it is a weaker or
"internal" obligation cannot rest on prose.  Composing `cascade_of_FAM` with `target_forms_agree`
one way and `FAM_of_existence` the other. -/
theorem FAM_iff_existence : FiniteActiveMembership ↔ ExistenceAt8 :=
  ⟨fun h => target_forms_agree.mpr (cascade_of_FAM h), FAM_of_existence⟩

/-! ## a candidate route: Three-Largest-Flanks

Not a wording of the target but a **conjecture that would imply it** over whole numbers.  Stated here
so progress on it is checkable rather than described: `ThreeLargestFlanks` is a `Prop`, and
`exists_lonely_of_threeLargest` is the reduction.

Evidence at the time of writing, in `docs/n8/RULE_TABLE_v1.md` §6: zero failures across the
exhaustive ranges `[1,17]`, `[1,20]`, `[1,22]`, `[1,24]` — over 500,000 primitive 7-sets — and a
single set with only one working flank, `(2,3,4,5,6,7,16)`, whose flank is the largest.  No set
found at any range has all its working flanks outside the three largest.

It is a **conjecture**: no proof is claimed, and unlike the target itself it may simply be false. -/

/-- **Three-Largest-Flanks.**  For whole-number differences, one of the three largest serves as a
flank with a lonely opening.  "`e` is among the three largest" is written as: at most two members of
`ds` exceed it. -/
def ThreeLargestFlanks : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ 7 → ds.Nonempty →
    (∀ d ∈ ds, ∃ a : ℤ, d = (a : ℝ)) →
      ∃ e ∈ ds, (ds.filter (fun d => e < d)).card ≤ 2 ∧
        ∃ k : ℕ, Lonely 8 ds (flankOpening 8 e k)

/-- **The reduction.**  `ThreeLargestFlanks` gives Existence for every whole-number difference set. -/
theorem exists_lonely_of_threeLargest (h : ThreeLargestFlanks) {ds : Finset ℝ}
    (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 7)
    (hint : ∀ d ∈ ds, ∃ a : ℤ, d = (a : ℝ)) :
    ∃ s, 0 < s ∧ Lonely 8 ds s := by
  rcases Finset.eq_empty_or_nonempty ds with rfl | hne
  · exact ⟨1, by norm_num, by intro d hd; simp at hd⟩
  · obtain ⟨e, he, -, k, hk⟩ := h ds hpos hcard hne hint
    exact ⟨flankOpening 8 e k, flankOpening_pos (hpos e he) k, hk⟩

/-! ## the framework's own form of the target

`ExistenceAt8` quantifies over a **time** `s : ℝ`.  The construction does not: its statement runs over
a runner and a lap index, both discrete, and its condition is a congruence.  No time appears, no frame
is changed, and nothing is placed at `0` — `0` is the circle's start and close, and `d · s` is a
**separation** between two moving runners, never a position.

`ExistenceAt8_congruence` below is that form.  It is stated **alongside** `ExistenceAt8`, not in place
of it: this file's rule is that a different statement is an amendment needing a recorded decision.
What the two are worth relative to each other is pinned by the two theorems that follow.

**They are equivalent on whole-number differences and not otherwise.**  `lonely_iff_emod_search`
carries `hint`, so the congruence form says nothing about real difference sets, while `ExistenceAt8`
covers them.  Adopting the congruence form as the target would therefore **drop the real case** —
which `DOOR3_v1` measures as mathematically comfortable (margins 1.6× to 3.7× once any ratio is
irrational) but expensive to formalise, since it needs a dense-orbit theorem on the `k`-torus that
mathlib does not carry.  It would **not** touch the difficulty: that sits entirely in the
commensurable case, which both forms contain in full. -/

/-- **The target in the framework's own objects.**  No time: a runner `b`, a lap `k`, and a congruence. -/
def ExistenceAt8_congruence : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ 7 → ds.Nonempty →
    (∀ d ∈ ds, ∃ a : ℤ, d = (a : ℝ)) →
      ∃ b : ℤ, 0 < b ∧ (b : ℝ) ∈ ds ∧ ∃ k : ℕ, (k : ℤ) < b ∧
        ∀ a : ℤ, (a : ℝ) ∈ ds →
          b ≤ a * ((8 : ℤ) * (k : ℤ) + 1) % ((8 : ℤ) * b)
          ∧ a * ((8 : ℤ) * (k : ℤ) + 1) % ((8 : ℤ) * b) ≤ (8 : ℤ) * b - b

/-- **The classical form gives the framework's form**, on whole-number differences. -/
theorem congruence_of_existence (h : ExistenceAt8) : ExistenceAt8_congruence := by
  intro ds hpos hcard hne hint
  exact (Flanks.lonely_iff_emod_search (n := 8) hpos hne hint).mp (h ds hpos hcard)

/-- **And the framework's form gives Existence**, on whole-number differences.  This is the exact
content of adopting it as the target: everything except the real case. -/
theorem exists_lonely_of_congruence (h : ExistenceAt8_congruence) {ds : Finset ℝ}
    (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 7) (hne : ds.Nonempty)
    (hint : ∀ d ∈ ds, ∃ a : ℤ, d = (a : ℝ)) :
    ∃ s, 0 < s ∧ Lonely 8 ds s :=
  (Flanks.lonely_iff_emod_search (n := 8) hpos hne hint).mpr (h ds hpos hcard hne hint)

/-! ## the conjecture itself

Everything above is stated in **difference sets**.  That is already a transform of the conjecture, and
it generalises: `ExistenceAt8` quantifies over arbitrary `ds` with `card ≤ 7`, whereas the conjecture
speaks of **eight runners with distinct speeds**, whose eight difference sets are not arbitrary — they
are coupled, sharing the 28 pairwise differences, each appearing in exactly two of them.

`LonelyRunnerAt8` below is the conjecture, stated with no transform at all: eight distinct speeds, a
chosen runner, and a time at which every other runner is at circle-distance at least `1/8` from it.
Nothing is placed at `0`, nothing is held stationary, and `v i * t - v k * t` is a separation between
two moving runners.

`lonelyRunnerAt8_of_existence` shows `ExistenceAt8` suffices for it.  The converse is **not** claimed:
the difference-set form is strictly more general, and how much of that generality the conjecture
actually needs is exactly the question of whether we have been proving more than was asked. -/

/-- **THE TARGET, as of 2026-09-18.**  The Lonely Runner Conjecture at eight runners, untransformed:
eight runners with distinct speeds; for each of them there is a positive time at which every other
runner is at circle-distance at least `1/8`.

Amended to this from `ExistenceAt8` by the author's decision; the reasons are recorded on
`ExistenceAt8` above.  The indexing is retained, so the arrangement — gaps, AP structure, the coupling
across the eight subjects — remains available to a proof.  A proof is a term of **this** type. -/
def LonelyRunnerAt8 : Prop :=
  ∀ v : Fin 8 → ℝ, Function.Injective v → ∀ k : Fin 8,
    ∃ t : ℝ, 0 < t ∧ ∀ i : Fin 8, i ≠ k → (8 : ℝ)⁻¹ ≤ circDist (v i * t - v k * t)

/-- **The difference-set form suffices for the conjecture.**  For a chosen runner `k`, the separations
`v i * t - v k * t` are `(v i - v k) * t`, and `circDist` is even, so the set of `|v i - v k|` for
`i ≠ k` is a `Finset` of at most seven positive reals. -/
theorem lonelyRunnerAt8_of_existence (h : ExistenceAt8) : LonelyRunnerAt8 := by
  intro v hinj k
  classical
  set ds : Finset ℝ := (Finset.univ.erase k).image (fun i => |v i - v k|) with hds
  have hpos : ∀ d ∈ ds, 0 < d := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
    have : v i ≠ v k := fun hc => (Finset.mem_erase.mp hi).1 (hinj hc)
    exact abs_pos.mpr (sub_ne_zero.mpr this)
  have hcard : ds.card ≤ 7 := by
    refine le_trans (Finset.card_image_le) ?_
    simp [Finset.card_erase_of_mem]
  obtain ⟨s, hs, hl⟩ := h ds hpos hcard
  refine ⟨s, hs, fun i hik => ?_⟩
  have hmem : |v i - v k| ∈ ds :=
    Finset.mem_image.mpr ⟨i, Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩, rfl⟩
  have := hl _ hmem
  rw [show v i * s - v k * s = (v i - v k) * s by ring]
  rcases abs_cases (v i - v k) with ⟨he, -⟩ | ⟨he, -⟩
  · rwa [he] at this
  · rw [he] at this
    rwa [show (v i - v k) * s = -(-(v i - v k) * s) by ring, Flanks.circDist_neg]

/-! ## how much wider is the difference-set form than the conjecture?

Exactly the sets no arrangement can produce, and they are already proved.

For a chosen runner `k`, a value `d` occurs as `|v i - v k|` for **at most two** runners, `v k ± d`.
So a difference set of card `m` needs multiplicities summing to 7 with each at most 2, i.e. `2m ≥ 7`,
i.e. **`m ≥ 4`**.  Conversely every `ds` with `4 ≤ card ≤ 7` does arise: take the subject at `0`,
a runner at `+d` for each `d ∈ ds`, and one at `−d` for `7 − card` of them — eight distinct speeds
whose difference set from the subject is exactly `ds` (checked on 20,000 sets, no failure).

So `ExistenceAt8` exceeds the conjecture **only on `card ≤ 3`** — and that case is a theorem. -/

/-- **Existence holds outright for at most three differences.**  `FewDifferences` stops the cascade
within three moves for `card ≤ 3` at every `n ≥ 4`, and a fixed point is a lonely time.

This is the whole of what `ExistenceAt8` asks beyond the conjecture, so the difference-set form is
**not** a weaker thing we have been chasing by mistake: it is the conjecture plus a case already
settled. -/
theorem exists_lonely_of_card_le_three {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    (hcard : ds.card ≤ 3) : ∃ s, 0 < s ∧ Lonely 8 ds s := by
  classical
  rcases Finset.eq_empty_or_nonempty ds with rfl | hne
  · exact ⟨1, by norm_num, by intro d hd; simp at hd⟩
  · obtain ⟨a, ha, hmin⟩ := ds.exists_min_image id hne
    have ha0 := hpos a ha
    have hb : (0 : ℝ) < 1 / (8 * a) := by positivity
    have hfix := FewDifferences.three_diffs_stop_within_three_moves (n := 8) (by norm_num)
      hpos hcard ha (fun d hd => hmin d hd)
    exact ⟨(move 8 ds)^[3] (1 / (8 * a)),
      lt_of_lt_of_le hb (iterate_ge (n := 8) ds _ 3), lonely_of_fixed hpos hfix⟩

/-- **The target in the arrangement's own objects.**  `LonelyRunnerAt8` is exactly "for every
arrangement and every subject there is a positive time at which the subject is lonely", with
`Arrangement.LonelyAt` the framework's predicate — separations between moving runners, no `ds`, no
duplicate collapse, and the indexing intact. -/
theorem lonelyRunnerAt8_iff_arrangement :
    LonelyRunnerAt8 ↔
      ∀ v : Fin 8 → ℝ, Function.Injective v → ∀ k : Fin 8,
        ∃ t : ℝ, 0 < t ∧ Arrangement.LonelyAt v k t := Iff.rfl

/-! ### Existence, stated where the mechanisms live

`ExistenceAt8` quantified over a `Finset ℝ` of size at most seven.  That form is *sufficient* for the
target but not identical to it: it forces decidable equality, collapses duplicate differences, admits
sets no arrangement produces, and — decisively — discards the arrangement, which is where the gaps,
the AP structure and "the subject and its two neighbours" live.

The obligation below is the same statement on the arrangement, and it is `Iff.rfl` to the target: not
a sufficient condition, the conjecture itself.  Its machinery is `LRC/Cascade/Arrangement.lean`. -/

/-- **Existence on arrangements.**  Every injective speed assignment, every subject, a lonely
instant.  Nothing is pinned at `0` and no scale is chosen: see `Arrangement.lonelyAt_add_const` and
`Arrangement.lonelyAt_const_mul`. -/
def ExistenceOnArrangements : Prop :=
  ∀ v : Fin 8 → ℝ, Function.Injective v → ∀ k : Fin 8,
    ∃ t : ℝ, 0 < t ∧ Arrangement.LonelyAt v k t

/-- **The obligation is the target.**  Definitional, not a reduction. -/
theorem lonelyRunnerAt8_iff_existenceOnArrangements :
    LonelyRunnerAt8 ↔ ExistenceOnArrangements := Iff.rfl

/-- **The target from per-subject witnesses**, with no difference set anywhere in the path. -/
theorem lonelyRunnerAt8_of_arrangement
    (H : ∀ v : Fin 8 → ℝ, Function.Injective v → ∀ k : Fin 8,
      ∃ t : ℝ, 0 < t ∧ Arrangement.LonelyAt v k t) :
    LonelyRunnerAt8 := H


end LRC.Spec
