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
lonely instant at threshold `1/8`. -/
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

So a uniform cap on the cascade's instants is all that is missing. `CascadeCapped` states it; the theorem
below is the composition, and it is the whole of the reduction. -/

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
iterates stabilise, so they are bounded by the arrival value. -/
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

end LRC.Spec
