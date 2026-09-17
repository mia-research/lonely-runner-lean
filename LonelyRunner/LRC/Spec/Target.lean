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

end LRC.Spec
