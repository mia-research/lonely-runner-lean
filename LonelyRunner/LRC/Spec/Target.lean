import LonelyRunner.LRC.Cascade.Flanks

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

open MomentIterationN Flanks

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

end LRC.Spec
