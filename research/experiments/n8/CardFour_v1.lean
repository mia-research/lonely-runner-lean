import LonelyRunner.LRC.Spec.Target

/-!
# Four differences, over `ℝ`, unconditionally

`Target.lean` proves `exists_lonely_of_card_le_three`: a **real** difference set of at most three
positive differences admits a lonely time at order 8. It is unconditional, and it goes through the
**cascade** — `FewDifferences.three_diffs_stop_within_three_moves` — not through integers, not
through any density argument.

`FourDifferences.four_diffs_stop_ge_eight` has exactly the same shape for **four** differences at
every `n ≥ 8`: the seventh iterate is fixed. `Target.lean` already imports it. The consequence had
not been drawn.

This draws it: **at most four differences is settled over `ℝ`, unconditionally.**
-/

namespace CardFour

open LRC.Spec MomentIterationN

/-- **Four differences suffice.**  A real difference set with at most four positive differences
admits a lonely time at order 8 — the cascade reaches a fixed point by its seventh step. -/
theorem exists_lonely_of_card_le_four {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    (hcard : ds.card ≤ 4) : ∃ s, 0 < s ∧ Lonely 8 ds s := by
  classical
  rcases Finset.eq_empty_or_nonempty ds with rfl | hne
  · exact ⟨1, by norm_num, by intro d hd; simp at hd⟩
  · obtain ⟨a, ha, hmin⟩ := ds.exists_min_image id hne
    have ha0 := hpos a ha
    have hb : (0 : ℝ) < 1 / (8 * a) := by positivity
    have hfix := FourDifferences.four_diffs_stop_ge_eight (n := 8) (by norm_num)
      hpos hcard ha (fun d hd => hmin d hd)
    exact ⟨(move 8 ds)^[7] (1 / (8 * a)),
      lt_of_lt_of_le hb (iterate_ge (n := 8) ds _ 7), lonely_of_fixed hpos hfix⟩

end CardFour

#print axioms CardFour.exists_lonely_of_card_le_four
