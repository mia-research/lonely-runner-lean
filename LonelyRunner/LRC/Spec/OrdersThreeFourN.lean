import LonelyRunner.LRC.Spec.DoorsN
import LonelyRunner.LRC.Cascade.VersionB

/-!
# The conjecture at orders three and four, inside the framework

2026-09-24.  `ExistenceAtN n` asks that every set of at most `n − 1` positive real disparities be
lonely at threshold `1/n`, and `lonelyRunnerAtN_of_existence` turns it into `LonelyRunnerAtN n`,
the conjecture itself for every injective arrangement of real speeds.

At order three a subject has at most two disparities, and at order four at most three.  The
framework already settles both counts: the cascade from the bound reaches a lonely instant
(`FewDifferences.two_diffs_stop_within_one_move` at `n ≥ 3`, `exists_lonely_of_card_le_three` at
`n ≥ 4`), and `lonely_of_fixed` exhibits it.  Nothing outside the framework is used.

The termination lemmas are move counts used as tools inside those proofs; the statements proved
here carry no cap and no move count.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.style.longLine false

namespace LRC.SpecN

open MomentIterationN

/-- **Order three.**  Every set of at most two positive real disparities is lonely at `1/3`. -/
theorem existenceAtN_three : ExistenceAtN 3 := by
  intro ds hpos hcard
  classical
  rcases Finset.eq_empty_or_nonempty ds with rfl | hne
  · exact ⟨1, by norm_num, by intro d hd; simp at hd⟩
  · obtain ⟨a, ha, hmin⟩ := ds.exists_min_image id hne
    have ha0 := hpos a ha
    have hb : (0 : ℝ) < 1 / ((3 : ℕ) * a) := by positivity
    obtain ⟨hl, -⟩ := VersionB.two_diffs (n := 3) le_rfl hpos (by simpa using hcard) ha
      (fun d hd => hmin d hd)
    exact ⟨(move 3 ds)^[1] (1 / ((3 : ℕ) * a)),
      lt_of_lt_of_le hb (iterate_ge (n := 3) ds _ 1), hl⟩

/-- **Order four.**  Every set of at most three positive real disparities is lonely at `1/4`. -/
theorem existenceAtN_four : ExistenceAtN 4 := fun ds hpos hcard =>
  exists_lonely_of_card_le_three (n := 4) le_rfl hpos (by simpa using hcard)

/-- **The Lonely Runner Conjecture at three runners**, for every injective arrangement of real
speeds, proved inside the framework. -/
theorem lonelyRunnerAtN_three : LonelyRunnerAtN 3 :=
  lonelyRunnerAtN_of_existence existenceAtN_three

/-- **The Lonely Runner Conjecture at four runners**, for every injective arrangement of real
speeds, proved inside the framework. -/
theorem lonelyRunnerAtN_four : LonelyRunnerAtN 4 :=
  lonelyRunnerAtN_of_existence existenceAtN_four

end LRC.SpecN
