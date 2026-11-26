import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.OneMoverA
import Fresh.CascadeLanding
import Fresh.CascadeLandingG
import Fresh.CascadeLanding2
import Fresh.ManyClear

/-!
# Three movers against a frozen set: the common-clear predicate and the first common clear instant

Written 2026-10-22.  New file.  As `CascadeLanding2.lean`, for three movers.  Grades: [L].
-/

open Classical

namespace Fresh.OneMover

open Fresh

/-- The three movers are clear at `s`. -/
-- STANDING: DEFINITION
def Clear3 (d1 d2 d3 s : ℝ) : Prop :=
  (1 / 8 : ℝ) ≤ distInt (d1 * s) ∧ (1 / 8 : ℝ) ≤ distInt (d2 * s) ∧ (1 / 8 : ℝ) ≤ distInt (d3 * s)

theorem lonely_insert3_iff (S : Finset ℕ) (d1 d2 d3 s : ℝ) :
    Fresh.Cascade.LonelyAt (insert d1 (insert d2 (insert d3 (fset S)))) s ↔ FClear S s ∧ Clear3 d1 d2 d3 s := by
  unfold Fresh.Cascade.LonelyAt FClear Clear3
  constructor
  · intro h
    refine ⟨fun i hi => h (i : ℝ) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (mem_fset.2 ⟨i, hi, rfl⟩)))),
      h d1 (Finset.mem_insert_self _ _), h d2 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)),
      h d3 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))⟩
  · rintro ⟨hF, h1, h2, h3⟩ d hd
    rcases Finset.mem_insert.1 hd with rfl | hd
    · exact h1
    · rcases Finset.mem_insert.1 hd with rfl | hd
      · exact h2
      · rcases Finset.mem_insert.1 hd with rfl | hd
        · exact h3
        · obtain ⟨i, hi, rfl⟩ := mem_fset.1 hd
          exact hF i hi

theorem lonely_triple_iff (d1 d2 d3 s : ℝ) : Fresh.Cascade.LonelyAt (insert d1 (insert d2 {d3})) s ↔ Clear3 d1 d2 d3 s := by
  unfold Fresh.Cascade.LonelyAt Clear3
  constructor
  · intro h
    exact ⟨h d1 (Finset.mem_insert_self _ _), h d2 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)),
      h d3 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))⟩
  · rintro ⟨h1, h2, h3⟩ d hd
    rcases Finset.mem_insert.1 hd with rfl | hd
    · exact h1
    · rcases Finset.mem_insert.1 hd with rfl | hd
      · exact h2
      · rw [Finset.mem_singleton] at hd; subst hd; exact h3

theorem pos_insert3 {S : Finset ℕ} (hS : ∀ i ∈ S, 1 ≤ i) {d1 d2 d3 : ℝ} (h1 : 0 < d1) (h2 : 0 < d2) (h3 : 0 < d3) :
    ∀ d ∈ insert d1 (insert d2 (insert d3 (fset S))), 0 < d := by
  intro d hd
  rcases Finset.mem_insert.1 hd with rfl | hd
  · exact h1
  · rcases Finset.mem_insert.1 hd with rfl | hd
    · exact h2
    · rcases Finset.mem_insert.1 hd with rfl | hd
      · exact h3
      · obtain ⟨i, hi, rfl⟩ := mem_fset.1 hd
        have := hS i hi
        exact_mod_cast this

theorem mem_insert3 {S : Finset ℕ} (d1 d2 d3 : ℝ) {a : ℕ} (ha : a ∈ S) : (a : ℝ) ∈ insert d1 (insert d2 (insert d3 (fset S))) :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (mem_fset.2 ⟨a, ha, rfl⟩)))

/-- The first common clear instant at or after `l`, if there is one. -/
theorem first_three_clear {d1 d2 d3 l : ℝ} (h1 : 0 < d1) (h2 : 0 < d2) (h3 : 0 < d3) (hl : 0 < l)
    (hex : ∃ t, l ≤ t ∧ Clear3 d1 d2 d3 t) :
    ∃ T, l ≤ T ∧ Clear3 d1 d2 d3 T ∧ ∀ s, l ≤ s → Clear3 d1 d2 d3 s → T ≤ s := by
  obtain ⟨t, hlt, ht⟩ := hex
  have hpos : ∀ d ∈ (insert d1 (insert d2 {d3}) : Finset ℝ), 0 < d := by
    intro d hd
    rcases Finset.mem_insert.1 hd with rfl | hd
    · exact h1
    · rcases Finset.mem_insert.1 hd with rfl | hd
      · exact h2
      · rw [Finset.mem_singleton] at hd; subst hd; exact h3
  have hlon : Fresh.Cascade.LonelyAt (insert d1 (insert d2 {d3})) t := (lonely_triple_iff _ _ _ _).2 ht
  obtain ⟨N, hN⟩ := Fresh.Cascade.exists_fixed_of_lonely hpos hl hlon hlt
  set seq := Fresh.Cascade.cascadeSeq (insert d1 (insert d2 {d3})) l with hseq
  have hmv : ∀ n, IsMove (insert d1 (insert d2 {d3})) (seq n) (seq (n + 1)) := Fresh.Cascade.cascadeSeq_isMove _ _
  have hfix : IsMove (insert d1 (insert d2 {d3})) (seq N) (seq N) := by
    have := hmv N; rw [hN] at this; exact this
  have hlonely : Fresh.Cascade.LonelyAt (insert d1 (insert d2 {d3})) (seq N) := (Fresh.Cascade.isMove_self_iff hpos).mp hfix
  refine ⟨seq N, Fresh.Cascade.start_le_seq hpos hmv N, (lonely_triple_iff _ _ _ _).1 hlonely, ?_⟩
  intro s hs hc
  exact Fresh.Cascade.seq_le_of_lonely hpos ((lonely_triple_iff _ _ _ _).2 hc) hs hmv N

#print axioms first_three_clear
#print axioms lonely_insert3_iff

end Fresh.OneMover
