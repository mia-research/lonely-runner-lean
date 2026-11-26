import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.OneMoverA
import Fresh.CascadeLanding
import Fresh.CascadeLandingG

/-!
# The cascade's landing with TWO movers: shared lemmas

Written 2026-10-22.  New file.  Frozen integer readings `S` and two movers `d1, d2 > 0`.  The first lonely instant of
`S ∪ {d1, d2}` is the first instant of a frozen piece at which BOTH movers are clear.  This file proves:
* `lonely_insert2_iff`: lonely for `insert d1 (insert d2 (fset S))` iff `FClear S` and both movers clear (`Clear2`);
* `first_two_clear`: if the two movers have a common clear instant at or after `l`, there is a FIRST one `T ≥ l`
  (the fixed point of the two-mover cascade started at `l`; it uses `Fresh.Cascade.exists_fixed_of_lonely`);
* `two_clear_in`: **[PROVISIONAL: counting tool]** an interval `[l, r]` with `r - l ≥ 7/(4 min d)` contains a common clear
  instant of the two movers (a full clear window of the slower mover, of length `3/(4 d)`, fits in the interval, and the
  faster mover has a clear point inside any interval of length `1/(4 d')`).
Grades: [L].
-/

open Classical

namespace Fresh.OneMover

open Fresh

/-- Both movers are clear at `s`. -/
-- STANDING: DEFINITION
def Clear2 (d1 d2 s : ℝ) : Prop := (1 / 8 : ℝ) ≤ distInt (d1 * s) ∧ (1 / 8 : ℝ) ≤ distInt (d2 * s)

theorem lonely_insert2_iff (S : Finset ℕ) (d1 d2 s : ℝ) :
    Fresh.Cascade.LonelyAt (insert d1 (insert d2 (fset S))) s ↔ FClear S s ∧ Clear2 d1 d2 s := by
  unfold Fresh.Cascade.LonelyAt FClear Clear2
  constructor
  · intro h
    refine ⟨fun i hi => h (i : ℝ) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (mem_fset.2 ⟨i, hi, rfl⟩))),
      h d1 (Finset.mem_insert_self _ _), h d2 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))⟩
  · rintro ⟨hF, h1, h2⟩ d hd
    rcases Finset.mem_insert.1 hd with rfl | hd
    · exact h1
    · rcases Finset.mem_insert.1 hd with rfl | hd
      · exact h2
      · obtain ⟨i, hi, rfl⟩ := mem_fset.1 hd
        exact hF i hi

theorem lonely_pair_iff (d1 d2 s : ℝ) : Fresh.Cascade.LonelyAt (insert d1 {d2}) s ↔ Clear2 d1 d2 s := by
  unfold Fresh.Cascade.LonelyAt Clear2
  constructor
  · intro h
    exact ⟨h d1 (Finset.mem_insert_self _ _), h d2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩
  · rintro ⟨h1, h2⟩ d hd
    rcases Finset.mem_insert.1 hd with rfl | hd
    · exact h1
    · rw [Finset.mem_singleton] at hd; subst hd; exact h2

theorem pos_insert2 {S : Finset ℕ} (hS : ∀ i ∈ S, 1 ≤ i) {d1 d2 : ℝ} (h1 : 0 < d1) (h2 : 0 < d2) :
    ∀ d ∈ insert d1 (insert d2 (fset S)), 0 < d := by
  intro d hd
  rcases Finset.mem_insert.1 hd with rfl | hd
  · exact h1
  · rcases Finset.mem_insert.1 hd with rfl | hd
    · exact h2
    · obtain ⟨i, hi, rfl⟩ := mem_fset.1 hd
      have := hS i hi
      exact_mod_cast this

theorem mem_insert2 {S : Finset ℕ} (d1 d2 : ℝ) {a : ℕ} (ha : a ∈ S) : (a : ℝ) ∈ insert d1 (insert d2 (fset S)) :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (mem_fset.2 ⟨a, ha, rfl⟩))

/-- The first common clear instant at or after `l`, if there is one. -/
theorem first_two_clear {d1 d2 l : ℝ} (h1 : 0 < d1) (h2 : 0 < d2) (hl : 0 < l)
    (hex : ∃ t, l ≤ t ∧ Clear2 d1 d2 t) :
    ∃ T, l ≤ T ∧ Clear2 d1 d2 T ∧ ∀ s, l ≤ s → Clear2 d1 d2 s → T ≤ s := by
  obtain ⟨t, hlt, ht⟩ := hex
  have hpos : ∀ d ∈ (insert d1 {d2} : Finset ℝ), 0 < d := by
    intro d hd
    rcases Finset.mem_insert.1 hd with rfl | hd
    · exact h1
    · rw [Finset.mem_singleton] at hd; subst hd; exact h2
  have hlon : Fresh.Cascade.LonelyAt (insert d1 {d2}) t := (lonely_pair_iff _ _ _).2 ht
  obtain ⟨N, hN⟩ := Fresh.Cascade.exists_fixed_of_lonely hpos hl hlon hlt
  set seq := Fresh.Cascade.cascadeSeq (insert d1 {d2}) l with hseq
  have hmv : ∀ n, IsMove (insert d1 {d2}) (seq n) (seq (n + 1)) := Fresh.Cascade.cascadeSeq_isMove _ _
  have hfix : IsMove (insert d1 {d2}) (seq N) (seq N) := by
    have := hmv N; rw [hN] at this; exact this
  have hlonely : Fresh.Cascade.LonelyAt (insert d1 {d2}) (seq N) := (Fresh.Cascade.isMove_self_iff hpos).mp hfix
  refine ⟨seq N, Fresh.Cascade.start_le_seq hpos hmv N, (lonely_pair_iff _ _ _).1 hlonely, ?_⟩
  intro s hs hc
  exact Fresh.Cascade.seq_le_of_lonely hpos ((lonely_pair_iff _ _ _).2 hc) hs hmv N

/-- In the way at `A` means the next opening is within a quarter of a zone width. -/
theorem opening_close {d A : ℝ} (hd : 0 < d) (h : ¬ (1 / 8 : ℝ) ≤ distInt (d * A)) :
    (((round (d * A) : ℤ) : ℝ) + 1 / 8) / d ≤ A + 1 / (4 * d) := by
  obtain ⟨w1, _⟩ := not_clear_window h
  rw [div_le_iff₀ hd]
  have : (A + 1 / (4 * d)) * d = A * d + 1 / 4 := by field_simp
  rw [this]; nlinarith

/-- **[PROVISIONAL: counting tool]** A common clear instant of two movers in any interval of length at least `7/(4 d1)`,
for `d1 ≤ d2`. -/
theorem two_clear_in {d1 d2 l r : ℝ} (h1 : 0 < d1) (h12 : d1 ≤ d2) (hw : l + 7 / (4 * d1) ≤ r) :
    ∃ t, l ≤ t ∧ t ≤ r ∧ Clear2 d1 d2 t := by
  have h2 : 0 < d2 := lt_of_lt_of_le h1 h12
  set N : ℤ := ⌈d1 * l - 1 / 8⌉ with hN
  have hN1 : d1 * l - 1 / 8 ≤ (N : ℝ) := Int.le_ceil _
  have hN2 : (N : ℝ) < d1 * l - 1 / 8 + 1 := Int.ceil_lt_add_one _
  set A : ℝ := ((N : ℝ) + 1 / 8) / d1 with hA
  have hAl : l ≤ A := by rw [hA, le_div_iff₀ h1]; linarith
  have hAu : A < l + 1 / d1 := by
    rw [hA, div_lt_iff₀ h1]
    have : (l + 1 / d1) * d1 = l * d1 + 1 := by field_simp
    rw [this]; nlinarith
  set B : ℝ := A + 3 / (4 * d1) with hB
  have hBr : B ≤ r := by
    have : 1 / d1 + 3 / (4 * d1) = 7 / (4 * d1) := by field_simp; ring
    linarith
  -- mover 1 is clear on [A, B]
  have hc1 : ∀ s, A ≤ s → s ≤ B → (1 / 8 : ℝ) ≤ distInt (d1 * s) := by
    intro s hs1 hs2
    apply Fresh.Localisation.clear_of_window N
    · have : d1 * A = (N : ℝ) + 1 / 8 := by rw [hA]; field_simp
      nlinarith
    · have : d1 * B = (N : ℝ) + 1 / 8 + 3 / 4 := by
        rw [hB, hA]; field_simp
      nlinarith
  -- mover 2 has a clear point in [A, B]
  have hAB : A ≤ B := by rw [hB]; have : 0 < 3 / (4 * d1) := by positivity
                         linarith
  have hhold : Holds d2 A B := by
    by_cases hc : (1 / 8 : ℝ) ≤ distInt (d2 * A)
    · exact Or.inl hc
    · right
      have := opening_close h2 hc
      have h3 : 1 / (4 * d2) ≤ 1 / (4 * d1) := by
        apply one_div_le_one_div_of_le (by positivity); nlinarith
      have h4 : 1 / (4 * d1) ≤ 3 / (4 * d1) := by
        apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
      rw [hB]; linarith
  obtain ⟨hcl, hl1, hl2, _⟩ := holds_clear h2 hAB hhold
  exact ⟨firstPt d2 A, by linarith, by linarith, hc1 _ hl1 hl2, hcl⟩

#print axioms lonely_insert2_iff
#print axioms first_two_clear
#print axioms two_clear_in

end Fresh.OneMover
