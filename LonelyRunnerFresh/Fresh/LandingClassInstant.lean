import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.CascadeLanding
import Fresh.CascadeLandingG
import Fresh.ClassInstantView

/-!
# The cascade lands on a class-1 instant of its setter (E754)

Written 2026-11-01.  New file; nothing existing is edited.  For ANY finite set of positive readings (no AP, no grid):

* `cascade_term_class_instant`: every term of the cascade from the bound `1/(8a)` is a class-1 instant
  `(8M+1)/(8d)` of some reading `d` with `M ≥ 0`.  The start is `d = a`, `M = 0`; every move lands on the next opening
  `(k + 1/8)/d` of a runner in the way (`isMove_mem_openings`), which is `(8k+1)/(8d)`.
* `first_is_class_instant`: so the landing (the first lonely instant, `cascade_landsG`) is a class-1 instant of a
  reading: the setter's.
* `isFirst_iff_least_goodM`: the landing is exactly the least class-1 instant `(8M+1)/(8d)`, over the readings `d`
  and `M ≥ 0`, at which every reading is good in the view through `d` (`GoodM`, E748).

No covering or counting step is added here; the finiteness step inside `exists_fixed_of_lonely` keeps its own
[PROVISIONAL: counting tool] tag in `Cascade.lean`.

Grades: [L].
-/

namespace Fresh.OneMover

open Fresh

/-- **Every cascade term is a class-1 instant of a reading.** -/
theorem cascade_term_class_instant {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {a : ℝ} (ha : a ∈ ds) {s : ℝ}
    (hl : Fresh.Cascade.LonelyAt ds s) (hs : 1 / (8 * a) ≤ s) (seq : ℕ → ℝ) (h0 : seq 0 = 1 / (8 * a))
    (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1))) :
    ∀ n, ∃ d ∈ ds, ∃ M : ℤ, 0 ≤ M ∧ seq n = (8 * (M : ℝ) + 1) / (8 * d) := by
  have hapos := hpos a ha
  have hle : ∀ n, seq n ≤ s := Fresh.Cascade.seq_le_of_lonely hpos hl (by rw [h0]; exact hs) hmv
  have hge : ∀ n, seq 0 ≤ seq n := Fresh.Cascade.start_le_seq hpos hmv
  have h0pos : 0 < seq 0 := by rw [h0]; positivity
  intro n
  induction n with
  | zero => exact ⟨a, ha, 0, le_rfl, by rw [h0]; push_cast; ring⟩
  | succ n ih =>
    rcases Fresh.Cascade.isMove_mem_openings hpos (lt_of_lt_of_le h0pos (hge n)) hl (hle n) (hmv n) with h | h
    · rw [h]; exact ih
    · unfold Fresh.Cascade.openingsUpTo at h
      obtain ⟨d, hd, hk⟩ := Finset.mem_biUnion.mp h
      obtain ⟨k, hk', hkv⟩ := Finset.mem_image.mp hk
      refine ⟨d, hd, k, (Finset.mem_Icc.mp hk').1, ?_⟩
      rw [← hkv]
      have := hpos d hd
      field_simp

/-- **The landing is a class-1 instant of its setter.**  For any finite set of positive readings with least reading
`a` attained, the first lonely instant is `(8M+1)/(8d)` for some reading `d` and `M ≥ 0`. -/
theorem first_is_class_instant {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {a : ℝ} (ha : a ∈ ds) {T : ℝ}
    (hT : 0 < T) (hf : IsFirst ds T) :
    ∃ d ∈ ds, ∃ M : ℤ, 0 ≤ M ∧ T = (8 * (M : ℝ) + 1) / (8 * d) := by
  obtain ⟨⟨seq, h0, hmv, N, hN⟩, hall⟩ := cascade_landsG hpos ha hT hf
  have hT' := hall seq h0 hmv N hN
  have hb : 1 / (8 * a) ≤ T := Fresh.Cascade.bound_le_of_lonely ha (hpos a ha) hf.1 hT
  obtain ⟨d, hd, M, hM, he⟩ := cascade_term_class_instant hpos ha hf.1 hb seq h0 hmv N
  exact ⟨d, hd, M, hM, by rw [← hT', he]⟩

/-- Lonely at a class-1 instant of `d` iff every reading is good in the view through `d`. -/
theorem lonely_class_instant_iff {ds : Finset ℝ} {d : ℝ} (hd : 0 < d) (M : ℤ) :
    Fresh.Cascade.LonelyAt ds ((8 * (M : ℝ) + 1) / (8 * d)) ↔ ∀ f ∈ ds, GoodM d f M := by
  refine forall_congr' fun f => imp_congr_right fun _ => ?_
  exact clear_at_class_instant_iff_goodM d f hd.ne' M

/-- **The landing, read in the class-1 views.**  For any finite set of positive readings with `a` in it, a positive
`T` is the first lonely instant iff it is a class-1 instant `(8M+1)/(8d)` (`d` a reading, `M ≥ 0`) at which every
reading is good in the view through `d`, and no earlier class-1 instant of any reading has every reading good. -/
theorem isFirst_iff_least_goodM {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {a : ℝ} (ha : a ∈ ds) {T : ℝ}
    (hT : 0 < T) :
    IsFirst ds T ↔
      (∃ d ∈ ds, ∃ M : ℤ, 0 ≤ M ∧ T = (8 * (M : ℝ) + 1) / (8 * d) ∧ ∀ f ∈ ds, GoodM d f M) ∧
        ∀ d ∈ ds, ∀ M : ℤ, 0 ≤ M → (∀ f ∈ ds, GoodM d f M) → T ≤ (8 * (M : ℝ) + 1) / (8 * d) := by
  have cpos : ∀ d ∈ ds, ∀ M : ℤ, 0 ≤ M → 0 < (8 * (M : ℝ) + 1) / (8 * d) := by
    intro d hd M hM
    have := hpos d hd
    have : (0 : ℝ) ≤ M := by exact_mod_cast hM
    positivity
  constructor
  · intro hf
    obtain ⟨d, hd, M, hM, he⟩ := first_is_class_instant hpos ha hT hf
    refine ⟨⟨d, hd, M, hM, he, ?_⟩, fun d' hd' M' hM' hg => ?_⟩
    · rw [← lonely_class_instant_iff (hpos d hd) M, ← he]; exact hf.1
    · exact hf.2 _ (cpos d' hd' M' hM') ((lonely_class_instant_iff (hpos d' hd') M').mpr hg)
  · rintro ⟨⟨d, hd, M, hM, he, hg⟩, hmin⟩
    have hlT : Fresh.Cascade.LonelyAt ds T := by
      rw [he]; exact (lonely_class_instant_iff (hpos d hd) M).mpr hg
    refine ⟨hlT, fun s hs hl => ?_⟩
    -- the cascade from the bound fixes at a first lonely instant, which is a good class-1 instant
    have hb : 1 / (8 * a) ≤ s := Fresh.Cascade.bound_le_of_lonely ha (hpos a ha) hl hs
    have hb0 : 0 < 1 / (8 * a) := by have := hpos a ha; positivity
    obtain ⟨N, hN⟩ := Fresh.Cascade.exists_fixed_of_lonely hpos hb0 hl hb
    set seq := Fresh.Cascade.cascadeSeq ds (1 / (8 * a))
    have h0 : seq 0 = 1 / (8 * a) := Fresh.Cascade.cascadeSeq_zero _ _
    have hmv : ∀ n, IsMove ds (seq n) (seq (n + 1)) := Fresh.Cascade.cascadeSeq_isMove _ _
    obtain ⟨hlN, hminN⟩ := Fresh.Cascade.fixed_is_first_isolation hpos ha h0 hmv hN
    obtain ⟨d', hd', M', hM', he'⟩ := cascade_term_class_instant hpos ha hl hb seq h0 hmv N
    have hgN : ∀ f ∈ ds, GoodM d' f M' := by
      rw [← lonely_class_instant_iff (hpos d' hd') M', ← he']; exact hlN
    calc T ≤ (8 * (M' : ℝ) + 1) / (8 * d') := hmin d' hd' M' hM' hgN
      _ = seq N := he'.symm
      _ ≤ s := hminN s hs hl

#print axioms cascade_term_class_instant
#print axioms first_is_class_instant
#print axioms lonely_class_instant_iff
#print axioms isFirst_iff_least_goodM

end Fresh.OneMover
