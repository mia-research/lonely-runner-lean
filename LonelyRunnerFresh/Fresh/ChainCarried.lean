import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.CascadeLanding

/-!
# A chain of carried instants of any length, any number of free readings (E757)

Written 2026-11-01.  New file; nothing existing is edited.  Any finite set `R` of frozen readings (rule 3, M037) and
any finite set `F` of free readings, all positive.  Start the cascade's move, restricted to the free readings, at an
instant `l` (`IsMove F`): while a free reading is in the way, jump to the largest next opening among the free readings
in the way.  No AP, no grid, no covering or counting step.

* `chain_blocked`: every instant in `[l, seq n)` has a free reading in the way.
* `chain_class`: every move lands on a free reading's next opening, a class-1 instant `(8k+1)/(8d)` at which that
  reading stands at exactly `1/8` (it is the setter of that move).
* `chain_lower`: if every frozen-clear instant before `l` has a free reading in the way, no landing of `F ∪ R` lies
  before any term of the chain.
* `chain_landing`: with that hypothesis, if the chain fixes at `seq K` and `R` is lonely there, then `seq K` is the
  landing of `F ∪ R`.
* `chain_setter_clear`: the setter of a move is clear at the instant it sets, so consecutive moves have different
  setters.
* `chain_fixed_iff`: the chain fixes at `seq K` iff every free reading is clear there.
* `chain_next_piece`: if the chain passes the piece's right end `r` and the frozen set is lonely nowhere in the gap to
  the next piece's left end `l'`, the hypothesis of `chain_lower` / `chain_landing` holds at `l'`.

E755 is `F = {ρ}` and E756 is `F = {g, h}`; here the number of moves is not bounded.  Grades: [L].
-/

namespace Fresh.OneMover

open Fresh

theorem lonelyAt_union {F R : Finset ℝ} {s : ℝ} :
    Fresh.Cascade.LonelyAt (F ∪ R) s ↔ Fresh.Cascade.LonelyAt F s ∧ Fresh.Cascade.LonelyAt R s := by
  unfold Fresh.Cascade.LonelyAt
  constructor
  · intro h; exact ⟨fun d hd => h d (Finset.mem_union_left _ hd), fun d hd => h d (Finset.mem_union_right _ hd)⟩
  · rintro ⟨h1, h2⟩ d hd
    rcases Finset.mem_union.mp hd with hd | hd
    · exact h1 d hd
    · exact h2 d hd

/-- **Every instant the chain has passed is blocked by a free reading.** -/
theorem chain_blocked {F : Finset ℝ} (hpos : ∀ d ∈ F, 0 < d) {l : ℝ} {seq : ℕ → ℝ} (h0 : seq 0 = l)
    (hmv : ∀ n, IsMove F (seq n) (seq (n + 1))) :
    ∀ n, ∀ s, l ≤ s → s < seq n → ∃ d ∈ F, InWay d s := by
  intro n
  induction n with
  | zero => intro s hs hsn; rw [h0] at hsn; exact absurd hs (not_le.mpr hsn)
  | succ n ih =>
    intro s hs hsn
    rcases lt_or_ge s (seq n) with hlt | hge
    · exact ih s hs hlt
    · rcases hmv n with ⟨_, he⟩ | ⟨d, hd, hw, he, _⟩
      · rw [he] at hsn; exact absurd hge (not_le.mpr hsn)
      · rw [he] at hsn
        exact ⟨d, hd, Fresh.Cascade.inWay_until_opening (hpos d hd) hw hge hsn⟩

/-- **Every move lands on a free reading's class-1 instant, where that reading stands at exactly `1/8`.** -/
theorem chain_class {F : Finset ℝ} (hpos : ∀ d ∈ F, 0 < d) {seq : ℕ → ℝ}
    (hmv : ∀ n, IsMove F (seq n) (seq (n + 1))) (n : ℕ) (hne : seq (n + 1) ≠ seq n) :
    ∃ d ∈ F, ∃ k : ℤ, seq (n + 1) = (8 * (k : ℝ) + 1) / (8 * d) ∧ distInt (d * seq (n + 1)) = 1 / 8 := by
  rcases hmv n with ⟨_, he⟩ | ⟨d, hd, hw, he, _⟩
  · exact absurd he hne
  · obtain ⟨k, hk⟩ := Fresh.Cascade.exists_near_int hw
    have hd0 := hpos d hd
    refine ⟨d, hd, k, ?_, ?_⟩
    · rw [he, Fresh.Cascade.nextOpening_eq hk]; field_simp
    · rw [he]; exact Fresh.Cascade.distInt_at_nextOpening hd0

/-- **No landing before the chain.** -/
theorem chain_lower {F R : Finset ℝ} (hpos : ∀ d ∈ F, 0 < d) {l : ℝ} {seq : ℕ → ℝ} (h0 : seq 0 = l)
    (hmv : ∀ n, IsMove F (seq n) (seq (n + 1)))
    (hb : ∀ s : ℝ, 0 < s → s < l → Fresh.Cascade.LonelyAt R s → ∃ d ∈ F, InWay d s)
    {T : ℝ} (hT : 0 < T) (hl : Fresh.Cascade.LonelyAt (F ∪ R) T) : ∀ n, seq n ≤ T := by
  obtain ⟨hF, hR⟩ := lonelyAt_union.mp hl
  have hfree : ¬ ∃ d ∈ F, InWay d T := by
    rintro ⟨d, hd, hw⟩; exact Fresh.Cascade.not_inWay_iff.mpr (hF d hd) hw
  have hlT : l ≤ T := by
    by_contra h; push Not at h; exact hfree (hb T hT h hR)
  intro n
  by_contra h; push Not at h
  exact hfree (chain_blocked hpos h0 hmv n T hlT h)

/-- **The landing at the end of the chain.** -/
theorem chain_landing {F R : Finset ℝ} (hpos : ∀ d ∈ F, 0 < d) {l : ℝ} {seq : ℕ → ℝ} (h0 : seq 0 = l)
    (hmv : ∀ n, IsMove F (seq n) (seq (n + 1)))
    (hb : ∀ s : ℝ, 0 < s → s < l → Fresh.Cascade.LonelyAt R s → ∃ d ∈ F, InWay d s)
    {K : ℕ} (hK : seq (K + 1) = seq K) (hR : Fresh.Cascade.LonelyAt R (seq K)) :
    IsFirst (F ∪ R) (seq K) := by
  have hF : Fresh.Cascade.LonelyAt F (seq K) := by
    have := hmv K; rw [hK] at this; exact (Fresh.Cascade.isMove_self_iff hpos).mp this
  exact ⟨lonelyAt_union.mpr ⟨hF, hR⟩, fun s hs hl => chain_lower hpos h0 hmv hb hs hl K⟩

/-- The chain fixes exactly where every free reading is clear. -/
theorem chain_fixed_iff {F : Finset ℝ} (hpos : ∀ d ∈ F, 0 < d) {seq : ℕ → ℝ}
    (hmv : ∀ n, IsMove F (seq n) (seq (n + 1))) (K : ℕ) :
    seq (K + 1) = seq K ↔ Fresh.Cascade.LonelyAt F (seq K) := by
  constructor
  · intro hK; have := hmv K; rw [hK] at this; exact (Fresh.Cascade.isMove_self_iff hpos).mp this
  · intro hl
    exact Fresh.Cascade.isMove_unique (hmv K) ((Fresh.Cascade.isMove_self_iff hpos).mpr hl)

/-- **From one piece to the next.**  If the chain from `l` passes `r` and the frozen set is lonely nowhere in the gap
`(r, l')`, then every frozen-clear instant before `l'` has a free reading in the way: the hypothesis `hb` for the chain
started at the next piece's left end `l'`. -/
theorem chain_next_piece {F R : Finset ℝ} (hpos : ∀ d ∈ F, 0 < d) {l r l' : ℝ} {seq : ℕ → ℝ} (h0 : seq 0 = l)
    (hmv : ∀ n, IsMove F (seq n) (seq (n + 1)))
    (hb : ∀ s : ℝ, 0 < s → s < l → Fresh.Cascade.LonelyAt R s → ∃ d ∈ F, InWay d s)
    {n : ℕ} (hn : r < seq n) (hgap : ∀ s : ℝ, r < s → s < l' → ¬ Fresh.Cascade.LonelyAt R s) :
    ∀ s : ℝ, 0 < s → s < l' → Fresh.Cascade.LonelyAt R s → ∃ d ∈ F, InWay d s := by
  intro s hs hsl hR
  rcases lt_or_ge s l with h1 | h1
  · exact hb s hs h1 hR
  rcases le_or_gt s r with h2 | h2
  · exact chain_blocked hpos h0 hmv n s h1 (lt_of_le_of_lt h2 hn)
  · exact absurd hR (hgap s h2 hsl)

/-- **The setter changes at every move.**  The reading that sets a move stands on its own leaving edge there, so it
is not in the way and cannot set the next move. -/
theorem chain_setter_clear {d t : ℝ} (hd : 0 < d) : ¬ InWay d (nextOpening d t) :=
  Fresh.Cascade.not_inWay_at_nextOpening hd

#print axioms lonelyAt_union
#print axioms chain_setter_clear
#print axioms chain_next_piece
#print axioms chain_blocked
#print axioms chain_class
#print axioms chain_lower
#print axioms chain_landing
#print axioms chain_fixed_iff

end Fresh.OneMover
