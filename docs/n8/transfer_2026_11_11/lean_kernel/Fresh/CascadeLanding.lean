import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.OneMoverA

/-!
# The cascade's landing for the AP with one mover: shared lemmas

Written 2026-10-22.  New file; nothing existing is edited.  Imports `Fresh.Cascade` (the move, `LonelyAt`,
`fixed_is_first_isolation`, `exists_fixed_of_lonely`) and `Fresh.OneMoverA` (`FrozenClear`).

The mechanism (E310, the freeze rule).  The runners other than the mover are frozen: their own lonely instants do not
move.  For the frozen set `F_m = {1..7} \ {m}` (integer readings) the lonely instants in the first lap are a finite
list of closed pieces (isolated points and intervals).  The cascade's fixed point from `1/8` is the FIRST instant that
is lonely for the frozen set and clear for the mover (`fixed_is_first_isolation`).  So the mover only decides which
piece holds the landing:
* a piece `[l, r]` HOLDS for the mover `ρ` iff `ρ l` is clear, or the mover's next opening `(round (ρ l) + 1/8)/ρ`
  is at most `r`;
* the landing is `l` if `ρ l` is clear, else that opening (the mover is the setter);
* a piece that does not hold lies inside one mover zone: the mover is in the way throughout it.

This file proves the three facts about one piece (`holds_clear`, `not_holds_inWay`, `holds_of_len`), the link between
the cascade and the first lonely instant (`cascade_lands`), and the lonely test for `insert ρ (frozenSet m)`.
Grades: [L].  The step `holds_of_len` is a width fact (an interval of length at least 1/4 does not fit inside one open
zone of width 1/4); it is used only to bound the mover's size in the existence of a holding piece, and is tagged
**[PROVISIONAL: counting tool]** where used.
-/

open Classical

namespace Fresh.OneMover

open Fresh

/-- The first lonely instant: `T` is lonely and every positive lonely instant is at least `T`. -/
-- STANDING: DEFINITION
def IsFirst (ds : Finset ℝ) (T : ℝ) : Prop :=
  Fresh.Cascade.LonelyAt ds T ∧ ∀ s : ℝ, 0 < s → Fresh.Cascade.LonelyAt ds s → T ≤ s

/-- The frozen runners: integer readings `1..7` except `m`. -/
noncomputable def frozenSet (m : ℕ) : Finset ℝ :=
  ((Finset.Icc 1 7).erase m).image (fun i : ℕ => (i : ℝ))

theorem mem_frozenSet {m : ℕ} {d : ℝ} : d ∈ frozenSet m ↔ ∃ i : ℕ, 1 ≤ i ∧ i ≤ 7 ∧ i ≠ m ∧ (i : ℝ) = d := by
  unfold frozenSet
  simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_Icc]
  constructor
  · rintro ⟨i, ⟨hne, h1, h7⟩, rfl⟩; exact ⟨i, h1, h7, hne, rfl⟩
  · rintro ⟨i, h1, h7, hne, rfl⟩; exact ⟨i, ⟨hne, h1, h7⟩, rfl⟩

theorem lonely_insert_iff (m : ℕ) (ρ s : ℝ) :
    Fresh.Cascade.LonelyAt (insert ρ (frozenSet m)) s ↔ FrozenClear m s ∧ (1 / 8 : ℝ) ≤ distInt (ρ * s) := by
  unfold Fresh.Cascade.LonelyAt
  constructor
  · intro h
    refine ⟨fun i h1 h7 hne => ?_, h ρ (Finset.mem_insert_self _ _)⟩
    exact h (i : ℝ) (Finset.mem_insert_of_mem (mem_frozenSet.2 ⟨i, h1, h7, hne, rfl⟩))
  · rintro ⟨hF, hρ⟩ d hd
    rcases Finset.mem_insert.1 hd with rfl | hd
    · exact hρ
    · obtain ⟨i, h1, h7, hne, rfl⟩ := mem_frozenSet.1 hd
      exact hF i h1 h7 hne

theorem pos_insert {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ) : ∀ d ∈ insert ρ (frozenSet m), 0 < d := by
  intro d hd
  rcases Finset.mem_insert.1 hd with rfl | hd
  · exact hρ
  · obtain ⟨i, h1, _, _, rfl⟩ := mem_frozenSet.1 hd
    exact_mod_cast h1

theorem one_mem_insert {m : ℕ} (ρ : ℝ) (hm : m ≠ 1) : (1 : ℝ) ∈ insert ρ (frozenSet m) :=
  Finset.mem_insert_of_mem (mem_frozenSet.2 ⟨1, le_refl _, by norm_num, fun h => hm h.symm, by norm_num⟩)

/-- A window of width less than `1/4` around an integer puts the reading in the way. -/
theorem inWay_of_window {x : ℝ} (N : ℤ) (h1 : (N : ℝ) - 1 / 8 < x) (h2 : x < (N : ℝ) + 1 / 8) :
    distInt x < 1 / 8 := by
  have h := Fresh.Cascade.distInt_le x N
  have h' : |x - (N : ℝ)| < 1 / 8 := abs_lt.2 ⟨by linarith, by linarith⟩
  linarith

/-! ## One piece `[l, r]` against the mover `ρ` -/

/-- The piece `[l, r]` holds a clear point of the mover: `ρ l` clear, or the mover's next opening lies in the piece. -/
-- STANDING: DEFINITION
def Holds (ρ l r : ℝ) : Prop :=
  (1 / 8 : ℝ) ≤ distInt (ρ * l) ∨ (((round (ρ * l) : ℤ) : ℝ) + 1 / 8) / ρ ≤ r

/-- The first clear point of the mover in the piece. -/
noncomputable def firstPt (ρ l : ℝ) : ℝ :=
  if (1 / 8 : ℝ) ≤ distInt (ρ * l) then l else (((round (ρ * l) : ℤ) : ℝ) + 1 / 8) / ρ

theorem not_clear_window {ρ l : ℝ} (h : ¬ (1 / 8 : ℝ) ≤ distInt (ρ * l)) :
    ((round (ρ * l) : ℤ) : ℝ) - 1 / 8 < ρ * l ∧ ρ * l < ((round (ρ * l) : ℤ) : ℝ) + 1 / 8 := by
  have h' : |ρ * l - (round (ρ * l) : ℝ)| < 1 / 8 := by
    unfold distInt at h; push Not at h; exact h
  rw [abs_lt] at h'
  constructor <;> linarith [h'.1, h'.2]

/-- If the piece holds: `firstPt` is a clear point of the mover, lies in `[l, r]`, and the mover is in the way on
`[l, firstPt)`. -/
theorem holds_clear {ρ l r : ℝ} (hρ : 0 < ρ) (hlr : l ≤ r) (h : Holds ρ l r) :
    (1 / 8 : ℝ) ≤ distInt (ρ * firstPt ρ l) ∧ l ≤ firstPt ρ l ∧ firstPt ρ l ≤ r ∧
      ∀ s : ℝ, l ≤ s → s < firstPt ρ l → distInt (ρ * s) < 1 / 8 := by
  by_cases hc : (1 / 8 : ℝ) ≤ distInt (ρ * l)
  · have e : firstPt ρ l = l := by unfold firstPt; rw [if_pos hc]
    rw [e]
    exact ⟨hc, le_refl _, hlr, fun s h1 h2 => absurd h2 (not_lt.2 h1)⟩
  · have e : firstPt ρ l = (((round (ρ * l) : ℤ) : ℝ) + 1 / 8) / ρ := by unfold firstPt; rw [if_neg hc]
    have hr : (((round (ρ * l) : ℤ) : ℝ) + 1 / 8) / ρ ≤ r := by
      rcases h with h | h
      · exact absurd h hc
      · exact h
    obtain ⟨w1, w2⟩ := not_clear_window hc
    rw [e]
    refine ⟨?_, ?_, hr, ?_⟩
    · have : ρ * ((((round (ρ * l) : ℤ) : ℝ) + 1 / 8) / ρ) = ((round (ρ * l) : ℤ) : ℝ) + 1 / 8 := by
        field_simp
      rw [this]
      exact Fresh.Localisation.clear_of_window (round (ρ * l)) (by linarith) (by linarith)
    · rw [le_div_iff₀ hρ]; linarith
    · intro s hs1 hs2
      rw [lt_div_iff₀ hρ] at hs2
      apply inWay_of_window (round (ρ * l))
      · nlinarith
      · nlinarith

/-- If the piece does not hold, the mover is in the way throughout it. -/
theorem not_holds_inWay {ρ l r : ℝ} (hρ : 0 < ρ) (hlr : l ≤ r) (h : ¬ Holds ρ l r) :
    ∀ s : ℝ, l ≤ s → s ≤ r → distInt (ρ * s) < 1 / 8 := by
  unfold Holds at h
  push Not at h
  obtain ⟨hc, hr⟩ := h
  obtain ⟨w1, w2⟩ := not_clear_window (not_le.2 (by
    have := hc; exact this))
  intro s hs1 hs2
  rw [lt_div_iff₀ hρ] at hr
  have a1 := mul_le_mul_of_nonneg_left hs1 hρ.le
  have a2 := mul_le_mul_of_nonneg_left hs2 hρ.le
  apply inWay_of_window (round (ρ * l))
  · linarith
  · nlinarith

/-- A piece the mover does not hold has `ρ (r - l) < 1/4`: an interval of length at least `1/4` does not fit inside
one open zone of width `1/4`.  **[PROVISIONAL: counting tool]** (width against zone); it supports: for large `ρ` the
last listed piece holds. -/
theorem not_holds_len {ρ l r : ℝ} (hρ : 0 < ρ) (hlr : l ≤ r) (h : ¬ Holds ρ l r) : ρ * (r - l) < 1 / 4 := by
  unfold Holds at h
  push Not at h
  obtain ⟨hc, hr⟩ := h
  obtain ⟨w1, w2⟩ := not_clear_window (not_le.2 hc)
  rw [lt_div_iff₀ hρ] at hr
  nlinarith

/-! ## From the first lonely instant to the cascade -/

/-- If `T` is the first lonely instant and `1 ∈ ds` (so the bound is `1/8`), the cascade from `1/8` lands at `T`:
it reaches a fixed point, and every fixed point it reaches equals `T`. -/
theorem cascade_lands {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (h1 : (1 : ℝ) ∈ ds) {T : ℝ} (hT : 0 < T)
    (hf : IsFirst ds T) :
    (∃ seq : ℕ → ℝ, seq 0 = 1 / 8 ∧ (∀ n, IsMove ds (seq n) (seq (n + 1))) ∧ ∃ N, seq (N + 1) = seq N) ∧
      ∀ seq : ℕ → ℝ, seq 0 = 1 / 8 → (∀ n, IsMove ds (seq n) (seq (n + 1))) →
        ∀ N, seq (N + 1) = seq N → seq N = T := by
  have hb : (1 / (8 * (1 : ℝ))) ≤ T := Fresh.Cascade.bound_le_of_lonely h1 one_pos hf.1 hT
  have hb' : (1 / 8 : ℝ) ≤ T := by simpa using hb
  refine ⟨?_, ?_⟩
  · obtain ⟨N, hN⟩ := Fresh.Cascade.exists_fixed_of_lonely hpos (by norm_num : (0 : ℝ) < 1 / 8) hf.1 hb'
    exact ⟨Fresh.Cascade.cascadeSeq ds (1 / 8), Fresh.Cascade.cascadeSeq_zero _ _,
      Fresh.Cascade.cascadeSeq_isMove _ _, N, hN⟩
  · intro seq h0 hmv N hN
    have h0' : seq 0 = 1 / (8 * (1 : ℝ)) := by simpa using h0
    obtain ⟨hl, hmin⟩ := Fresh.Cascade.fixed_is_first_isolation hpos h1 h0' hmv hN
    have hge : seq 0 ≤ seq N := Fresh.Cascade.start_le_seq hpos hmv N
    have hpos' : 0 < seq N := lt_of_lt_of_le (by rw [h0]; norm_num) hge
    exact le_antisymm (hmin T hT hf.1) (hf.2 _ hpos' hl)


/-- Some frozen reading `i` is in the way at `s`: the frozen set is not clear there. -/
theorem frozen_not (m i : ℕ) (hi1 : 1 ≤ i) (hi7 : i ≤ 7) (hne : i ≠ m) (N : ℤ) (s : ℝ)
    (h1 : (N : ℝ) - 1 / 8 < (i : ℝ) * s) (h2 : (i : ℝ) * s < (N : ℝ) + 1 / 8) : ¬ FrozenClear m s :=
  fun hF => not_le.2 (inWay_of_window N h1 h2) (hF i hi1 hi7 hne)

/-- A piece the mover does not hold: a window integer for its two ends. -/
theorem not_holds_win {ρ l r : ℝ} (hρ : 0 < ρ) (h : ¬ Holds ρ l r) :
    ∃ N : ℤ, (N : ℝ) - 1 / 8 < ρ * l ∧ ρ * r < (N : ℝ) + 1 / 8 := by
  unfold Holds at h
  push Not at h
  obtain ⟨hc, hr⟩ := h
  obtain ⟨w1, _⟩ := not_clear_window (not_le.2 hc)
  rw [lt_div_iff₀ hρ] at hr
  exact ⟨round (ρ * l), w1, by linarith⟩

theorem int_ge_of_real {N K : ℤ} (h : (K : ℝ) - 1 < N) : K ≤ N := by
  have : ((K - 1 : ℤ) : ℝ) < N := by push_cast; exact h
  have := Int.cast_lt.mp this
  omega

theorem int_le_of_real {N K : ℤ} (h : (N : ℝ) < K + 1) : N ≤ K := by
  have : (N : ℝ) < ((K + 1 : ℤ) : ℝ) := by push_cast; exact h
  have := Int.cast_lt.mp this
  omega

/-- From a lonely instant and `1 ∈ ds`: `1/8 ≤ s`. -/
theorem lonely_ge_eighth {ds : Finset ℝ} (h1 : (1 : ℝ) ∈ ds) {s : ℝ} (hs : 0 < s)
    (hl : Fresh.Cascade.LonelyAt ds s) : (1 / 8 : ℝ) ≤ s := by
  have := Fresh.Cascade.bound_le_of_lonely h1 one_pos hl hs
  simpa using this

#print axioms holds_clear
#print axioms not_holds_inWay
#print axioms not_holds_len
#print axioms cascade_lands
#print axioms lonely_insert_iff

end Fresh.OneMover
