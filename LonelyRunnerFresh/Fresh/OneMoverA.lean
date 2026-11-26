import Mathlib
import Fresh.Framework
import Fresh.Localisation

/-!
# S1, family A: the AP with one reading removed and one free reading (GENERATED; see experiments/n8/s1_gen_lean_A_v1.py)

Written 2026-10-22.  New file; nothing existing is edited.  Imports Mathlib, `Fresh.Framework`, `Fresh.Localisation`.

Frozen readings `F_j = {1, ..., 7} \ {j}` (the AP gaps seen by the end subject, with the reading `j` removed) and one
free reading `d > 0`.  `family_j` : for every real `d > 0` there is a positive instant at which every reading of `F_j`
and `d` are at circle distance at least `1/8` from an integer.  No density, cap, move count or clock is used: the
witnesses are constant instants (grid and frozen openings), the mover's own openings `(n + 1/8)/d`, a shifted copy of the
frozen window for `d ≤ 3/4`, and the mover's openings inside a frozen window for large `d`.  The ranges of `d` served by
each witness are a finite list of closed intervals computed in exact rationals (`s1_cover_v2.json`) and re-proved here.
Grades: [L] for every theorem.  Tags under rule 7 of `RULES_n8_v4` (relaxed 2026-10-05): the covering of `(3/4, D_j]` by
finitely many pieces is [PROVISIONAL: covering]; `small_d` and `tail_window` are [PROVISIONAL: counting tool].  The
relaxation can be withdrawn by the owner, and the steps resting on it with it.  These are existence witnesses, not the
cascade's own landing: they do not say where the cascade lands or why.
-/

open Classical

namespace Fresh.OneMover

open Fresh Fresh.Localisation

/-- The frozen readings `1..7` other than `j` are all clear at `t`. -/
-- STANDING: DEFINITION
def FrozenClear (j : ℕ) (t : ℝ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ 7 → i ≠ j → (1 / 8 : ℝ) ≤ distInt ((i : ℝ) * t)

theorem frozen_intro (j : ℕ) (t : ℝ)
    (h1 : j ≠ 1 → (1 / 8 : ℝ) ≤ distInt ((1 : ℝ) * t)) (h2 : j ≠ 2 → (1 / 8 : ℝ) ≤ distInt ((2 : ℝ) * t))
    (h3 : j ≠ 3 → (1 / 8 : ℝ) ≤ distInt ((3 : ℝ) * t)) (h4 : j ≠ 4 → (1 / 8 : ℝ) ≤ distInt ((4 : ℝ) * t))
    (h5 : j ≠ 5 → (1 / 8 : ℝ) ≤ distInt ((5 : ℝ) * t)) (h6 : j ≠ 6 → (1 / 8 : ℝ) ≤ distInt ((6 : ℝ) * t))
    (h7 : j ≠ 7 → (1 / 8 : ℝ) ≤ distInt ((7 : ℝ) * t)) : FrozenClear j t := by
  intro i hi1 hi7 hij
  interval_cases i
  · simpa using h1 (fun h => hij h.symm)
  · simpa using h2 (fun h => hij h.symm)
  · simpa using h3 (fun h => hij h.symm)
  · simpa using h4 (fun h => hij h.symm)
  · simpa using h5 (fun h => hij h.symm)
  · simpa using h6 (fun h => hij h.symm)
  · simpa using h7 (fun h => hij h.symm)

theorem clear_div {X d : ℝ} (hd : 0 < d) (N : ℤ) (h1 : ((N : ℝ) + 1 / 8) * d ≤ X)
    (h2 : X ≤ ((N : ℝ) + 7 / 8) * d) : (1 / 8 : ℝ) ≤ distInt (X / d) :=
  clear_of_window N ((le_div_iff₀ hd).2 h1) ((div_le_iff₀ hd).2 h2)

theorem clear_scaled {i l r t : ℝ} (N : ℤ) (hi : 0 ≤ i) (hl : l ≤ t) (hr : t ≤ r)
    (h1 : (N : ℝ) + 1 / 8 ≤ i * l) (h2 : i * r ≤ (N : ℝ) + 7 / 8) : (1 / 8 : ℝ) ≤ distInt (i * t) :=
  clear_of_window N (le_trans h1 (mul_le_mul_of_nonneg_left hl hi))
    (le_trans (mul_le_mul_of_nonneg_left hr hi) h2)

/-- Every frozen reading is clear at `N + 1/8`: the grid instant `1/8`, shifted by whole laps. -/
theorem frozen_shift (j N : ℕ) : FrozenClear j ((N : ℝ) + 1 / 8) := by
  intro i hi1 hi7 _
  have h1 : (1 : ℝ) ≤ i := by exact_mod_cast hi1
  have h7 : (i : ℝ) ≤ 7 := by exact_mod_cast hi7
  have e : (i : ℝ) * ((N : ℝ) + 1 / 8) = (i : ℝ) / 8 + (((i * N : ℕ) : ℤ) : ℝ) := by push_cast; ring
  rw [e, distInt_add_int]
  exact clear_of_window 0 (by push_cast; linarith) (by push_cast; linarith)

/-- Small `d` (`d ≤ 3/4`): the shifted grid instant `N + 1/8` serves, with `N` the least integer such that the mover has
come round to `1/8`.  **[PROVISIONAL: counting tool]** equally spaced points `d (N + 1/8)` (step `d ≤ 3/4`) against the
clear arc `[1/8, 7/8]` of length `3/4`; it supports: for every `d ∈ (0, 3/4]` the frozen set and `d` are clear at some
positive instant. -/
theorem small_d (j : ℕ) (d : ℝ) (hd : 0 < d) (hd34 : d ≤ 3 / 4) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear j t ∧ (1 / 8 : ℝ) ≤ distInt (d * t) := by
  have hx : 0 ≤ 1 / (8 * d) - 1 / 8 := by
    have : (1 : ℝ) / 8 ≤ 1 / (8 * d) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    linarith
  set x : ℝ := 1 / (8 * d) - 1 / 8 with hxdef
  have hdx : d * x = 1 / 8 - d / 8 := by rw [hxdef]; field_simp
  have hN1 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hN2 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
  refine ⟨(⌈x⌉₊ : ℝ) + 1 / 8, by positivity, frozen_shift j ⌈x⌉₊, ?_⟩
  apply clear_of_window 0
  · have := mul_le_mul_of_nonneg_left hN1 hd.le
    push_cast; nlinarith
  · have := mul_le_mul_of_nonneg_left hN2.le hd.le
    push_cast; nlinarith

/-- Large `d`: a window `[l, r]` of the frozen set holds a mover opening `(n + 1/8)/d` once `(r - l) d ≥ 1`.
**[PROVISIONAL: counting tool]** the mover's openings `(n + 1/8)/d` are spaced `1/d` apart and a window of length at least
`1/d` holds one; it supports: for every `d` beyond the window threshold the frozen set and `d` are clear at some instant. -/
theorem tail_window (l r d : ℝ) (hl : 0 < l) (hd : 0 < d) (hw : 1 ≤ (r - l) * d) :
    ∃ n : ℕ, l ≤ ((n : ℝ) + 1 / 8) / d ∧ ((n : ℝ) + 1 / 8) / d ≤ r := by
  have hld : 0 < l * d := mul_pos hl hd
  have hrd : l * d + 1 ≤ r * d := by nlinarith
  by_cases hx : 0 ≤ l * d - 1 / 8
  · refine ⟨⌈l * d - 1 / 8⌉₊, ?_, ?_⟩
    · rw [le_div_iff₀ hd]; have := Nat.le_ceil (l * d - 1 / 8); linarith
    · rw [div_le_iff₀ hd]; have := Nat.ceil_lt_add_one hx; linarith
  · refine ⟨0, ?_, ?_⟩
    · rw [le_div_iff₀ hd]; push_cast; linarith
    · rw [div_le_iff₀ hd]; push_cast; linarith


/-! ## Family j = 1 : frozen readings [2, 3, 4, 5, 6, 7] -/

theorem tail_1 (d : ℝ) (hd : (16 : ℝ) ≤ d) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 1 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  obtain ⟨n, h1, h2⟩ := tail_window (1/16 : ℝ) (1/8 : ℝ) d (by norm_num) hd0 (by nlinarith [hd])
  have hpos : 0 < ((n : ℝ) + 1/8) / d := by positivity
  refine ⟨((n : ℝ) + 1/8) / d, hpos, frozen_intro 1 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro h; exact absurd rfl h
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · have e : d * (((n : ℝ) + 1/8) / d) = (n : ℝ) + 1/8 := by field_simp
    rw [e]; exact clear_of_window (n : ℤ) (by push_cast; linarith) (by push_cast; linarith)

/-- **[PROVISIONAL: covering]** one piece of `family_1`: a constant instant serves for `d` in this interval. -/
theorem piece_1_1 (d : ℝ) (ha : (3/4 : ℝ) ≤ d) (hb : d ≤ (7/3 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 1 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(3/8 : ℝ), by norm_num, frozen_intro 1 (3/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · exact clear_of_window 0 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_1`: a constant instant serves for `d` in this interval. -/
theorem piece_1_2 (d : ℝ) (ha : (7/3 : ℝ) ≤ d) (hb : d ≤ (14 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 1 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/16 : ℝ), by norm_num, frozen_intro 1 (1/16 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 0 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_1`: the mover's own opening serves for `d` in this interval. -/
theorem piece_1_3 (d : ℝ) (ha : (14 : ℝ) ≤ d) (hb : d ≤ (16 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 1 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  have hd : 0 < d := by linarith
  refine ⟨((1 : ℝ) + 1/8) / d, by positivity, frozen_intro 1 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro h; exact absurd rfl h
  · intro _
    have e : (2 : ℝ) * (((1 : ℝ) + 1/8) / d) = ((2 : ℝ) * ((1 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (3 : ℝ) * (((1 : ℝ) + 1/8) / d) = ((3 : ℝ) * ((1 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (4 : ℝ) * (((1 : ℝ) + 1/8) / d) = ((4 : ℝ) * ((1 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (5 : ℝ) * (((1 : ℝ) + 1/8) / d) = ((5 : ℝ) * ((1 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (6 : ℝ) * (((1 : ℝ) + 1/8) / d) = ((6 : ℝ) * ((1 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (7 : ℝ) * (((1 : ℝ) + 1/8) / d) = ((7 : ℝ) * ((1 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · have e : d * (((1 : ℝ) + 1/8) / d) = (1 : ℝ) + 1/8 := by field_simp
    rw [e]; exact clear_of_window 1 (by norm_num) (by norm_num)

/-- **[PROVISIONAL: covering]** supports: for every free reading `d` in `(3/4, 16]` one of the 3 pieces above serves, so with `small_d` and `tail_1` the frozen set `F_1` and `d` have a common clear instant for every `d > 0`. -/
theorem family_1 (d : ℝ) (hd : 0 < d) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 1 t ∧ (1 / 8 : ℝ) ≤ distInt (d * t) := by
  by_cases h0 : d ≤ 3 / 4
  · exact small_d 1 d hd h0
  by_cases c1 : d ≤ (7/3 : ℝ)
  · exact piece_1_1 d (by linarith) c1
  by_cases c2 : d ≤ (14 : ℝ)
  · exact piece_1_2 d (by linarith) c2
  by_cases c3 : d ≤ (16 : ℝ)
  · exact piece_1_3 d (by linarith) c3
  exact tail_1 d (by linarith)

/-! ## Family j = 2 : frozen readings [1, 3, 4, 5, 6, 7] -/

theorem tail_2 (d : ℝ) (hd : (224/5 : ℝ) ≤ d) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 2 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  obtain ⟨n, h1, h2⟩ := tail_window (25/56 : ℝ) (15/32 : ℝ) d (by norm_num) hd0 (by nlinarith [hd])
  have hpos : 0 < ((n : ℝ) + 1/8) / d := by positivity
  refine ⟨((n : ℝ) + 1/8) / d, hpos, frozen_intro 2 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_scaled 1 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 1 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 2 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 2 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 3 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · have e : d * (((n : ℝ) + 1/8) / d) = (n : ℝ) + 1/8 := by field_simp
    rw [e]; exact clear_of_window (n : ℤ) (by push_cast; linarith) (by push_cast; linarith)

/-- **[PROVISIONAL: covering]** one piece of `family_2`: a constant instant serves for `d` in this interval. -/
theorem piece_2_1 (d : ℝ) (ha : (3/4 : ℝ) ≤ d) (hb : d ≤ (7/3 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 2 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(3/8 : ℝ), by norm_num, frozen_intro 2 (3/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · exact clear_of_window 0 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_2`: a constant instant serves for `d` in this interval. -/
theorem piece_2_2 (d : ℝ) (ha : (7/3 : ℝ) ≤ d) (hb : d ≤ (7 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 2 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 2 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 0 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_2`: a constant instant serves for `d` in this interval. -/
theorem piece_2_3 (d : ℝ) (ha : (7 : ℝ) ≤ d) (hb : d ≤ (217/25 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 2 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(25/56 : ℝ), by norm_num, frozen_intro 2 (25/56 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 3 (by norm_num) (by norm_num)
  · exact clear_of_window 3 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_2`: a constant instant serves for `d` in this interval. -/
theorem piece_2_4 (d : ℝ) (ha : (217/25 : ℝ) ≤ d) (hb : d ≤ (31/3 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 2 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(3/8 : ℝ), by norm_num, frozen_intro 2 (3/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · exact clear_of_window 3 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_2`: a constant instant serves for `d` in this interval. -/
theorem piece_2_5 (d : ℝ) (ha : (31/3 : ℝ) ≤ d) (hb : d ≤ (15 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 2 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 2 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 1 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_2`: a constant instant serves for `d` in this interval. -/
theorem piece_2_6 (d : ℝ) (ha : (15 : ℝ) ≤ d) (hb : d ≤ (111/7 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 2 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(7/8 : ℝ), by norm_num, frozen_intro 2 (7/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 3 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 4 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 5 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 6 (by norm_num) (by norm_num)
  · exact clear_of_window 13 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_2`: a constant instant serves for `d` in this interval. -/
theorem piece_2_7 (d : ℝ) (ha : (111/7 : ℝ) ≤ d) (hb : d ≤ (284/17 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 2 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(17/32 : ℝ), by norm_num, frozen_intro 2 (17/32 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 3 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 3 (by norm_num) (by norm_num)
  · exact clear_of_window 8 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_2`: a constant instant serves for `d` in this interval. -/
theorem piece_2_8 (d : ℝ) (ha : (284/17 : ℝ) ≤ d) (hb : d ≤ (55/3 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 2 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(3/8 : ℝ), by norm_num, frozen_intro 2 (3/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · exact clear_of_window 6 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_2`: a constant instant serves for `d` in this interval. -/
theorem piece_2_9 (d : ℝ) (ha : (55/3 : ℝ) ≤ d) (hb : d ≤ (23 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 2 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 2 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 2 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_2`: a constant instant serves for `d` in this interval. -/
theorem piece_2_10 (d : ℝ) (ha : (23 : ℝ) ≤ d) (hb : d ≤ (609/25 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 2 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(25/56 : ℝ), by norm_num, frozen_intro 2 (25/56 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 3 (by norm_num) (by norm_num)
  · exact clear_of_window 10 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_2`: a constant instant serves for `d` in this interval. -/
theorem piece_2_11 (d : ℝ) (ha : (609/25 : ℝ) ≤ d) (hb : d ≤ (79/3 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 2 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(3/8 : ℝ), by norm_num, frozen_intro 2 (3/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · exact clear_of_window 9 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_2`: a constant instant serves for `d` in this interval. -/
theorem piece_2_12 (d : ℝ) (ha : (79/3 : ℝ) ≤ d) (hb : d ≤ (31 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 2 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 2 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 3 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_2`: the mover's own opening serves for `d` in this interval. -/
theorem piece_2_13 (d : ℝ) (ha : (31 : ℝ) ≤ d) (hb : d ≤ (548/17 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 2 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  have hd : 0 < d := by linarith
  refine ⟨((17 : ℝ) + 1/8) / d, by positivity, frozen_intro 2 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    have e : (1 : ℝ) * (((17 : ℝ) + 1/8) / d) = ((1 : ℝ) * ((17 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro h; exact absurd rfl h
  · intro _
    have e : (3 : ℝ) * (((17 : ℝ) + 1/8) / d) = ((3 : ℝ) * ((17 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 1 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (4 : ℝ) * (((17 : ℝ) + 1/8) / d) = ((4 : ℝ) * ((17 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 2 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (5 : ℝ) * (((17 : ℝ) + 1/8) / d) = ((5 : ℝ) * ((17 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 2 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (6 : ℝ) * (((17 : ℝ) + 1/8) / d) = ((6 : ℝ) * ((17 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 3 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (7 : ℝ) * (((17 : ℝ) + 1/8) / d) = ((7 : ℝ) * ((17 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 3 (by push_cast; linarith) (by push_cast; linarith)
  · have e : d * (((17 : ℝ) + 1/8) / d) = (17 : ℝ) + 1/8 := by field_simp
    rw [e]; exact clear_of_window 17 (by norm_num) (by norm_num)

/-- **[PROVISIONAL: covering]** one piece of `family_2`: a constant instant serves for `d` in this interval. -/
theorem piece_2_14 (d : ℝ) (ha : (548/17 : ℝ) ≤ d) (hb : d ≤ (572/17 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 2 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(17/32 : ℝ), by norm_num, frozen_intro 2 (17/32 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 3 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 3 (by norm_num) (by norm_num)
  · exact clear_of_window 17 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_2`: a constant instant serves for `d` in this interval. -/
theorem piece_2_15 (d : ℝ) (ha : (572/17 : ℝ) ≤ d) (hb : d ≤ (39 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 2 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 2 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 4 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_2`: the mover's own opening serves for `d` in this interval. -/
theorem piece_2_16 (d : ℝ) (ha : (39 : ℝ) ≤ d) (hb : d ≤ (203/5 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 2 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  have hd : 0 < d := by linarith
  refine ⟨((18 : ℝ) + 1/8) / d, by positivity, frozen_intro 2 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    have e : (1 : ℝ) * (((18 : ℝ) + 1/8) / d) = ((1 : ℝ) * ((18 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro h; exact absurd rfl h
  · intro _
    have e : (3 : ℝ) * (((18 : ℝ) + 1/8) / d) = ((3 : ℝ) * ((18 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 1 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (4 : ℝ) * (((18 : ℝ) + 1/8) / d) = ((4 : ℝ) * ((18 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 1 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (5 : ℝ) * (((18 : ℝ) + 1/8) / d) = ((5 : ℝ) * ((18 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 2 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (6 : ℝ) * (((18 : ℝ) + 1/8) / d) = ((6 : ℝ) * ((18 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 2 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (7 : ℝ) * (((18 : ℝ) + 1/8) / d) = ((7 : ℝ) * ((18 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 3 (by push_cast; linarith) (by push_cast; linarith)
  · have e : d * (((18 : ℝ) + 1/8) / d) = (18 : ℝ) + 1/8 := by field_simp
    rw [e]; exact clear_of_window 18 (by norm_num) (by norm_num)

/-- **[PROVISIONAL: covering]** one piece of `family_2`: a constant instant serves for `d` in this interval. -/
theorem piece_2_17 (d : ℝ) (ha : (203/5 : ℝ) ≤ d) (hb : d ≤ (127/3 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 2 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(3/8 : ℝ), by norm_num, frozen_intro 2 (3/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · exact clear_of_window 15 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_2`: a constant instant serves for `d` in this interval. -/
theorem piece_2_18 (d : ℝ) (ha : (127/3 : ℝ) ≤ d) (hb : d ≤ (45 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 2 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 2 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 5 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** supports: for every free reading `d` in `(3/4, 45]` one of the 18 pieces above serves, so with `small_d` and `tail_2` the frozen set `F_2` and `d` have a common clear instant for every `d > 0`. -/
theorem family_2 (d : ℝ) (hd : 0 < d) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 2 t ∧ (1 / 8 : ℝ) ≤ distInt (d * t) := by
  by_cases h0 : d ≤ 3 / 4
  · exact small_d 2 d hd h0
  by_cases c1 : d ≤ (7/3 : ℝ)
  · exact piece_2_1 d (by linarith) c1
  by_cases c2 : d ≤ (7 : ℝ)
  · exact piece_2_2 d (by linarith) c2
  by_cases c3 : d ≤ (217/25 : ℝ)
  · exact piece_2_3 d (by linarith) c3
  by_cases c4 : d ≤ (31/3 : ℝ)
  · exact piece_2_4 d (by linarith) c4
  by_cases c5 : d ≤ (15 : ℝ)
  · exact piece_2_5 d (by linarith) c5
  by_cases c6 : d ≤ (111/7 : ℝ)
  · exact piece_2_6 d (by linarith) c6
  by_cases c7 : d ≤ (284/17 : ℝ)
  · exact piece_2_7 d (by linarith) c7
  by_cases c8 : d ≤ (55/3 : ℝ)
  · exact piece_2_8 d (by linarith) c8
  by_cases c9 : d ≤ (23 : ℝ)
  · exact piece_2_9 d (by linarith) c9
  by_cases c10 : d ≤ (609/25 : ℝ)
  · exact piece_2_10 d (by linarith) c10
  by_cases c11 : d ≤ (79/3 : ℝ)
  · exact piece_2_11 d (by linarith) c11
  by_cases c12 : d ≤ (31 : ℝ)
  · exact piece_2_12 d (by linarith) c12
  by_cases c13 : d ≤ (548/17 : ℝ)
  · exact piece_2_13 d (by linarith) c13
  by_cases c14 : d ≤ (572/17 : ℝ)
  · exact piece_2_14 d (by linarith) c14
  by_cases c15 : d ≤ (39 : ℝ)
  · exact piece_2_15 d (by linarith) c15
  by_cases c16 : d ≤ (203/5 : ℝ)
  · exact piece_2_16 d (by linarith) c16
  by_cases c17 : d ≤ (127/3 : ℝ)
  · exact piece_2_17 d (by linarith) c17
  by_cases c18 : d ≤ (45 : ℝ)
  · exact piece_2_18 d (by linarith) c18
  exact tail_2 d (by linarith)

/-! ## Family j = 3 : frozen readings [1, 2, 4, 5, 6, 7] -/

theorem tail_3 (d : ℝ) (hd : (48 : ℝ) ≤ d) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 3 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  obtain ⟨n, h1, h2⟩ := tail_window (17/48 : ℝ) (3/8 : ℝ) d (by norm_num) hd0 (by nlinarith [hd])
  have hpos : 0 < ((n : ℝ) + 1/8) / d := by positivity
  refine ⟨((n : ℝ) + 1/8) / d, hpos, frozen_intro 3 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_scaled 1 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 1 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 2 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 2 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · have e : d * (((n : ℝ) + 1/8) / d) = (n : ℝ) + 1/8 := by field_simp
    rw [e]; exact clear_of_window (n : ℤ) (by push_cast; linarith) (by push_cast; linarith)

/-- **[PROVISIONAL: covering]** one piece of `family_3`: a constant instant serves for `d` in this interval. -/
theorem piece_3_1 (d : ℝ) (ha : (3/4 : ℝ) ≤ d) (hb : d ≤ (49/17 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 3 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(17/56 : ℝ), by norm_num, frozen_intro 3 (17/56 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · exact clear_of_window 0 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_3`: a constant instant serves for `d` in this interval. -/
theorem piece_3_2 (d : ℝ) (ha : (49/17 : ℝ) ≤ d) (hb : d ≤ (7 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 3 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 3 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 0 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_3`: a constant instant serves for `d` in this interval. -/
theorem piece_3_3 (d : ℝ) (ha : (7 : ℝ) ≤ d) (hb : d ≤ (161/17 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 3 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(17/56 : ℝ), by norm_num, frozen_intro 3 (17/56 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · exact clear_of_window 2 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_3`: a constant instant serves for `d` in this interval. -/
theorem piece_3_4 (d : ℝ) (ha : (161/17 : ℝ) ≤ d) (hb : d ≤ (15 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 3 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 3 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 1 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_3`: a constant instant serves for `d` in this interval. -/
theorem piece_3_5 (d : ℝ) (ha : (15 : ℝ) ≤ d) (hb : d ≤ (282/17 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 3 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(17/48 : ℝ), by norm_num, frozen_intro 3 (17/48 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · exact clear_of_window 5 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_3`: a constant instant serves for `d` in this interval. -/
theorem piece_3_6 (d : ℝ) (ha : (282/17 : ℝ) ≤ d) (hb : d ≤ (55/3 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 3 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(3/8 : ℝ), by norm_num, frozen_intro 3 (3/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · exact clear_of_window 6 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_3`: a constant instant serves for `d` in this interval. -/
theorem piece_3_7 (d : ℝ) (ha : (55/3 : ℝ) ≤ d) (hb : d ≤ (23 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 3 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 3 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 2 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_3`: a constant instant serves for `d` in this interval. -/
theorem piece_3_8 (d : ℝ) (ha : (23 : ℝ) ≤ d) (hb : d ≤ (426/17 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 3 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(17/48 : ℝ), by norm_num, frozen_intro 3 (17/48 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · exact clear_of_window 8 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_3`: a constant instant serves for `d` in this interval. -/
theorem piece_3_9 (d : ℝ) (ha : (426/17 : ℝ) ≤ d) (hb : d ≤ (31 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 3 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 3 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 3 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_3`: a constant instant serves for `d` in this interval. -/
theorem piece_3_10 (d : ℝ) (ha : (31 : ℝ) ≤ d) (hb : d ≤ (553/17 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 3 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(17/56 : ℝ), by norm_num, frozen_intro 3 (17/56 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · exact clear_of_window 9 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_3`: a constant instant serves for `d` in this interval. -/
theorem piece_3_11 (d : ℝ) (ha : (553/17 : ℝ) ≤ d) (hb : d ≤ (103/3 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 3 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(3/8 : ℝ), by norm_num, frozen_intro 3 (3/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · exact clear_of_window 12 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_3`: a constant instant serves for `d` in this interval. -/
theorem piece_3_12 (d : ℝ) (ha : (103/3 : ℝ) ≤ d) (hb : d ≤ (39 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 3 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 3 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 4 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_3`: the mover's own opening serves for `d` in this interval. -/
theorem piece_3_13 (d : ℝ) (ha : (39 : ℝ) ≤ d) (hb : d ≤ (201/5 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 3 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  have hd : 0 < d := by linarith
  refine ⟨((25 : ℝ) + 1/8) / d, by positivity, frozen_intro 3 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    have e : (1 : ℝ) * (((25 : ℝ) + 1/8) / d) = ((1 : ℝ) * ((25 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (2 : ℝ) * (((25 : ℝ) + 1/8) / d) = ((2 : ℝ) * ((25 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 1 (by push_cast; linarith) (by push_cast; linarith)
  · intro h; exact absurd rfl h
  · intro _
    have e : (4 : ℝ) * (((25 : ℝ) + 1/8) / d) = ((4 : ℝ) * ((25 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 2 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (5 : ℝ) * (((25 : ℝ) + 1/8) / d) = ((5 : ℝ) * ((25 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 3 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (6 : ℝ) * (((25 : ℝ) + 1/8) / d) = ((6 : ℝ) * ((25 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 3 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (7 : ℝ) * (((25 : ℝ) + 1/8) / d) = ((7 : ℝ) * ((25 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 4 (by push_cast; linarith) (by push_cast; linarith)
  · have e : d * (((25 : ℝ) + 1/8) / d) = (25 : ℝ) + 1/8 := by field_simp
    rw [e]; exact clear_of_window 25 (by norm_num) (by norm_num)

/-- **[PROVISIONAL: covering]** one piece of `family_3`: a constant instant serves for `d` in this interval. -/
theorem piece_3_14 (d : ℝ) (ha : (201/5 : ℝ) ≤ d) (hb : d ≤ (721/17 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 3 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(17/56 : ℝ), by norm_num, frozen_intro 3 (17/56 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · exact clear_of_window 12 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_3`: a constant instant serves for `d` in this interval. -/
theorem piece_3_15 (d : ℝ) (ha : (721/17 : ℝ) ≤ d) (hb : d ≤ (47 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 3 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 3 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 5 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_3`: a constant instant serves for `d` in this interval. -/
theorem piece_3_16 (d : ℝ) (ha : (47 : ℝ) ≤ d) (hb : d ≤ (48 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 3 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(17/56 : ℝ), by norm_num, frozen_intro 3 (17/56 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · exact clear_of_window 14 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** supports: for every free reading `d` in `(3/4, 48]` one of the 16 pieces above serves, so with `small_d` and `tail_3` the frozen set `F_3` and `d` have a common clear instant for every `d > 0`. -/
theorem family_3 (d : ℝ) (hd : 0 < d) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 3 t ∧ (1 / 8 : ℝ) ≤ distInt (d * t) := by
  by_cases h0 : d ≤ 3 / 4
  · exact small_d 3 d hd h0
  by_cases c1 : d ≤ (49/17 : ℝ)
  · exact piece_3_1 d (by linarith) c1
  by_cases c2 : d ≤ (7 : ℝ)
  · exact piece_3_2 d (by linarith) c2
  by_cases c3 : d ≤ (161/17 : ℝ)
  · exact piece_3_3 d (by linarith) c3
  by_cases c4 : d ≤ (15 : ℝ)
  · exact piece_3_4 d (by linarith) c4
  by_cases c5 : d ≤ (282/17 : ℝ)
  · exact piece_3_5 d (by linarith) c5
  by_cases c6 : d ≤ (55/3 : ℝ)
  · exact piece_3_6 d (by linarith) c6
  by_cases c7 : d ≤ (23 : ℝ)
  · exact piece_3_7 d (by linarith) c7
  by_cases c8 : d ≤ (426/17 : ℝ)
  · exact piece_3_8 d (by linarith) c8
  by_cases c9 : d ≤ (31 : ℝ)
  · exact piece_3_9 d (by linarith) c9
  by_cases c10 : d ≤ (553/17 : ℝ)
  · exact piece_3_10 d (by linarith) c10
  by_cases c11 : d ≤ (103/3 : ℝ)
  · exact piece_3_11 d (by linarith) c11
  by_cases c12 : d ≤ (39 : ℝ)
  · exact piece_3_12 d (by linarith) c12
  by_cases c13 : d ≤ (201/5 : ℝ)
  · exact piece_3_13 d (by linarith) c13
  by_cases c14 : d ≤ (721/17 : ℝ)
  · exact piece_3_14 d (by linarith) c14
  by_cases c15 : d ≤ (47 : ℝ)
  · exact piece_3_15 d (by linarith) c15
  by_cases c16 : d ≤ (48 : ℝ)
  · exact piece_3_16 d (by linarith) c16
  exact tail_3 d (by linarith)

/-! ## Family j = 4 : frozen readings [1, 2, 3, 5, 6, 7] -/

theorem tail_4 (d : ℝ) (hd : (70/3 : ℝ) ≤ d) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 4 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  obtain ⟨n, h1, h2⟩ := tail_window (9/40 : ℝ) (15/56 : ℝ) d (by norm_num) hd0 (by nlinarith [hd])
  have hpos : 0 < ((n : ℝ) + 1/8) / d := by positivity
  refine ⟨((n : ℝ) + 1/8) / d, hpos, frozen_intro 4 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_scaled 1 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 1 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 1 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · have e : d * (((n : ℝ) + 1/8) / d) = (n : ℝ) + 1/8 := by field_simp
    rw [e]; exact clear_of_window (n : ℤ) (by push_cast; linarith) (by push_cast; linarith)

/-- **[PROVISIONAL: covering]** one piece of `family_4`: a constant instant serves for `d` in this interval. -/
theorem piece_4_1 (d : ℝ) (ha : (3/4 : ℝ) ≤ d) (hb : d ≤ (35/9 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 4 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(9/40 : ℝ), by norm_num, frozen_intro 4 (9/40 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · exact clear_of_window 0 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_4`: a constant instant serves for `d` in this interval. -/
theorem piece_4_2 (d : ℝ) (ha : (35/9 : ℝ) ≤ d) (hb : d ≤ (7 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 4 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 4 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 0 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_4`: a constant instant serves for `d` in this interval. -/
theorem piece_4_3 (d : ℝ) (ha : (7 : ℝ) ≤ d) (hb : d ≤ (25/3 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 4 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(9/40 : ℝ), by norm_num, frozen_intro 4 (9/40 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · exact clear_of_window 1 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_4`: a constant instant serves for `d` in this interval. -/
theorem piece_4_4 (d : ℝ) (ha : (25/3 : ℝ) ≤ d) (hb : d ≤ (31/3 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 4 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(3/8 : ℝ), by norm_num, frozen_intro 4 (3/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · exact clear_of_window 3 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_4`: a constant instant serves for `d` in this interval. -/
theorem piece_4_5 (d : ℝ) (ha : (31/3 : ℝ) ≤ d) (hb : d ≤ (15 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 4 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 4 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 1 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_4`: a constant instant serves for `d` in this interval. -/
theorem piece_4_6 (d : ℝ) (ha : (15 : ℝ) ≤ d) (hb : d ≤ (155/9 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 4 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(9/40 : ℝ), by norm_num, frozen_intro 4 (9/40 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · exact clear_of_window 3 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_4`: a constant instant serves for `d` in this interval. -/
theorem piece_4_7 (d : ℝ) (ha : (155/9 : ℝ) ≤ d) (hb : d ≤ (23 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 4 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 4 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 2 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_4`: a constant instant serves for `d` in this interval. -/
theorem piece_4_8 (d : ℝ) (ha : (23 : ℝ) ≤ d) (hb : d ≤ (24 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 4 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(9/40 : ℝ), by norm_num, frozen_intro 4 (9/40 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · exact clear_of_window 5 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** supports: for every free reading `d` in `(3/4, 24]` one of the 8 pieces above serves, so with `small_d` and `tail_4` the frozen set `F_4` and `d` have a common clear instant for every `d > 0`. -/
theorem family_4 (d : ℝ) (hd : 0 < d) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 4 t ∧ (1 / 8 : ℝ) ≤ distInt (d * t) := by
  by_cases h0 : d ≤ 3 / 4
  · exact small_d 4 d hd h0
  by_cases c1 : d ≤ (35/9 : ℝ)
  · exact piece_4_1 d (by linarith) c1
  by_cases c2 : d ≤ (7 : ℝ)
  · exact piece_4_2 d (by linarith) c2
  by_cases c3 : d ≤ (25/3 : ℝ)
  · exact piece_4_3 d (by linarith) c3
  by_cases c4 : d ≤ (31/3 : ℝ)
  · exact piece_4_4 d (by linarith) c4
  by_cases c5 : d ≤ (15 : ℝ)
  · exact piece_4_5 d (by linarith) c5
  by_cases c6 : d ≤ (155/9 : ℝ)
  · exact piece_4_6 d (by linarith) c6
  by_cases c7 : d ≤ (23 : ℝ)
  · exact piece_4_7 d (by linarith) c7
  by_cases c8 : d ≤ (24 : ℝ)
  · exact piece_4_8 d (by linarith) c8
  exact tail_4 d (by linarith)

/-! ## Family j = 5 : frozen readings [1, 2, 3, 4, 6, 7] -/

theorem tail_5 (d : ℝ) (hd : (28 : ℝ) ≤ d) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 5 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  obtain ⟨n, h1, h2⟩ := tail_window (3/8 : ℝ) (23/56 : ℝ) d (by norm_num) hd0 (by nlinarith [hd])
  have hpos : 0 < ((n : ℝ) + 1/8) / d := by positivity
  refine ⟨((n : ℝ) + 1/8) / d, hpos, frozen_intro 5 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 1 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 1 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_scaled 2 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 2 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · have e : d * (((n : ℝ) + 1/8) / d) = (n : ℝ) + 1/8 := by field_simp
    rw [e]; exact clear_of_window (n : ℤ) (by push_cast; linarith) (by push_cast; linarith)

/-- **[PROVISIONAL: covering]** one piece of `family_5`: a constant instant serves for `d` in this interval. -/
theorem piece_5_1 (d : ℝ) (ha : (3/4 : ℝ) ≤ d) (hb : d ≤ (14/3 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 5 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(3/16 : ℝ), by norm_num, frozen_intro 5 (3/16 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · exact clear_of_window 0 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_5`: a constant instant serves for `d` in this interval. -/
theorem piece_5_2 (d : ℝ) (ha : (14/3 : ℝ) ≤ d) (hb : d ≤ (7 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 5 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 5 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 0 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_5`: a constant instant serves for `d` in this interval. -/
theorem piece_5_3 (d : ℝ) (ha : (7 : ℝ) ≤ d) (hb : d ≤ (10 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 5 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(3/16 : ℝ), by norm_num, frozen_intro 5 (3/16 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · exact clear_of_window 1 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_5`: a constant instant serves for `d` in this interval. -/
theorem piece_5_4 (d : ℝ) (ha : (10 : ℝ) ≤ d) (hb : d ≤ (15 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 5 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 5 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 1 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_5`: the mover's own opening serves for `d` in this interval. -/
theorem piece_5_5 (d : ℝ) (ha : (15 : ℝ) ≤ d) (hb : d ≤ (50/3 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 5 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  have hd : 0 < d := by linarith
  refine ⟨((3 : ℝ) + 1/8) / d, by positivity, frozen_intro 5 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    have e : (1 : ℝ) * (((3 : ℝ) + 1/8) / d) = ((1 : ℝ) * ((3 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (2 : ℝ) * (((3 : ℝ) + 1/8) / d) = ((2 : ℝ) * ((3 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (3 : ℝ) * (((3 : ℝ) + 1/8) / d) = ((3 : ℝ) * ((3 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (4 : ℝ) * (((3 : ℝ) + 1/8) / d) = ((4 : ℝ) * ((3 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro h; exact absurd rfl h
  · intro _
    have e : (6 : ℝ) * (((3 : ℝ) + 1/8) / d) = ((6 : ℝ) * ((3 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 1 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (7 : ℝ) * (((3 : ℝ) + 1/8) / d) = ((7 : ℝ) * ((3 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 1 (by push_cast; linarith) (by push_cast; linarith)
  · have e : d * (((3 : ℝ) + 1/8) / d) = (3 : ℝ) + 1/8 := by field_simp
    rw [e]; exact clear_of_window 3 (by norm_num) (by norm_num)

/-- **[PROVISIONAL: covering]** one piece of `family_5`: a constant instant serves for `d` in this interval. -/
theorem piece_5_6 (d : ℝ) (ha : (50/3 : ℝ) ≤ d) (hb : d ≤ (62/3 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 5 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(3/16 : ℝ), by norm_num, frozen_intro 5 (3/16 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · exact clear_of_window 3 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_5`: a constant instant serves for `d` in this interval. -/
theorem piece_5_7 (d : ℝ) (ha : (62/3 : ℝ) ≤ d) (hb : d ≤ (23 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 5 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 5 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 2 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_5`: a constant instant serves for `d` in this interval. -/
theorem piece_5_8 (d : ℝ) (ha : (23 : ℝ) ≤ d) (hb : d ≤ (26 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 5 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(3/16 : ℝ), by norm_num, frozen_intro 5 (3/16 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · exact clear_of_window 4 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_5`: a constant instant serves for `d` in this interval. -/
theorem piece_5_9 (d : ℝ) (ha : (26 : ℝ) ≤ d) (hb : d ≤ (28 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 5 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 5 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 3 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** supports: for every free reading `d` in `(3/4, 28]` one of the 9 pieces above serves, so with `small_d` and `tail_5` the frozen set `F_5` and `d` have a common clear instant for every `d > 0`. -/
theorem family_5 (d : ℝ) (hd : 0 < d) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 5 t ∧ (1 / 8 : ℝ) ≤ distInt (d * t) := by
  by_cases h0 : d ≤ 3 / 4
  · exact small_d 5 d hd h0
  by_cases c1 : d ≤ (14/3 : ℝ)
  · exact piece_5_1 d (by linarith) c1
  by_cases c2 : d ≤ (7 : ℝ)
  · exact piece_5_2 d (by linarith) c2
  by_cases c3 : d ≤ (10 : ℝ)
  · exact piece_5_3 d (by linarith) c3
  by_cases c4 : d ≤ (15 : ℝ)
  · exact piece_5_4 d (by linarith) c4
  by_cases c5 : d ≤ (50/3 : ℝ)
  · exact piece_5_5 d (by linarith) c5
  by_cases c6 : d ≤ (62/3 : ℝ)
  · exact piece_5_6 d (by linarith) c6
  by_cases c7 : d ≤ (23 : ℝ)
  · exact piece_5_7 d (by linarith) c7
  by_cases c8 : d ≤ (26 : ℝ)
  · exact piece_5_8 d (by linarith) c8
  by_cases c9 : d ≤ (28 : ℝ)
  · exact piece_5_9 d (by linarith) c9
  exact tail_5 d (by linarith)

/-! ## Family j = 6 : frozen readings [1, 2, 3, 4, 5, 7] -/

theorem tail_6 (d : ℝ) (hd : (70 : ℝ) ≤ d) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  obtain ⟨n, h1, h2⟩ := tail_window (9/56 : ℝ) (7/40 : ℝ) d (by norm_num) hd0 (by nlinarith [hd])
  have hpos : 0 < ((n : ℝ) + 1/8) / d := by positivity
  refine ⟨((n : ℝ) + 1/8) / d, hpos, frozen_intro 6 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_scaled 1 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · have e : d * (((n : ℝ) + 1/8) / d) = (n : ℝ) + 1/8 := by field_simp
    rw [e]; exact clear_of_window (n : ℤ) (by push_cast; linarith) (by push_cast; linarith)

/-- **[PROVISIONAL: covering]** one piece of `family_6`: a constant instant serves for `d` in this interval. -/
theorem piece_6_1 (d : ℝ) (ha : (3/4 : ℝ) ≤ d) (hb : d ≤ (7/3 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(3/8 : ℝ), by norm_num, frozen_intro 6 (3/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · exact clear_of_window 0 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_6`: a constant instant serves for `d` in this interval. -/
theorem piece_6_2 (d : ℝ) (ha : (7/3 : ℝ) ≤ d) (hb : d ≤ (7 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 6 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 0 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_6`: a constant instant serves for `d` in this interval. -/
theorem piece_6_3 (d : ℝ) (ha : (7 : ℝ) ≤ d) (hb : d ≤ (35/3 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(9/56 : ℝ), by norm_num, frozen_intro 6 (9/56 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · exact clear_of_window 1 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_6`: a constant instant serves for `d` in this interval. -/
theorem piece_6_4 (d : ℝ) (ha : (35/3 : ℝ) ≤ d) (hb : d ≤ (15 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 6 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 1 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_6`: a constant instant serves for `d` in this interval. -/
theorem piece_6_5 (d : ℝ) (ha : (15 : ℝ) ≤ d) (hb : d ≤ (161/9 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(9/56 : ℝ), by norm_num, frozen_intro 6 (9/56 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · exact clear_of_window 2 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_6`: a constant instant serves for `d` in this interval. -/
theorem piece_6_6 (d : ℝ) (ha : (161/9 : ℝ) ≤ d) (hb : d ≤ (23 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 6 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 2 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_6`: a constant instant serves for `d` in this interval. -/
theorem piece_6_7 (d : ℝ) (ha : (23 : ℝ) ≤ d) (hb : d ≤ (217/9 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(9/56 : ℝ), by norm_num, frozen_intro 6 (9/56 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · exact clear_of_window 3 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_6`: the mover's own opening serves for `d` in this interval. -/
theorem piece_6_8 (d : ℝ) (ha : (217/9 : ℝ) ≤ d) (hb : d ≤ (77/3 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  have hd : 0 < d := by linarith
  refine ⟨((4 : ℝ) + 1/8) / d, by positivity, frozen_intro 6 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    have e : (1 : ℝ) * (((4 : ℝ) + 1/8) / d) = ((1 : ℝ) * ((4 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (2 : ℝ) * (((4 : ℝ) + 1/8) / d) = ((2 : ℝ) * ((4 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (3 : ℝ) * (((4 : ℝ) + 1/8) / d) = ((3 : ℝ) * ((4 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (4 : ℝ) * (((4 : ℝ) + 1/8) / d) = ((4 : ℝ) * ((4 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (5 : ℝ) * (((4 : ℝ) + 1/8) / d) = ((5 : ℝ) * ((4 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro h; exact absurd rfl h
  · intro _
    have e : (7 : ℝ) * (((4 : ℝ) + 1/8) / d) = ((7 : ℝ) * ((4 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 1 (by push_cast; linarith) (by push_cast; linarith)
  · have e : d * (((4 : ℝ) + 1/8) / d) = (4 : ℝ) + 1/8 := by field_simp
    rw [e]; exact clear_of_window 4 (by norm_num) (by norm_num)

/-- **[PROVISIONAL: covering]** one piece of `family_6`: a constant instant serves for `d` in this interval. -/
theorem piece_6_9 (d : ℝ) (ha : (77/3 : ℝ) ≤ d) (hb : d ≤ (31 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 6 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 3 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_6`: the mover's own opening serves for `d` in this interval. -/
theorem piece_6_10 (d : ℝ) (ha : (31 : ℝ) ≤ d) (hb : d ≤ (287/9 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  have hd : 0 < d := by linarith
  refine ⟨((5 : ℝ) + 1/8) / d, by positivity, frozen_intro 6 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    have e : (1 : ℝ) * (((5 : ℝ) + 1/8) / d) = ((1 : ℝ) * ((5 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (2 : ℝ) * (((5 : ℝ) + 1/8) / d) = ((2 : ℝ) * ((5 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (3 : ℝ) * (((5 : ℝ) + 1/8) / d) = ((3 : ℝ) * ((5 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (4 : ℝ) * (((5 : ℝ) + 1/8) / d) = ((4 : ℝ) * ((5 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (5 : ℝ) * (((5 : ℝ) + 1/8) / d) = ((5 : ℝ) * ((5 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro h; exact absurd rfl h
  · intro _
    have e : (7 : ℝ) * (((5 : ℝ) + 1/8) / d) = ((7 : ℝ) * ((5 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 1 (by push_cast; linarith) (by push_cast; linarith)
  · have e : d * (((5 : ℝ) + 1/8) / d) = (5 : ℝ) + 1/8 := by field_simp
    rw [e]; exact clear_of_window 5 (by norm_num) (by norm_num)

/-- **[PROVISIONAL: covering]** one piece of `family_6`: a constant instant serves for `d` in this interval. -/
theorem piece_6_11 (d : ℝ) (ha : (287/9 : ℝ) ≤ d) (hb : d ≤ (329/9 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(9/56 : ℝ), by norm_num, frozen_intro 6 (9/56 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · exact clear_of_window 5 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_6`: a constant instant serves for `d` in this interval. -/
theorem piece_6_12 (d : ℝ) (ha : (329/9 : ℝ) ≤ d) (hb : d ≤ (39 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 6 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 4 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_6`: a constant instant serves for `d` in this interval. -/
theorem piece_6_13 (d : ℝ) (ha : (39 : ℝ) ≤ d) (hb : d ≤ (385/9 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(9/56 : ℝ), by norm_num, frozen_intro 6 (9/56 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · exact clear_of_window 6 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_6`: a constant instant serves for `d` in this interval. -/
theorem piece_6_14 (d : ℝ) (ha : (385/9 : ℝ) ≤ d) (hb : d ≤ (47 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 6 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 5 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_6`: the mover's own opening serves for `d` in this interval. -/
theorem piece_6_15 (d : ℝ) (ha : (47 : ℝ) ≤ d) (hb : d ≤ (455/9 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  have hd : 0 < d := by linarith
  refine ⟨((8 : ℝ) + 1/8) / d, by positivity, frozen_intro 6 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    have e : (1 : ℝ) * (((8 : ℝ) + 1/8) / d) = ((1 : ℝ) * ((8 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (2 : ℝ) * (((8 : ℝ) + 1/8) / d) = ((2 : ℝ) * ((8 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (3 : ℝ) * (((8 : ℝ) + 1/8) / d) = ((3 : ℝ) * ((8 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (4 : ℝ) * (((8 : ℝ) + 1/8) / d) = ((4 : ℝ) * ((8 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (5 : ℝ) * (((8 : ℝ) + 1/8) / d) = ((5 : ℝ) * ((8 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro h; exact absurd rfl h
  · intro _
    have e : (7 : ℝ) * (((8 : ℝ) + 1/8) / d) = ((7 : ℝ) * ((8 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 1 (by push_cast; linarith) (by push_cast; linarith)
  · have e : d * (((8 : ℝ) + 1/8) / d) = (8 : ℝ) + 1/8 := by field_simp
    rw [e]; exact clear_of_window 8 (by norm_num) (by norm_num)

/-- **[PROVISIONAL: covering]** one piece of `family_6`: a constant instant serves for `d` in this interval. -/
theorem piece_6_16 (d : ℝ) (ha : (455/9 : ℝ) ≤ d) (hb : d ≤ (497/9 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(9/56 : ℝ), by norm_num, frozen_intro 6 (9/56 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · exact clear_of_window 8 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_6`: the mover's own opening serves for `d` in this interval. -/
theorem piece_6_17 (d : ℝ) (ha : (497/9 : ℝ) ≤ d) (hb : d ≤ (511/9 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  have hd : 0 < d := by linarith
  refine ⟨((9 : ℝ) + 1/8) / d, by positivity, frozen_intro 6 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    have e : (1 : ℝ) * (((9 : ℝ) + 1/8) / d) = ((1 : ℝ) * ((9 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (2 : ℝ) * (((9 : ℝ) + 1/8) / d) = ((2 : ℝ) * ((9 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (3 : ℝ) * (((9 : ℝ) + 1/8) / d) = ((3 : ℝ) * ((9 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (4 : ℝ) * (((9 : ℝ) + 1/8) / d) = ((4 : ℝ) * ((9 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (5 : ℝ) * (((9 : ℝ) + 1/8) / d) = ((5 : ℝ) * ((9 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro h; exact absurd rfl h
  · intro _
    have e : (7 : ℝ) * (((9 : ℝ) + 1/8) / d) = ((7 : ℝ) * ((9 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 1 (by push_cast; linarith) (by push_cast; linarith)
  · have e : d * (((9 : ℝ) + 1/8) / d) = (9 : ℝ) + 1/8 := by field_simp
    rw [e]; exact clear_of_window 9 (by norm_num) (by norm_num)

/-- **[PROVISIONAL: covering]** one piece of `family_6`: a constant instant serves for `d` in this interval. -/
theorem piece_6_18 (d : ℝ) (ha : (511/9 : ℝ) ≤ d) (hb : d ≤ (553/9 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(9/56 : ℝ), by norm_num, frozen_intro 6 (9/56 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · exact clear_of_window 9 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_6`: a constant instant serves for `d` in this interval. -/
theorem piece_6_19 (d : ℝ) (ha : (553/9 : ℝ) ≤ d) (hb : d ≤ (63 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 6 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 7 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_6`: a constant instant serves for `d` in this interval. -/
theorem piece_6_20 (d : ℝ) (ha : (63 : ℝ) ≤ d) (hb : d ≤ (203/3 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(9/56 : ℝ), by norm_num, frozen_intro 6 (9/56 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · exact clear_of_window 10 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_6`: a constant instant serves for `d` in this interval. -/
theorem piece_6_21 (d : ℝ) (ha : (203/3 : ℝ) ≤ d) (hb : d ≤ (70 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 6 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · exact clear_of_window 8 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** supports: for every free reading `d` in `(3/4, 70]` one of the 21 pieces above serves, so with `small_d` and `tail_6` the frozen set `F_6` and `d` have a common clear instant for every `d > 0`. -/
theorem family_6 (d : ℝ) (hd : 0 < d) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 6 t ∧ (1 / 8 : ℝ) ≤ distInt (d * t) := by
  by_cases h0 : d ≤ 3 / 4
  · exact small_d 6 d hd h0
  by_cases c1 : d ≤ (7/3 : ℝ)
  · exact piece_6_1 d (by linarith) c1
  by_cases c2 : d ≤ (7 : ℝ)
  · exact piece_6_2 d (by linarith) c2
  by_cases c3 : d ≤ (35/3 : ℝ)
  · exact piece_6_3 d (by linarith) c3
  by_cases c4 : d ≤ (15 : ℝ)
  · exact piece_6_4 d (by linarith) c4
  by_cases c5 : d ≤ (161/9 : ℝ)
  · exact piece_6_5 d (by linarith) c5
  by_cases c6 : d ≤ (23 : ℝ)
  · exact piece_6_6 d (by linarith) c6
  by_cases c7 : d ≤ (217/9 : ℝ)
  · exact piece_6_7 d (by linarith) c7
  by_cases c8 : d ≤ (77/3 : ℝ)
  · exact piece_6_8 d (by linarith) c8
  by_cases c9 : d ≤ (31 : ℝ)
  · exact piece_6_9 d (by linarith) c9
  by_cases c10 : d ≤ (287/9 : ℝ)
  · exact piece_6_10 d (by linarith) c10
  by_cases c11 : d ≤ (329/9 : ℝ)
  · exact piece_6_11 d (by linarith) c11
  by_cases c12 : d ≤ (39 : ℝ)
  · exact piece_6_12 d (by linarith) c12
  by_cases c13 : d ≤ (385/9 : ℝ)
  · exact piece_6_13 d (by linarith) c13
  by_cases c14 : d ≤ (47 : ℝ)
  · exact piece_6_14 d (by linarith) c14
  by_cases c15 : d ≤ (455/9 : ℝ)
  · exact piece_6_15 d (by linarith) c15
  by_cases c16 : d ≤ (497/9 : ℝ)
  · exact piece_6_16 d (by linarith) c16
  by_cases c17 : d ≤ (511/9 : ℝ)
  · exact piece_6_17 d (by linarith) c17
  by_cases c18 : d ≤ (553/9 : ℝ)
  · exact piece_6_18 d (by linarith) c18
  by_cases c19 : d ≤ (63 : ℝ)
  · exact piece_6_19 d (by linarith) c19
  by_cases c20 : d ≤ (203/3 : ℝ)
  · exact piece_6_20 d (by linarith) c20
  by_cases c21 : d ≤ (70 : ℝ)
  · exact piece_6_21 d (by linarith) c21
  exact tail_6 d (by linarith)

/-! ## Family j = 7 : frozen readings [1, 2, 3, 4, 5, 6] -/

theorem tail_7 (d : ℝ) (hd : (48 : ℝ) ≤ d) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 7 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  obtain ⟨n, h1, h2⟩ := tail_window (1/8 : ℝ) (7/48 : ℝ) d (by norm_num) hd0 (by nlinarith [hd])
  have hpos : 0 < ((n : ℝ) + 1/8) / d := by positivity
  refine ⟨((n : ℝ) + 1/8) / d, hpos, frozen_intro 7 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro _
    exact clear_scaled 0 (by norm_num) h1 h2 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · have e : d * (((n : ℝ) + 1/8) / d) = (n : ℝ) + 1/8 := by field_simp
    rw [e]; exact clear_of_window (n : ℤ) (by push_cast; linarith) (by push_cast; linarith)

/-- **[PROVISIONAL: covering]** one piece of `family_7`: a constant instant serves for `d` in this interval. -/
theorem piece_7_1 (d : ℝ) (ha : (3/4 : ℝ) ≤ d) (hb : d ≤ (28/9 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 7 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(9/32 : ℝ), by norm_num, frozen_intro 7 (9/32 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · exact clear_of_window 0 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_7`: a constant instant serves for `d` in this interval. -/
theorem piece_7_2 (d : ℝ) (ha : (28/9 : ℝ) ≤ d) (hb : d ≤ (7 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 7 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 7 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · exact clear_of_window 0 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_7`: a constant instant serves for `d` in this interval. -/
theorem piece_7_3 (d : ℝ) (ha : (7 : ℝ) ≤ d) (hb : d ≤ (55/7 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 7 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(7/8 : ℝ), by norm_num, frozen_intro 7 (7/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 2 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 3 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 4 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 5 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · exact clear_of_window 6 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_7`: a constant instant serves for `d` in this interval. -/
theorem piece_7_4 (d : ℝ) (ha : (55/7 : ℝ) ≤ d) (hb : d ≤ (92/9 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 7 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(9/32 : ℝ), by norm_num, frozen_intro 7 (9/32 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · exact clear_of_window 2 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_7`: a constant instant serves for `d` in this interval. -/
theorem piece_7_5 (d : ℝ) (ha : (92/9 : ℝ) ≤ d) (hb : d ≤ (15 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 7 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 7 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · exact clear_of_window 1 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_7`: a constant instant serves for `d` in this interval. -/
theorem piece_7_6 (d : ℝ) (ha : (15 : ℝ) ≤ d) (hb : d ≤ (52/3 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 7 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(9/32 : ℝ), by norm_num, frozen_intro 7 (9/32 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · exact clear_of_window 4 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_7`: a constant instant serves for `d` in this interval. -/
theorem piece_7_7 (d : ℝ) (ha : (52/3 : ℝ) ≤ d) (hb : d ≤ (23 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 7 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 7 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · exact clear_of_window 2 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_7`: the mover's own opening serves for `d` in this interval. -/
theorem piece_7_8 (d : ℝ) (ha : (23 : ℝ) ≤ d) (hb : d ≤ (25 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 7 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  have hd : 0 < d := by linarith
  refine ⟨((3 : ℝ) + 1/8) / d, by positivity, frozen_intro 7 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    have e : (1 : ℝ) * (((3 : ℝ) + 1/8) / d) = ((1 : ℝ) * ((3 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (2 : ℝ) * (((3 : ℝ) + 1/8) / d) = ((2 : ℝ) * ((3 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (3 : ℝ) * (((3 : ℝ) + 1/8) / d) = ((3 : ℝ) * ((3 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (4 : ℝ) * (((3 : ℝ) + 1/8) / d) = ((4 : ℝ) * ((3 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (5 : ℝ) * (((3 : ℝ) + 1/8) / d) = ((5 : ℝ) * ((3 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (6 : ℝ) * (((3 : ℝ) + 1/8) / d) = ((6 : ℝ) * ((3 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro h; exact absurd rfl h
  · have e : d * (((3 : ℝ) + 1/8) / d) = (3 : ℝ) + 1/8 := by field_simp
    rw [e]; exact clear_of_window 3 (by norm_num) (by norm_num)

/-- **[PROVISIONAL: covering]** one piece of `family_7`: a constant instant serves for `d` in this interval. -/
theorem piece_7_9 (d : ℝ) (ha : (25 : ℝ) ≤ d) (hb : d ≤ (31 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 7 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 7 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · exact clear_of_window 3 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_7`: the mover's own opening serves for `d` in this interval. -/
theorem piece_7_10 (d : ℝ) (ha : (31 : ℝ) ≤ d) (hb : d ≤ (33 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 7 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  have hd : 0 < d := by linarith
  refine ⟨((4 : ℝ) + 1/8) / d, by positivity, frozen_intro 7 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    have e : (1 : ℝ) * (((4 : ℝ) + 1/8) / d) = ((1 : ℝ) * ((4 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (2 : ℝ) * (((4 : ℝ) + 1/8) / d) = ((2 : ℝ) * ((4 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (3 : ℝ) * (((4 : ℝ) + 1/8) / d) = ((3 : ℝ) * ((4 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (4 : ℝ) * (((4 : ℝ) + 1/8) / d) = ((4 : ℝ) * ((4 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (5 : ℝ) * (((4 : ℝ) + 1/8) / d) = ((5 : ℝ) * ((4 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (6 : ℝ) * (((4 : ℝ) + 1/8) / d) = ((6 : ℝ) * ((4 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro h; exact absurd rfl h
  · have e : d * (((4 : ℝ) + 1/8) / d) = (4 : ℝ) + 1/8 := by field_simp
    rw [e]; exact clear_of_window 4 (by norm_num) (by norm_num)

/-- **[PROVISIONAL: covering]** one piece of `family_7`: a constant instant serves for `d` in this interval. -/
theorem piece_7_11 (d : ℝ) (ha : (33 : ℝ) ≤ d) (hb : d ≤ (39 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 7 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 7 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · exact clear_of_window 4 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_7`: the mover's own opening serves for `d` in this interval. -/
theorem piece_7_12 (d : ℝ) (ha : (39 : ℝ) ≤ d) (hb : d ≤ (41 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 7 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  have hd : 0 < d := by linarith
  refine ⟨((5 : ℝ) + 1/8) / d, by positivity, frozen_intro 7 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    have e : (1 : ℝ) * (((5 : ℝ) + 1/8) / d) = ((1 : ℝ) * ((5 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (2 : ℝ) * (((5 : ℝ) + 1/8) / d) = ((2 : ℝ) * ((5 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (3 : ℝ) * (((5 : ℝ) + 1/8) / d) = ((3 : ℝ) * ((5 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (4 : ℝ) * (((5 : ℝ) + 1/8) / d) = ((4 : ℝ) * ((5 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (5 : ℝ) * (((5 : ℝ) + 1/8) / d) = ((5 : ℝ) * ((5 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro _
    have e : (6 : ℝ) * (((5 : ℝ) + 1/8) / d) = ((6 : ℝ) * ((5 : ℝ) + 1/8)) / d := by ring
    rw [e]
    exact clear_div hd 0 (by push_cast; linarith) (by push_cast; linarith)
  · intro h; exact absurd rfl h
  · have e : d * (((5 : ℝ) + 1/8) / d) = (5 : ℝ) + 1/8 := by field_simp
    rw [e]; exact clear_of_window 5 (by norm_num) (by norm_num)

/-- **[PROVISIONAL: covering]** one piece of `family_7`: a constant instant serves for `d` in this interval. -/
theorem piece_7_13 (d : ℝ) (ha : (41 : ℝ) ≤ d) (hb : d ≤ (47 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 7 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(1/8 : ℝ), by norm_num, frozen_intro 7 (1/8 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · exact clear_of_window 5 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** one piece of `family_7`: a constant instant serves for `d` in this interval. -/
theorem piece_7_14 (d : ℝ) (ha : (47 : ℝ) ≤ d) (hb : d ≤ (48 : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 7 t ∧ (1/8 : ℝ) ≤ distInt (d * t) := by
  refine ⟨(9/32 : ℝ), by norm_num, frozen_intro 7 (9/32 : ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 0 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro _
    exact clear_of_window 1 (by norm_num) (by norm_num)
  · intro h; exact absurd rfl h
  · exact clear_of_window 13 (by nlinarith [ha]) (by nlinarith [hb])

/-- **[PROVISIONAL: covering]** supports: for every free reading `d` in `(3/4, 48]` one of the 14 pieces above serves, so with `small_d` and `tail_7` the frozen set `F_7` and `d` have a common clear instant for every `d > 0`. -/
theorem family_7 (d : ℝ) (hd : 0 < d) :
    ∃ t : ℝ, 0 < t ∧ FrozenClear 7 t ∧ (1 / 8 : ℝ) ≤ distInt (d * t) := by
  by_cases h0 : d ≤ 3 / 4
  · exact small_d 7 d hd h0
  by_cases c1 : d ≤ (28/9 : ℝ)
  · exact piece_7_1 d (by linarith) c1
  by_cases c2 : d ≤ (7 : ℝ)
  · exact piece_7_2 d (by linarith) c2
  by_cases c3 : d ≤ (55/7 : ℝ)
  · exact piece_7_3 d (by linarith) c3
  by_cases c4 : d ≤ (92/9 : ℝ)
  · exact piece_7_4 d (by linarith) c4
  by_cases c5 : d ≤ (15 : ℝ)
  · exact piece_7_5 d (by linarith) c5
  by_cases c6 : d ≤ (52/3 : ℝ)
  · exact piece_7_6 d (by linarith) c6
  by_cases c7 : d ≤ (23 : ℝ)
  · exact piece_7_7 d (by linarith) c7
  by_cases c8 : d ≤ (25 : ℝ)
  · exact piece_7_8 d (by linarith) c8
  by_cases c9 : d ≤ (31 : ℝ)
  · exact piece_7_9 d (by linarith) c9
  by_cases c10 : d ≤ (33 : ℝ)
  · exact piece_7_10 d (by linarith) c10
  by_cases c11 : d ≤ (39 : ℝ)
  · exact piece_7_11 d (by linarith) c11
  by_cases c12 : d ≤ (41 : ℝ)
  · exact piece_7_12 d (by linarith) c12
  by_cases c13 : d ≤ (47 : ℝ)
  · exact piece_7_13 d (by linarith) c13
  by_cases c14 : d ≤ (48 : ℝ)
  · exact piece_7_14 d (by linarith) c14
  exact tail_7 d (by linarith)

#print axioms family_1
#print axioms family_2
#print axioms family_3
#print axioms family_4
#print axioms family_5
#print axioms family_6
#print axioms family_7
#print axioms small_d
#print axioms tail_window

end Fresh.OneMover
