import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Localisation
import Fresh.LonelyCells

/-!
# The carving calculus (Task S; v9 section 7: `K₁ = [1, 7]`, `K_k = K_{k−1}` minus the zones of reading `k`, L2)

Written 2026-10-08 (two sessions; the second fixed `cells_ordered` and `apPrefix_succ` and added
`ap_first_cell_leftmost`).  Imports `Mathlib` and the Fresh modules `Framework`, `Cascade`, `Localisation`, `LonelyCells`;
nothing from the existing `LonelyRunner` repo.  Exact reals only; every disparity is positive (no runner is
stationary); every statement is symbolic, for every finite set `ds` of positive disparities and every `d > 0`.

This file describes what adding ONE runner `d` does to the lonely set of `ds` and to each of its cells.  It does not
argue that a lonely instant or a cell exists, and it bounds nothing: no number of cells, moves or laps appears in any
statement.  Every statement takes a given cell and says what carving does to it.

Objects.  `clearSet d = {t | 1/8 ≤ ‖d t‖}`; the window of lap `N` is `[winLo d N, winHi d N] = [(N + 1/8)/d,
(N + 7/8)/d]`; the zone of lap `N` is the open interval `zone d N = ((N − 1/8)/d, (N + 1/8)/d)`.

Results (grades in the docstrings; every [L] has its `#print axioms` line below it).
* (1) `lonelySet_insert`, `lonelySet_eq_iInter`, `clearSet_eq_iUnion`, `notMem_clearSet_iff`, `zone_succ_eq`,
  `window_length`, `zone_width`, `zone_disjoint_clearSet`.
* (2) `inter_clearSet_eq` (the carving of `[u, w]` is the union of the pieces `[max u lo_N, min w hi_N]`),
  `inter_clearSet_eq_finite` (only the `N` in an explicit integer interval contribute; `[PROVISIONAL: counting tool]`),
  (a) `killed_iff`, `cell_killed_iff`; (b) `survives_of_wide`, `cell_survives_of_wide` (`[PROVISIONAL: covering]`);
  (c) `cell_insert_is_piece`, `piece_isCell`, `isCell_insert_iff`, `cell_insert_ends`.
* (3) `lonelySet_induction`, `lonelySet_toFinset_eq_foldl`, `cellSet_insert`, `window_isCell`, `cell_singleton_iff`.
* (4) L2: `cells_ordered`, `cell_gap` (holds for EVERY `ds`), `zone_meets_at_most_one_cell` (`[PROVISIONAL: covering]`,
  hypothesis: the added `d` is at least every element of `ds`), and the exception `L2_fails_without_order`
  (`ds = {8}`, `d = 1`).
* (6) The AP touch produced by carving: `ap_first_cell_carving` (`[1/8, 7/(8k)]` is a cell of `{1, …, k}` for
  `1 ≤ k ≤ 7`, obtained from the cell of `{1, …, k − 1}` by `piece_isCell`), `ap_first_cell_leftmost` (every cell of
  `{1, …, k}` starts at or after `1/8`, so that cell is the first one) and `ap_touch_by_carving` (at `k = 7` it is the touch `[1/8, 1/8]`, agreeing with
  `LonelyCells.ap_first_cell_is_touch`).

Provenance.  The carving is the record's boundary set method (v9 §1, P§2.1) and its gate-lemma form K_k (v9 §7, GL).
No Lean declaration in the existing `LRC/` tree was found for carving a cell by one runner; every proof below was
written for this file and none was copied.  The cell ends used are `LonelyCells.cell_left_end_is_opening` /
`cell_right_end_is_entry`; the window facts are `Localisation.clear_of_window`, `clear_iff_fract`.
-/

open Classical

namespace Fresh.Carving

open Fresh Fresh.LonelyCells

/-! ## Objects -/

/-- The instants at which runner `d` is clear (at circle distance at least `1/8`). -/
def clearSet (d : ℝ) : Set ℝ := {t | (1 / 8 : ℝ) ≤ distInt (d * t)}

/-- Left end of the window of lap `N`: the opening `(N + 1/8)/d`. -/
noncomputable def winLo (d : ℝ) (N : ℤ) : ℝ := ((N : ℝ) + 1 / 8) / d

/-- Right end of the window of lap `N`: the entry `(N + 7/8)/d`. -/
noncomputable def winHi (d : ℝ) (N : ℤ) : ℝ := ((N : ℝ) + 7 / 8) / d

/-- The open zone of lap `N`: `((N − 1/8)/d, (N + 1/8)/d)`, where `d` is in the way. -/
noncomputable def zone (d : ℝ) (N : ℤ) : Set ℝ := Set.Ioo (((N : ℝ) - 1 / 8) / d) (((N : ℝ) + 1 / 8) / d)

theorem mem_window_iff {d t : ℝ} (hd : 0 < d) (N : ℤ) :
    t ∈ Set.Icc (winLo d N) (winHi d N) ↔ (N : ℝ) + 1 / 8 ≤ d * t ∧ d * t ≤ (N : ℝ) + 7 / 8 := by
  unfold winLo winHi
  rw [Set.mem_Icc, div_le_iff₀ hd, le_div_iff₀ hd, mul_comm t d]

#print axioms mem_window_iff

theorem mem_zone_iff {d t : ℝ} (hd : 0 < d) (N : ℤ) :
    t ∈ zone d N ↔ (N : ℝ) - 1 / 8 < d * t ∧ d * t < (N : ℝ) + 1 / 8 := by
  unfold zone
  rw [Set.mem_Ioo, div_lt_iff₀ hd, lt_div_iff₀ hd, mul_comm t d]

#print axioms mem_zone_iff

theorem mul_winLo {d : ℝ} (hd : 0 < d) (N : ℤ) : d * winLo d N = (N : ℝ) + 1 / 8 := by
  unfold winLo; field_simp

#print axioms mul_winLo

theorem mul_winHi {d : ℝ} (hd : 0 < d) (N : ℤ) : d * winHi d N = (N : ℝ) + 7 / 8 := by
  unfold winHi; field_simp

#print axioms mul_winHi

/-! ## (1) Adding one runner intersects with its clear set -/

/-- **(1) `lonelySet_insert`** [L]: adding the runner `d` to `ds` intersects the lonely set with `clearSet d`. -/
theorem lonelySet_insert (d : ℝ) (ds : Finset ℝ) :
    lonelySet (insert d ds) = lonelySet ds ∩ clearSet d := by
  ext t
  simp only [lonelySet, Cascade.LonelyAt, clearSet, Set.mem_inter_iff, Set.mem_setOf_eq,
    Finset.forall_mem_insert]
  exact and_comm

#print axioms lonelySet_insert

theorem lonelySet_singleton (d : ℝ) : lonelySet {d} = clearSet d := by
  rw [← insert_empty_eq d, lonelySet_insert, lonelySet_empty, Set.univ_inter]

#print axioms lonelySet_singleton

/-- The lonely set is the intersection of the clear sets of its runners [L]. -/
theorem lonelySet_eq_iInter (ds : Finset ℝ) : lonelySet ds = ⋂ d ∈ ds, clearSet d := by
  ext t
  simp [lonelySet, Cascade.LonelyAt, clearSet]

#print axioms lonelySet_eq_iInter

/-- **(1) The clear set is the union of the closed windows** [L]: `clearSet d = ⋃_N [(N + 1/8)/d, (N + 7/8)/d]`. -/
theorem clearSet_eq_iUnion {d : ℝ} (hd : 0 < d) :
    clearSet d = ⋃ N : ℤ, Set.Icc (winLo d N) (winHi d N) := by
  ext t
  simp only [Set.mem_iUnion]
  constructor
  · intro h
    have hf := (Localisation.clear_iff_fract (d * t)).mp h
    unfold Int.fract at hf
    exact ⟨⌊d * t⌋, (mem_window_iff hd _).mpr ⟨by linarith [hf.1], by linarith [hf.2]⟩⟩
  · rintro ⟨N, hN⟩
    have := (mem_window_iff hd N).mp hN
    exact Localisation.clear_of_window N this.1 this.2

#print axioms clearSet_eq_iUnion

/-- **(1) The complement of the clear set is the union of the open zones** [L]: `t` is not clear for `d` iff `t` lies
in some zone `((N − 1/8)/d, (N + 1/8)/d)`. -/
theorem notMem_clearSet_iff {d t : ℝ} (hd : 0 < d) : t ∉ clearSet d ↔ ∃ N : ℤ, t ∈ zone d N := by
  constructor
  · intro h
    have h' : distInt (d * t) < 1 / 8 := lt_of_not_ge h
    unfold distInt at h'
    rw [abs_lt] at h'
    exact ⟨round (d * t), (mem_zone_iff hd _).mpr ⟨by linarith [h'.1], by linarith [h'.2]⟩⟩
  · rintro ⟨N, hN⟩ hc
    have hz := (mem_zone_iff hd N).mp hN
    have hw : InWay d t := inWay_of_near N (by rw [abs_lt]; constructor <;> linarith [hz.1, hz.2])
    exact Cascade.not_inWay_iff.mpr hc hw

#print axioms notMem_clearSet_iff

/-- **(1) Consecutive windows are separated by exactly one open zone** [L]: the zone of lap `N + 1` is the open
interval `(winHi d N, winLo d (N + 1))` between the window of lap `N` and that of lap `N + 1`. -/
theorem zone_succ_eq (d : ℝ) (N : ℤ) : zone d (N + 1) = Set.Ioo (winHi d N) (winLo d (N + 1)) := by
  unfold zone winHi winLo
  congr 2
  push_cast; ring

#print axioms zone_succ_eq

/-- **(1) Every window has length `3/(4d)`** [L]. -/
theorem window_length {d : ℝ} (hd : 0 < d) (N : ℤ) : winHi d N - winLo d N = 3 / (4 * d) := by
  unfold winHi winLo; field_simp; ring

#print axioms window_length

/-- **(1) Every zone has width `1/(4d)`** [L]: `winLo d (N + 1) − winHi d N = 1/(4d)`. -/
theorem zone_width {d : ℝ} (hd : 0 < d) (N : ℤ) : winLo d (N + 1) - winHi d N = 1 / (4 * d) := by
  unfold winHi winLo; field_simp; push_cast; ring

#print axioms zone_width

/-- The zone is the open interval of width `1/(4d)` around the lap line `N/d`. -/
theorem zone_width' {d : ℝ} (hd : 0 < d) (N : ℤ) :
    ((N : ℝ) + 1 / 8) / d - ((N : ℝ) - 1 / 8) / d = 1 / (4 * d) := by
  field_simp; ring

#print axioms zone_width'

/-- **(1) No point of a zone is clear** [L]. -/
theorem zone_disjoint_clearSet {d : ℝ} (hd : 0 < d) (N : ℤ) : Disjoint (zone d N) (clearSet d) :=
  Set.disjoint_left.mpr fun _ ht => (notMem_clearSet_iff hd).mpr ⟨N, ht⟩

#print axioms zone_disjoint_clearSet

/-! ## (2) Carving one interval (in particular one cell) by one runner -/

/-- **(2) The carving of `[u, w]` by `d`** [L]: what survives is the union over laps `N` of the closed pieces
`[max u lo_N, min w hi_N]` (empty when `max u lo_N > min w hi_N`). -/
theorem inter_clearSet_eq {d : ℝ} (hd : 0 < d) (u w : ℝ) :
    Set.Icc u w ∩ clearSet d = ⋃ N : ℤ, Set.Icc (max u (winLo d N)) (min w (winHi d N)) := by
  rw [clearSet_eq_iUnion hd, Set.inter_iUnion]
  refine Set.iUnion_congr fun N => ?_
  ext s
  simp only [Set.mem_inter_iff, Set.mem_Icc, max_le_iff, le_min_iff]
  tauto

#print axioms inter_clearSet_eq

/-- A piece is nonempty only for laps `N` with `⌈d u − 7/8⌉ ≤ N ≤ ⌊d w − 1/8⌋`. -/
theorem lap_bounds_of_piece {d u w : ℝ} (hd : 0 < d) {N : ℤ}
    (h : max u (winLo d N) ≤ min w (winHi d N)) : N ∈ Finset.Icc ⌈d * u - 7 / 8⌉ ⌊d * w - 1 / 8⌋ := by
  have h1 : winLo d N ≤ w := le_trans (le_max_right _ _) (le_trans h (min_le_left _ _))
  have h2 : u ≤ winHi d N := le_trans (le_max_left _ _) (le_trans h (min_le_right _ _))
  have e1 := mul_le_mul_of_nonneg_left h1 hd.le
  have e2 := mul_le_mul_of_nonneg_left h2 hd.le
  rw [mul_winLo hd] at e1
  rw [mul_winHi hd] at e2
  rw [Finset.mem_Icc]
  constructor
  · rw [Int.ceil_le]; linarith
  · rw [Int.le_floor]; linarith

#print axioms lap_bounds_of_piece

/-- **(2) Only finitely many laps contribute** [L]: the union of (2) may be taken over the integers `N` in the explicit
interval `[⌈d u − 7/8⌉, ⌊d w − 1/8⌋]`.
[PROVISIONAL: counting tool] restricting the union to a `Finset` of laps supports the claim "the carving of a bounded
interval by one runner is a finite union of closed pieces".  Nothing is counted in the statement. -/
theorem inter_clearSet_eq_finite {d : ℝ} (hd : 0 < d) (u w : ℝ) :
    Set.Icc u w ∩ clearSet d =
      ⋃ N ∈ Finset.Icc ⌈d * u - 7 / 8⌉ ⌊d * w - 1 / 8⌋, Set.Icc (max u (winLo d N)) (min w (winHi d N)) := by
  rw [inter_clearSet_eq hd]
  ext s
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨N, hN⟩
    -- [PROVISIONAL: counting tool] supporting "a bounded interval is carved into a finite union of pieces".
    exact ⟨N, lap_bounds_of_piece hd (le_trans hN.1 hN.2), hN⟩
  · rintro ⟨N, -, hN⟩
    exact ⟨N, hN⟩

#print axioms inter_clearSet_eq_finite

/-- **(2a) `killed_iff`** [L]: for `u ≤ w`, no point of `[u, w]` is clear for `d` iff `[u, w]` lies inside one open
zone of `d`: `(N − 1/8)/d < u` and `w < (N + 1/8)/d` for some lap `N`.  (If `u` lies in the zone of lap `N` and `w`
reached `(N + 1/8)/d`, that opening would be a clear point of `[u, w]`.) -/
theorem killed_iff {d u w : ℝ} (hd : 0 < d) (huw : u ≤ w) :
    (∀ s ∈ Set.Icc u w, s ∉ clearSet d) ↔ ∃ N : ℤ, ((N : ℝ) - 1 / 8) / d < u ∧ w < ((N : ℝ) + 1 / 8) / d := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := (notMem_clearSet_iff hd).mp (h u ⟨le_rfl, huw⟩)
    refine ⟨N, hN.1, ?_⟩
    by_contra hc
    push Not at hc
    apply h (((N : ℝ) + 1 / 8) / d) ⟨hN.2.le, hc⟩
    have e : d * (((N : ℝ) + 1 / 8) / d) = (N : ℝ) + 1 / 8 := by field_simp
    show (1 / 8 : ℝ) ≤ distInt (d * (((N : ℝ) + 1 / 8) / d))
    rw [e]
    exact Localisation.clear_of_window N le_rfl (by linarith)
  · rintro ⟨N, h1, h2⟩ s hs
    exact (notMem_clearSet_iff hd).mpr ⟨N, h1.trans_le hs.1, lt_of_le_of_lt hs.2 h2⟩

#print axioms killed_iff

/-- **(2a) `cell_killed_iff`** [L]: a cell `[u, w]` of `ds` is wholly removed by adding `d` (no point of it is lonely
for `insert d ds`) iff it lies inside one open zone of `d`. -/
theorem cell_killed_iff {ds : Finset ℝ} {d u w : ℝ} (hd : 0 < d) (h : IsCell ds u w) :
    (∀ s ∈ Set.Icc u w, s ∉ lonelySet (insert d ds)) ↔
      ∃ N : ℤ, ((N : ℝ) - 1 / 8) / d < u ∧ w < ((N : ℝ) + 1 / 8) / d := by
  rw [← killed_iff hd h.2.1]
  refine forall₂_congr fun s hs => ?_
  rw [lonelySet_insert]
  exact ⟨fun h1 h2 => h1 ⟨h.2.2.1 hs, h2⟩, fun h1 h2 => h1 h2.2⟩

#print axioms cell_killed_iff

/-- **(2b) `survives_of_wide`** [L] [PROVISIONAL: covering]: if `w − u ≥ 1/(4d)` then `[u, w]` contains a point clear
for `d`.  A window-against-zone statement (an interval at least as wide as a zone is not inside one zone); it supports
the claim "a wide cell is not wholly carved away by one added runner".  It is a tool of the carving calculus, not an
existence result: the interval is given. -/
theorem survives_of_wide {d u w : ℝ} (hd : 0 < d) (hw : 1 / (4 * d) ≤ w - u) :
    ∃ s ∈ Set.Icc u w, s ∈ clearSet d := by
  have hq : 0 < 1 / (4 * d) := by positivity
  have huw : u ≤ w := by linarith
  by_contra hc
  push Not at hc
  -- [PROVISIONAL: covering] supporting "a wide cell is not wholly carved away by one added runner":
  -- the interval would lie in one zone, whose width is exactly `1/(4d)`.
  obtain ⟨N, h1, h2⟩ := (killed_iff hd huw).mp hc
  have := zone_width' hd N
  linarith

#print axioms survives_of_wide

/-- **(2b) `cell_survives_of_wide`** [L] [PROVISIONAL: covering] (supports "a wide cell is not wholly carved away by one
added runner"; a tool, not an existence result): a cell of `ds` of width at least `1/(4d)` keeps a point lonely for
`insert d ds`. -/
theorem cell_survives_of_wide {ds : Finset ℝ} {d u w : ℝ} (hd : 0 < d) (h : IsCell ds u w)
    (hw : 1 / (4 * d) ≤ w - u) : ∃ s ∈ Set.Icc u w, s ∈ lonelySet (insert d ds) := by
  -- [PROVISIONAL: covering] supporting "a wide cell is not wholly carved away by one added runner".
  obtain ⟨s, hs, hc⟩ := survives_of_wide hd hw
  exact ⟨s, hs, by rw [lonelySet_insert]; exact ⟨h.2.2.1 hs, hc⟩⟩

#print axioms cell_survives_of_wide

/-! ## (2c) The cells of `insert d ds` are exactly the nonempty pieces of the cells of `ds` -/

/-- A piece of a cell of `ds` is lonely for `insert d ds`. -/
theorem piece_subset {ds : Finset ℝ} {d u w : ℝ} (hd : 0 < d) (h : IsCell ds u w) (N : ℤ) :
    Set.Icc (max u (winLo d N)) (min w (winHi d N)) ⊆ lonelySet (insert d ds) := by
  intro s hs
  rw [lonelySet_insert]
  refine ⟨h.2.2.1 ⟨le_trans (le_max_left _ _) hs.1, le_trans hs.2 (min_le_left _ _)⟩, ?_⟩
  rw [clearSet_eq_iUnion hd]
  exact Set.mem_iUnion.mpr ⟨N, le_trans (le_max_right _ _) hs.1, le_trans hs.2 (min_le_right _ _)⟩

#print axioms piece_subset

/-- **(2c) `cell_insert_is_piece`** [L]: every cell `[u', w']` of `insert d ds` (`ds` nonempty) is
`[max u lo_N, min w hi_N]` for one cell `[u, w]` of `ds` and one lap `N` of `d`; in particular it lies in that cell. -/
theorem cell_insert_is_piece {ds : Finset ℝ} (hpos : ∀ e ∈ ds, 0 < e) (hne : ds.Nonempty) {d u' w' : ℝ}
    (hd : 0 < d) (h : IsCell (insert d ds) u' w') :
    ∃ u w : ℝ, ∃ N : ℤ, IsCell ds u w ∧ u' = max u (winLo d N) ∧ w' = min w (winHi d N) := by
  have hl : Set.Icc u' w' ⊆ lonelySet ds ∩ clearSet d := by
    rw [← lonelySet_insert]; exact h.2.2.1
  have hu'l : u' ∈ lonelySet ds := (hl ⟨le_rfl, h.2.1⟩).1
  obtain ⟨x, -, y, -, hc, hT, hS⟩ := cell_of_lonely hpos hne h.1 hu'l
  set U := Localisation.lastOpening x u'
  set W := nextEntry y u'
  -- the new cell does not pass the right end of the old one
  have hw'W : w' ≤ W := by
    by_contra hcon
    push Not at hcon
    apply hc.2.2.2.2 w' hcon
    intro s hs
    rcases le_or_gt s W with h1 | h1
    · exact hc.2.2.1 ⟨hs.1, h1⟩
    · exact (hl ⟨le_trans hS h1.le, hs.2⟩).1
  -- the lap of `d` at `u'`
  set N := ⌊d * u'⌋ with hNdef
  have hf := (Localisation.clear_iff_fract (d * u')).mp (hl ⟨le_rfl, h.2.1⟩).2
  unfold Int.fract at hf
  have hlo : winLo d N ≤ u' := ((mem_window_iff hd N).mpr ⟨by linarith [hf.1], by linarith [hf.2]⟩).1
  have hhi : u' ≤ winHi d N := ((mem_window_iff hd N).mpr ⟨by linarith [hf.1], by linarith [hf.2]⟩).2
  -- the new cell does not pass the entry of `d` that ends lap `N`'s window
  have hw'hi : w' ≤ winHi d N := by
    by_contra hcon
    push Not at hcon
    set s := min w' (winHi d N + 1 / (8 * d)) with hsdef
    have hq : 0 < 1 / (8 * d) := by positivity
    have hq' : 1 / (8 * d) < 1 / (4 * d) := by
      apply one_div_lt_one_div_of_lt (by positivity); linarith
    have hs1 : winHi d N < s := lt_min hcon (by linarith)
    have hs2 : s < winHi d N + 1 / (4 * d) := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hw := inWay_after_entry hd (mul_winHi hd N) hs1 hs2
    exact Cascade.not_inWay_iff.mpr (hl ⟨le_trans hhi hs1.le, min_le_left _ _⟩).2 hw
  have hmax : max U (winLo d N) ≤ u' := max_le hT hlo
  have hmin : w' ≤ min W (winHi d N) := le_min hw'W hw'hi
  have hpiece := piece_subset hd hc N
  refine ⟨U, W, N, hc, ?_, ?_⟩
  · by_contra hne'
    have hlt : max U (winLo d N) < u' := lt_of_le_of_ne hmax (Ne.symm hne')
    exact h.2.2.2.1 _ hlt fun s hs => hpiece ⟨hs.1, le_trans hs.2 hmin⟩
  · by_contra hne'
    have hlt : w' < min W (winHi d N) := lt_of_le_of_ne hmin hne'
    exact h.2.2.2.2 _ hlt fun s hs => hpiece ⟨le_trans hmax hs.1, hs.2⟩

#print axioms cell_insert_is_piece

/-- **(2c) `piece_isCell`** [L]: conversely, every nonempty piece `[max u lo_N, min w hi_N]` of a cell `[u, w]` of
`ds` is a cell of `insert d ds`.  Its left end is either the old left end or the opening `lo_N` of `d` (just before
which `d` is in the way); its right end is either the old right end or the entry `hi_N` of `d`. -/
theorem piece_isCell {ds : Finset ℝ} {d u w : ℝ} (hd : 0 < d) (h : IsCell ds u w) {N : ℤ}
    (hne : max u (winLo d N) ≤ min w (winHi d N)) :
    IsCell (insert d ds) (max u (winLo d N)) (min w (winHi d N)) := by
  have hsub := piece_subset hd h N
  have hds : lonelySet (insert d ds) ⊆ lonelySet ds := by
    rw [lonelySet_insert]; exact Set.inter_subset_left
  have hq : 0 < 1 / (8 * d) := by positivity
  have hq' : 1 / (8 * d) < 1 / (4 * d) := by
    apply one_div_lt_one_div_of_lt (by positivity); linarith
  refine ⟨lt_of_lt_of_le h.1 (le_max_left _ _), hne, hsub, ?_, ?_⟩
  · intro u'' hu'' hs''
    rcases le_total (winLo d N) u with h1 | h1
    · -- the left end is the old left end `u`
      rw [max_eq_left h1] at hu'' hne
      apply h.2.2.2.1 u'' hu''
      intro s hs
      rcases le_or_gt s (min w (winHi d N)) with h2 | h2
      · exact hds (hs'' ⟨hs.1, h2⟩)
      · exact h.2.2.1 ⟨le_trans hne h2.le, hs.2⟩
    · -- the left end is the opening `lo_N` of `d`
      rw [max_eq_right h1] at hu'' hne
      set s := max u'' (winLo d N - 1 / (8 * d))
      have hs1 : winLo d N - 1 / (4 * d) < s := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      have hs2 : s < winLo d N := max_lt hu'' (by linarith)
      have hw := inWay_before_opening hd (mul_winLo hd N) hs1 hs2
      have hl := hs'' ⟨le_max_left _ _, le_trans hs2.le hne⟩
      rw [lonelySet_insert] at hl
      exact Cascade.not_inWay_iff.mpr hl.2 hw
  · intro w'' hw'' hs''
    rcases le_total w (winHi d N) with h1 | h1
    · -- the right end is the old right end `w`
      rw [min_eq_left h1] at hw'' hne
      apply h.2.2.2.2 w'' hw''
      intro s hs
      rcases le_or_gt (max u (winLo d N)) s with h2 | h2
      · exact hds (hs'' ⟨h2, hs.2⟩)
      · exact h.2.2.1 ⟨hs.1, le_trans h2.le hne⟩
    · -- the right end is the entry `hi_N` of `d`
      rw [min_eq_right h1] at hw'' hne
      set s := min w'' (winHi d N + 1 / (8 * d))
      have hs1 : winHi d N < s := lt_min hw'' (by linarith)
      have hs2 : s < winHi d N + 1 / (4 * d) := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hw := inWay_after_entry hd (mul_winHi hd N) hs1 hs2
      have hl := hs'' ⟨le_trans hne hs1.le, min_le_left _ _⟩
      rw [lonelySet_insert] at hl
      exact Cascade.not_inWay_iff.mpr hl.2 hw

#print axioms piece_isCell

/-- **(2c) `isCell_insert_iff`** [L]: the cells of `insert d ds` are exactly the nonempty pieces
`[max u lo_N, min w hi_N]` of the cells `[u, w]` of `ds` (`ds` nonempty, all positive, `d > 0`). -/
theorem isCell_insert_iff {ds : Finset ℝ} (hpos : ∀ e ∈ ds, 0 < e) (hne : ds.Nonempty) {d u' w' : ℝ}
    (hd : 0 < d) :
    IsCell (insert d ds) u' w' ↔
      ∃ u w : ℝ, ∃ N : ℤ, IsCell ds u w ∧ max u (winLo d N) ≤ min w (winHi d N) ∧
        u' = max u (winLo d N) ∧ w' = min w (winHi d N) := by
  constructor
  · intro h
    obtain ⟨u, w, N, hc, h1, h2⟩ := cell_insert_is_piece hpos hne hd h
    exact ⟨u, w, N, hc, h1 ▸ h2 ▸ h.2.1, h1, h2⟩
  · rintro ⟨u, w, N, hc, hle, rfl, rfl⟩
    exact piece_isCell hd hc hle

#print axioms isCell_insert_iff

/-- **(2c) `cell_insert_ends`** [L]: a cell `[u', w']` of `insert d ds` lies in a cell `[u, w]` of `ds`; its left end is
the old left end or an opening of `d` (`d u' = N + 1/8`), its right end the old right end or an entry of `d`
(`d w' = N + 7/8`).  Consistent with `cell_left_end_is_opening` / `cell_right_end_is_entry`: an old end is an opening
(entry) of a runner of `ds`. -/
theorem cell_insert_ends {ds : Finset ℝ} (hpos : ∀ e ∈ ds, 0 < e) (hne : ds.Nonempty) {d u' w' : ℝ}
    (hd : 0 < d) (h : IsCell (insert d ds) u' w') :
    ∃ u w : ℝ, ∃ N : ℤ, IsCell ds u w ∧ Set.Icc u' w' ⊆ Set.Icc u w ∧
      (u' = u ∨ d * u' = (N : ℝ) + 1 / 8) ∧ (w' = w ∨ d * w' = (N : ℝ) + 7 / 8) := by
  obtain ⟨u, w, N, hc, h1, h2⟩ := cell_insert_is_piece hpos hne hd h
  refine ⟨u, w, N, hc, ?_, ?_, ?_⟩
  · intro s hs
    exact ⟨le_trans (h1 ▸ le_max_left _ _) hs.1, le_trans hs.2 (h2 ▸ min_le_left _ _)⟩
  · rcases max_choice u (winLo d N) with e | e <;> rw [e] at h1
    · exact Or.inl h1
    · exact Or.inr (by rw [h1]; exact mul_winLo hd N)
  · rcases min_choice w (winHi d N) with e | e <;> rw [e] at h2
    · exact Or.inl h2
    · exact Or.inr (by rw [h2]; exact mul_winHi hd N)

#print axioms cell_insert_ends

/-! ## (3) The recursion -/

/-- **(3) `lonelySet_induction`** [L]: an induction principle on `Finset.insert`: the lonely set of `ds` is obtained
from `Set.univ` (no runner) by carving with one runner at a time, in any order. -/
theorem lonelySet_induction {P : Finset ℝ → Set ℝ → Prop} (h0 : P ∅ Set.univ)
    (hstep : ∀ d ds, d ∉ ds → P ds (lonelySet ds) → P (insert d ds) (lonelySet ds ∩ clearSet d))
    (ds : Finset ℝ) : P ds (lonelySet ds) := by
  induction ds using Finset.induction_on with
  | empty => rw [lonelySet_empty]; exact h0
  | insert d s hd ih => rw [lonelySet_insert]; exact hstep d s hd ih

#print axioms lonelySet_induction

/-- Carving a set by a list of runners, in the list's order. -/
def carveList (l : List ℝ) (L : Set ℝ) : Set ℝ := l.foldl (fun L d => L ∩ clearSet d) L

theorem carveList_eq (l : List ℝ) (L : Set ℝ) : carveList l L = L ∩ lonelySet l.toFinset := by
  induction l generalizing L with
  | nil => simp [carveList, lonelySet_empty]
  | cons d l ih =>
    unfold carveList at ih ⊢
    rw [List.foldl_cons, ih, List.toFinset_cons, lonelySet_insert]
    ext t; simp only [Set.mem_inter_iff]; tauto

#print axioms carveList_eq

/-- **(3) `lonelySet_toFinset_eq_foldl`** [L]: for any list of runners (for example `d₁ < d₂ < … < d₇`), the lonely set
of the set is `Set.univ` carved by `d₁`, then `d₂`, …, in the list's order. -/
theorem lonelySet_toFinset_eq_foldl (l : List ℝ) : lonelySet l.toFinset = carveList l Set.univ := by
  rw [carveList_eq, Set.univ_inter]

#print axioms lonelySet_toFinset_eq_foldl

/-- The cells of `ds`, as a set of pairs. -/
def cellSet (ds : Finset ℝ) : Set (ℝ × ℝ) := {p | IsCell ds p.1 p.2}

/-- Carving a set of cells by the runner `d`: all nonempty pieces. -/
noncomputable def carveCells (d : ℝ) (C : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {p | ∃ q ∈ C, ∃ N : ℤ, max q.1 (winLo d N) ≤ min q.2 (winHi d N) ∧
    p = (max q.1 (winLo d N), min q.2 (winHi d N))}

/-- **(3) `cellSet_insert`** [L]: the cells of `insert d ds` are the carving of the cells of `ds` by `d`. -/
theorem cellSet_insert {ds : Finset ℝ} (hpos : ∀ e ∈ ds, 0 < e) (hne : ds.Nonempty) {d : ℝ} (hd : 0 < d) :
    cellSet (insert d ds) = carveCells d (cellSet ds) := by
  ext ⟨u', w'⟩
  simp only [cellSet, carveCells, Set.mem_setOf_eq, Prod.mk.injEq]
  rw [isCell_insert_iff hpos hne hd]
  constructor
  · rintro ⟨u, w, N, hc, hle, h1, h2⟩
    exact ⟨(u, w), hc, N, hle, h1, h2⟩
  · rintro ⟨⟨u, w⟩, hc, N, hle, h1, h2⟩
    exact ⟨u, w, N, hc, hle, h1, h2⟩

#print axioms cellSet_insert

/-- **(3) Base of the recursion** [L]: each window `[(N + 1/8)/d, (N + 7/8)/d]`, `N` a natural number, is a cell of
`{d}`. -/
theorem window_isCell {d : ℝ} (hd : 0 < d) (N : ℕ) : IsCell {d} (winLo d N) (winHi d N) := by
  have hle : winLo d N ≤ winHi d N := by have := window_length hd N; have : 0 < 3 / (4 * d) := by positivity
                                         linarith
  have hq : 0 < 1 / (8 * d) := by positivity
  have hq' : 1 / (8 * d) < 1 / (4 * d) := by
    apply one_div_lt_one_div_of_lt (by positivity); linarith
  have hmem : d ∈ ({d} : Finset ℝ) := Finset.mem_singleton_self d
  refine ⟨?_, hle, ?_, ?_, ?_⟩
  · unfold winLo; positivity
  · intro s hs
    rw [lonelySet_singleton, clearSet_eq_iUnion hd]
    exact Set.mem_iUnion.mpr ⟨N, hs⟩
  · intro u'' hu'' hs''
    set s := max u'' (winLo d N - 1 / (8 * d))
    have hs1 : winLo d N - 1 / (4 * d) < s := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hs2 : s < winLo d N := max_lt hu'' (by linarith)
    exact not_lonely_of_inWay hmem (inWay_before_opening hd (mul_winLo hd N) hs1 hs2)
      (hs'' ⟨le_max_left _ _, le_trans hs2.le hle⟩)
  · intro w'' hw'' hs''
    set s := min w'' (winHi d N + 1 / (8 * d))
    have hs1 : winHi d N < s := lt_min hw'' (by linarith)
    have hs2 : s < winHi d N + 1 / (4 * d) := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    exact not_lonely_of_inWay hmem (inWay_after_entry hd (mul_winHi hd N) hs1 hs2)
      (hs'' ⟨le_trans hle hs1.le, min_le_left _ _⟩)

#print axioms window_isCell

/-- **(3) The cells of one runner are exactly its windows of laps `N ≥ 0`** [L]. -/
theorem cell_singleton_iff {d u w : ℝ} (hd : 0 < d) :
    IsCell {d} u w ↔ ∃ N : ℕ, u = winLo d N ∧ w = winHi d N := by
  constructor
  · intro h
    have hpos : ∀ e ∈ ({d} : Finset ℝ), 0 < e := by
      intro e he; rw [Finset.mem_singleton.mp he]; exact hd
    obtain ⟨x, hx, k, hu, -⟩ := cell_left_end_is_opening hpos h
    rw [Finset.mem_singleton.mp hx] at hu
    have hu' : u = winLo d (k : ℕ) := by rw [hu]; unfold winLo; push_cast; rfl
    have hc := window_isCell hd k
    have := cell_unique h hc ⟨le_rfl, h.2.1⟩ ⟨hu'.ge, by rw [hu']; exact hc.2.1⟩
    exact ⟨k, this.1, this.2⟩
  · rintro ⟨N, rfl, rfl⟩
    exact window_isCell hd N

#print axioms cell_singleton_iff

/-! ## (4) L2: a zone of the added runner meets at most one cell -/

/-- Two cells are equal or one lies strictly to the left of the other [L]. -/
theorem cells_ordered {ds : Finset ℝ} {u₁ w₁ u₂ w₂ : ℝ} (h₁ : IsCell ds u₁ w₁) (h₂ : IsCell ds u₂ w₂) :
    (u₁ = u₂ ∧ w₁ = w₂) ∨ w₁ < u₂ ∨ w₂ < u₁ := by
  by_cases ha : w₁ < u₂
  · exact Or.inr (Or.inl ha)
  by_cases hb : w₂ < u₁
  · exact Or.inr (Or.inr hb)
  push Not at ha hb
  left
  exact cell_unique h₁ h₂ ⟨le_max_left _ _, max_le h₁.2.1 ha⟩ ⟨le_max_right _ _, max_le hb h₂.2.1⟩

#print axioms cells_ordered

/-- **(4) `cell_gap`** [L]: for EVERY finite set of positive disparities, two cells with `w₁ < u₂` are separated by at
least `1/(4y)`, `y ∈ ds` the closer of the left cell (in the way on `(w₁, w₁ + 1/(4y))`, which is one of its zones).
Hence the gap is at least `1/(4 d_max(ds))`.  No order of the readings is needed. -/
theorem cell_gap {ds : Finset ℝ} (hpos : ∀ e ∈ ds, 0 < e) {u₁ w₁ u₂ w₂ : ℝ} (h₁ : IsCell ds u₁ w₁)
    (h₂ : IsCell ds u₂ w₂) (hlt : w₁ < u₂) : ∃ y ∈ ds, 1 / (4 * y) ≤ u₂ - w₁ := by
  obtain ⟨y, hy, -, -, -, -, hway⟩ := cell_right_end_is_entry hpos h₁
  refine ⟨y, hy, ?_⟩
  by_contra hc
  push Not at hc
  exact not_lonely_of_inWay hy (hway u₂ hlt (by linarith)) (h₂.2.2.1 ⟨le_rfl, h₂.2.1⟩)

#print axioms cell_gap

/-- **(4) L2, `zone_meets_at_most_one_cell`** [L] [PROVISIONAL: covering]: if the added runner `d` is at least every
disparity of `ds` (the case of K_k, where the readings are added in increasing order), a zone of `d` meets at most one
cell of `ds`.  A window-against-zone statement (a zone of width `1/(4d)` against a gap of at least `1/(4y) ≥ 1/(4d)`);
it supports the claim "the carving of a cell by an added runner leaves at most one piece per zone".  Without the
hypothesis it is false: `L2_fails_without_order`. -/
theorem zone_meets_at_most_one_cell {ds : Finset ℝ} (hpos : ∀ e ∈ ds, 0 < e) {d : ℝ} (hd : 0 < d)
    (hmax : ∀ e ∈ ds, e ≤ d) {N : ℤ} {u₁ w₁ u₂ w₂ s₁ s₂ : ℝ} (h₁ : IsCell ds u₁ w₁) (h₂ : IsCell ds u₂ w₂)
    (hs₁ : s₁ ∈ Set.Icc u₁ w₁) (hs₂ : s₂ ∈ Set.Icc u₂ w₂) (hz₁ : s₁ ∈ zone d N) (hz₂ : s₂ ∈ zone d N) :
    u₁ = u₂ ∧ w₁ = w₂ := by
  have hzw := zone_width' hd N
  -- [PROVISIONAL: covering] supporting "the carving of a cell by an added runner leaves at most one piece per zone":
  -- a gap of at least `1/(4y) ≥ 1/(4d)` cannot fit inside a zone of width `1/(4d)`.
  have key : ∀ {a b c e sa sb : ℝ}, IsCell ds a b → IsCell ds c e → b < c → sa ∈ Set.Icc a b →
      sb ∈ Set.Icc c e → sa ∈ zone d N → sb ∈ zone d N → False := by
    intro a b c e sa sb ha hc hbc hsa hsb hza hzb
    obtain ⟨y, hy, hgap⟩ := cell_gap hpos ha hc hbc
    have hy0 := hpos y hy
    have hyd : 1 / (4 * d) ≤ 1 / (4 * y) :=
      one_div_le_one_div_of_le (by positivity) (by linarith [hmax y hy])
    unfold zone at hza hzb
    have : sb - sa < 1 / (4 * d) := by linarith [hza.1, hzb.2]
    linarith [hsa.2, hsb.1]
  rcases cells_ordered h₁ h₂ with h | h | h
  · exact h
  · exact (key h₁ h₂ h hs₁ hs₂ hz₁ hz₂).elim
  · exact (key h₂ h₁ h hs₂ hs₁ hz₂ hz₁).elim

#print axioms zone_meets_at_most_one_cell

/-- **(4) The exception to L2 without the order** [L]: for `ds = {8}` and the added runner `d = 1 < 8`, the zone
`(7/8, 9/8)` of lap `1` of runner `1` contains two whole cells of `{8}`: `[57/64, 63/64]` and `[65/64, 71/64]`.
Why: the hypothesis `d ≥ max ds` fails; the gap between cells of `{8}` is a zone of `8`, of width `1/32`, while the
zone of `1` has width `1/4`, so it holds the gap together with the cells on both sides (as `cell_gap` predicts, the
gap `1/(4·8)` is not at least `1/(4·1)`). -/
theorem L2_fails_without_order :
    IsCell {(8 : ℝ)} (57 / 64) (63 / 64) ∧ IsCell {(8 : ℝ)} (65 / 64) (71 / 64) ∧
      Set.Icc (57 / 64 : ℝ) (63 / 64) ⊆ zone 1 1 ∧ Set.Icc (65 / 64 : ℝ) (71 / 64) ⊆ zone 1 1 ∧
      (57 / 64 : ℝ) ≠ 65 / 64 := by
  have h7 := window_isCell (d := 8) (by norm_num) 7
  have h8 := window_isCell (d := 8) (by norm_num) 8
  have e1 : winLo 8 ((7 : ℕ) : ℤ) = 57 / 64 := by unfold winLo; norm_num
  have e2 : winHi 8 ((7 : ℕ) : ℤ) = 63 / 64 := by unfold winHi; norm_num
  have e3 : winLo 8 ((8 : ℕ) : ℤ) = 65 / 64 := by unfold winLo; norm_num
  have e4 : winHi 8 ((8 : ℕ) : ℤ) = 71 / 64 := by unfold winHi; norm_num
  rw [e1, e2] at h7
  rw [e3, e4] at h8
  refine ⟨h7, h8, ?_, ?_, by norm_num⟩
  · intro s hs; unfold zone; push_cast; constructor <;> linarith [hs.1, hs.2]
  · intro s hs; unfold zone; push_cast; constructor <;> linarith [hs.1, hs.2]

#print axioms L2_fails_without_order

/-! ## (6) The AP touch produced by carving -/

/-- The prefix `{1, …, k}` of the AP's disparities. -/
noncomputable def apPrefix (k : ℕ) : Finset ℝ := (Finset.Icc 1 k).image (fun i : ℕ => (i : ℝ))

theorem apPrefix_pos (k : ℕ) : ∀ e ∈ apPrefix k, (0 : ℝ) < e := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
  have : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  exact_mod_cast this

#print axioms apPrefix_pos

theorem apPrefix_succ (k : ℕ) : apPrefix (k + 1) = insert ((k : ℝ) + 1) (apPrefix k) := by
  unfold apPrefix
  ext x
  simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_insert]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · exact Or.inr ⟨i, ⟨h1, by omega⟩, rfl⟩
    · left
      have : i = k + 1 := by omega
      subst this; push_cast; rfl
  · rintro (rfl | ⟨i, ⟨h1, h2⟩, rfl⟩)
    · exact ⟨k + 1, ⟨by omega, le_rfl⟩, by push_cast; rfl⟩
    · exact ⟨i, ⟨h1, by omega⟩, rfl⟩

#print axioms apPrefix_succ

/-- **(6) `ap_first_cell_carving`** [L]: for `1 ≤ k ≤ 7`, `[1/8, 7/(8k)]` is a cell of `{1, …, k}`.  By carving: the
cell `[1/8, 7/8]` of `{1}` is the window of lap `0`; adding runner `k + 1` cuts it with the window `[1/(8(k+1)),
7/(8(k+1))]` of its lap `0`, whose opening lies below `1/8` and whose entry `7/(8(k+1))` becomes the new right end. -/
theorem ap_first_cell_carving : ∀ k : ℕ, 1 ≤ k → k ≤ 7 → IsCell (apPrefix k) (1 / 8) (7 / (8 * k)) := by
  intro k hk1 hk7
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · -- base: `{1}` and its window of lap `0`
      have h := window_isCell (d := 1) one_pos 0
      have e : apPrefix (0 + 1) = {(1 : ℝ)} := by
        unfold apPrefix; simp
      rw [e]
      have e1 : winLo 1 ((0 : ℕ) : ℤ) = 1 / 8 := by unfold winLo; norm_num
      have e2 : winHi 1 ((0 : ℕ) : ℤ) = 7 / 8 := by unfold winHi; norm_num
      rw [e1, e2] at h
      convert h using 2; push_cast; ring
    · have hc := ih hk (by omega)
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hk7' : (k : ℝ) + 1 ≤ 7 := by exact_mod_cast hk7
      have hd : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have elo : winLo ((k : ℝ) + 1) 0 = 1 / (8 * ((k : ℝ) + 1)) := by
        unfold winLo; field_simp; push_cast; ring
      have ehi : winHi ((k : ℝ) + 1) 0 = 7 / (8 * ((k : ℝ) + 1)) := by
        unfold winHi; field_simp; push_cast; ring
      have hlo : winLo ((k : ℝ) + 1) 0 ≤ 1 / 8 := by
        rw [elo, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      have hhi : winHi ((k : ℝ) + 1) 0 ≤ 7 / (8 * (k : ℝ)) := by
        rw [ehi, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      have hmax : max (1 / 8 : ℝ) (winLo ((k : ℝ) + 1) 0) = 1 / 8 := max_eq_left hlo
      have hmin : min (7 / (8 * (k : ℝ))) (winHi ((k : ℝ) + 1) 0) = 7 / (8 * ((k : ℝ) + 1)) := by
        rw [min_eq_right hhi, ehi]
      have hne : max (1 / 8 : ℝ) (winLo ((k : ℝ) + 1) 0) ≤ min (7 / (8 * (k : ℝ))) (winHi ((k : ℝ) + 1) 0) := by
        rw [hmax, hmin, div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
      have h := piece_isCell hd hc hne
      rw [hmax, hmin, ← apPrefix_succ] at h
      convert h using 2; push_cast; ring

#print axioms ap_first_cell_carving

/-- **(6) `ap_first_cell_leftmost`** [L]: for `1 ≤ k`, every cell `[u, w]` of `{1, …, k}` has `1/8 ≤ u`, so together
with `ap_first_cell_carving` the cell `[1/8, 7/(8k)]` is the first (leftmost) cell.  Why: runner `1` belongs to every
prefix, and on `(0, 1/8)` it lies in its zone of lap `0`. -/
theorem ap_first_cell_leftmost {k : ℕ} (hk : 1 ≤ k) {u w : ℝ} (h : IsCell (apPrefix k) u w) : (1 / 8 : ℝ) ≤ u := by
  have h1 : (1 : ℝ) ∈ apPrefix k :=
    Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hk⟩, by norm_num⟩
  have hl : u ∈ lonelySet (apPrefix k) := h.2.2.1 ⟨le_rfl, h.2.1⟩
  rw [lonelySet_eq_iInter] at hl
  have hc : u ∈ clearSet 1 := Set.mem_iInter₂.mp hl 1 h1
  by_contra hlt
  have hlt' : u < 1 / 8 := not_le.mp hlt
  have hz : u ∈ zone 1 0 :=
    (mem_zone_iff one_pos 0).mpr ⟨by push_cast; linarith [h.1], by push_cast; linarith⟩
  exact Set.disjoint_left.mp (zone_disjoint_clearSet one_pos 0) hz hc

#print axioms ap_first_cell_leftmost

/-- **(6) `ap_touch_by_carving`** [L]: at `k = 7` the carving gives the touch `[1/8, 1/8]`: the entry `7/(8·7)` of
runner `7` at lap `0` meets the opening `1/8` of runner `1`.  `apPrefix 7` is the AP's set `LonelyCells.apSet`. -/
theorem ap_touch_by_carving : apPrefix 7 = apSet ∧ IsCell apSet (1 / 8) (1 / 8) := by
  have he : apPrefix 7 = apSet := by
    unfold apPrefix apSet
    ext x
    simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
      interval_cases i <;> norm_num
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      exacts [⟨1, by norm_num⟩, ⟨2, by norm_num⟩, ⟨3, by norm_num⟩, ⟨4, by norm_num⟩, ⟨5, by norm_num⟩,
        ⟨6, by norm_num⟩, ⟨7, by norm_num⟩]
  refine ⟨he, ?_⟩
  have h := ap_first_cell_carving 7 (by norm_num) le_rfl
  rw [he] at h
  convert h using 1; norm_num

#print axioms ap_touch_by_carving

end Fresh.Carving
