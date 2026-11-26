import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Dilation
import Fresh.Localisation
import Fresh.WhereProofs

/-!
# The shape of the lonely set near the landing (Task M; mapping, rule 1, goal G1)

Written 2026-10-07.  Imports `Mathlib` and the Fresh modules `Framework`, `Cascade`, `Dilation`, `Localisation`,
`WhereProofs`; nothing from the existing `LonelyRunner` repo.  Exact reals only; every disparity is positive (no runner
is stationary); every statement is symbolic, for every finite set `ds` of positive disparities (or every arrangement).

This file MAPS the object.  It does not argue that a lonely instant exists: every statement is about cells that exist.
No bound on moves or chain length is stated anywhere.

Objects.  The lonely set `lonelySet ds = {t | LonelyAt ds t}`.  A *cell* `[u, w]` (`IsCell`) is a maximal closed
interval of it with `0 < u`.  For a disparity `d` and an instant `t`: the last opening `(⌊d t⌋ + 1/8)/d`
(`Localisation.lastOpening`) and the next entry `(⌊d t⌋ + 7/8)/d` (`nextEntry`).

Results (grades in the docstrings; every [L] has its `#print axioms` line below it).
* (1) `isClosed_lonelySet`: the lonely set is closed (an intersection of closed sets, one per disparity and lap).
  `cell_of_lonely`: every positive lonely `t` lies in the cell `[max_x lastOpening x t, min_y nextEntry y t]`.
  `cell_unique`: two cells sharing a point are equal.  `cells_upTo_finite`: the cells with left end `≤ b` form a
  finite set `[PROVISIONAL: counting tool]`; `lonely_upTo_iff_cells`: `(0, b] ∩ L` is their union (clipped to `b`).
* (2) `cell_left_end_is_opening`, `cell_right_end_is_entry`.
* (3) `first_cell_iff`, `landing_is_first_cell_left_end`, `landing_eq_first_cell_left_end`,
  `cascade_lands_at_first_cell`.
* (4) `cell_width`, `cell_nondegenerate_iff`, `opener_eq_closer_window`, `degenerate_opener_ne_closer`,
  `degenerate_cell_isolated`; the touch at the AP: `ap_first_cell_is_touch`.
* (5) `states_below_landing`, `final_setter_opens_cell`.

Provenance.  The left-end construction is the localisation argument (`Fresh.Localisation.exists_opening_of_lonely`,
existing repo `Flanks.exists_flank_of_lonely`), run here at a lonely instant to find the start of its cell; the
right-end construction is its mirror (written for this file; no existing declaration of that name was found by a
search of `LRC/` for `cell`, `touch`, `lastOpening`).  The cells are the record's boundary set method (v9 §1, P§2.1:
"between consecutive endpoints the status is constant") and the touch is record L7 (v9 §7).  Every proof here was
written for this file; no proof was copied.
-/

open Classical

namespace Fresh.LonelyCells

open Fresh

/-- The lonely set of a set of disparities. -/
def lonelySet (ds : Finset ℝ) : Set ℝ := {t | Cascade.LonelyAt ds t}

/-- A cell of the lonely set: a maximal closed interval `[u, w]` of it with `0 < u` (possibly a single point). -/
-- STANDING: DEFINITION
def IsCell (ds : Finset ℝ) (u w : ℝ) : Prop := 0 < u ∧ u ≤ w ∧ Set.Icc u w ⊆ lonelySet ds ∧ (∀ u' < u, ¬ Set.Icc u' w ⊆ lonelySet ds) ∧ (∀ w' > w, ¬ Set.Icc u w' ⊆ lonelySet ds)

/-- The next entry of runner `d` after `t`: the instant at which it stands at `⌊d t⌋ + 7/8`. -/
noncomputable def nextEntry (d t : ℝ) : ℝ := (((⌊d * t⌋ : ℤ) : ℝ) + 7 / 8) / d

/-! ## Local facts: in the way near a lap line -/

/-- Within `1/8` of a lap line means in the way. -/
theorem inWay_of_near {x s : ℝ} (N : ℤ) (h : |x * s - N| < 1 / 8) : InWay x s :=
  lt_of_le_of_lt (Localisation.distInt_le (x * s) N) h

#print axioms inWay_of_near

/-- **Just before an opening the runner is in the way**: if `x a = N + 1/8` then `x` is in the way on
`(a − 1/(4x), a)`. -/
theorem inWay_before_opening {x a s : ℝ} (hx : 0 < x) {N : ℤ} (ha : x * a = N + 1 / 8)
    (h1 : a - 1 / (4 * x) < s) (h2 : s < a) : InWay x s := by
  apply inWay_of_near N
  have e : x * (a - 1 / (4 * x)) = x * a - 1 / 4 := by field_simp
  have l1 := mul_lt_mul_of_pos_left h1 hx
  have l2 := mul_lt_mul_of_pos_left h2 hx
  rw [abs_lt]; constructor <;> linarith

#print axioms inWay_before_opening

/-- **Just after an entry the runner is in the way**: if `x b = N + 7/8` then `x` is in the way on
`(b, b + 1/(4x))`. -/
theorem inWay_after_entry {x b s : ℝ} (hx : 0 < x) {N : ℤ} (hb : x * b = N + 7 / 8)
    (h1 : b < s) (h2 : s < b + 1 / (4 * x)) : InWay x s := by
  apply inWay_of_near (N + 1)
  have e : x * (b + 1 / (4 * x)) = x * b + 1 / 4 := by field_simp
  have l1 := mul_lt_mul_of_pos_left h1 hx
  have l2 := mul_lt_mul_of_pos_left h2 hx
  push_cast
  rw [abs_lt]; constructor <;> linarith

#print axioms inWay_after_entry

/-- A runner in the way at `s` makes `s` not lonely. -/
theorem not_lonely_of_inWay {ds : Finset ℝ} {x s : ℝ} (hx : x ∈ ds) (h : InWay x s) : s ∉ lonelySet ds :=
  fun hl => Cascade.not_inWay_iff.mpr (hl x hx) h

#print axioms not_lonely_of_inWay

/-- The empty set of disparities is lonely everywhere. -/
theorem lonelySet_empty : lonelySet (∅ : Finset ℝ) = Set.univ := by
  ext t; simp [lonelySet, Cascade.LonelyAt]

#print axioms lonelySet_empty

/-! ## (1) Closedness -/

/-- **(1a) The lonely set is closed** [L]: it is `⋂_{d ∈ ds} ⋂_{z ∈ ℤ} {t | 1/8 ≤ |d t − z|}`, an intersection of
closed sets.  Hence `{t > 0 | LonelyAt ds t} = (0, ∞) ∩ lonelySet ds` is closed in `(0, ∞)`. -/
theorem isClosed_lonelySet (ds : Finset ℝ) : IsClosed (lonelySet ds) := by
  have h : lonelySet ds = ⋂ d ∈ ds, ⋂ z : ℤ, {t : ℝ | (1 / 8 : ℝ) ≤ |d * t - z|} := by
    ext t
    simp only [lonelySet, Cascade.LonelyAt, Set.mem_setOf_eq, Set.mem_iInter]
    exact forall₂_congr fun d _ => Localisation.le_distInt_iff _ _
  rw [h]
  refine isClosed_biInter fun d _ => isClosed_iInter fun z => ?_
  exact isClosed_le continuous_const (by fun_prop)

#print axioms isClosed_lonelySet

/-! ## The cell of a lonely instant -/

/-- The last opening of a runner clear at `t > 0` is positive. -/
theorem lastOpening_pos {x t : ℝ} (hx : 0 < x) (ht : 0 < t) : 0 < Localisation.lastOpening x t := by
  unfold Localisation.lastOpening
  have : (0 : ℝ) ≤ ((⌊x * t⌋ : ℤ) : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr (by positivity)
  exact div_pos (by linarith) hx

#print axioms lastOpening_pos

/-- At its last opening the runner reads exactly `⌊x t⌋ + 1/8`. -/
theorem mul_lastOpening {x t : ℝ} (hx : 0 < x) :
    x * Localisation.lastOpening x t = ((⌊x * t⌋ : ℤ) : ℝ) + 1 / 8 := by
  unfold Localisation.lastOpening; field_simp

#print axioms mul_lastOpening

/-- At its next entry the runner reads exactly `⌊x t⌋ + 7/8`. -/
theorem mul_nextEntry {x t : ℝ} (hx : 0 < x) : x * nextEntry x t = ((⌊x * t⌋ : ℤ) : ℝ) + 7 / 8 := by
  unfold nextEntry; field_simp

#print axioms mul_nextEntry

/-- A runner clear at `t` has its next entry at or after `t`. -/
theorem le_nextEntry {d t : ℝ} (hd : 0 < d) (hc : (1 / 8 : ℝ) ≤ distInt (d * t)) : t ≤ nextEntry d t := by
  have hf := ((Localisation.clear_iff_fract _).mp hc).2
  unfold Int.fract at hf
  unfold nextEntry
  rw [le_div_iff₀ hd]
  linarith

#print axioms le_nextEntry

/-- The mirror of the window step: a runner clear at `t` stays clear on `[t, nextEntry d t]`. -/
theorem clear_until_entry {d s t : ℝ} (hd : 0 < d) (hc : (1 / 8 : ℝ) ≤ distInt (d * t))
    (hlo : t ≤ s) (hhi : s ≤ nextEntry d t) : (1 / 8 : ℝ) ≤ distInt (d * s) := by
  have hf := (Localisation.clear_iff_fract _).mp hc
  unfold Int.fract at hf
  unfold nextEntry at hhi
  rw [le_div_iff₀ hd] at hhi
  apply Localisation.clear_of_window ⌊d * t⌋
  · have : d * t ≤ d * s := mul_le_mul_of_nonneg_left hlo hd.le
    linarith [hf.1]
  · linarith

#print axioms clear_until_entry

/-- **The start of the cell of `t`**: the latest last opening `T` before a lonely `t` is at most `t`, and `[T, t]` is
lonely (positivity of `T` for `t > 0` is `lastOpening_pos`). -/
theorem exists_start {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hne : ds.Nonempty) {t : ℝ}
    (hl : t ∈ lonelySet ds) :
    ∃ x ∈ ds, Localisation.lastOpening x t ≤ t ∧
      Set.Icc (Localisation.lastOpening x t) t ⊆ lonelySet ds := by
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image ds (fun e => Localisation.lastOpening e t) hne
  refine ⟨x, hx, Localisation.lastOpening_le (hpos x hx) (hl x hx), ?_⟩
  intro s hs d hd
  exact Localisation.clear_between (hpos d hd) (hl d hd) (le_trans (hmax d hd) hs.1) hs.2

#print axioms exists_start

/-- **The end of the cell of `t`**: the earliest next entry `S` after a lonely `t` is at least `t`, and `[t, S]` is
lonely. -/
theorem exists_end {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hne : ds.Nonempty) {t : ℝ}
    (hl : t ∈ lonelySet ds) :
    ∃ y ∈ ds, t ≤ nextEntry y t ∧ Set.Icc t (nextEntry y t) ⊆ lonelySet ds := by
  obtain ⟨y, hy, hmin⟩ := Finset.exists_min_image ds (fun e => nextEntry e t) hne
  refine ⟨y, hy, le_nextEntry (hpos y hy) (hl y hy), ?_⟩
  intro s hs d hd
  exact clear_until_entry (hpos d hd) (hl d hd) hs.1 (le_trans hs.2 (hmin d hd))

#print axioms exists_end

/-- **(1b) Every positive lonely instant lies in a cell, with explicit ends** [L]: the cell of `t` is
`[lastOpening x t, nextEntry y t]`, `x` maximising the last opening and `y` minimising the next entry.  Left of the
cell `x` is in the way, right of it `y` is.  (`ds` nonempty: with no disparity the lonely set is all of `ℝ`.) -/
theorem cell_of_lonely {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hne : ds.Nonempty) {t : ℝ} (ht : 0 < t)
    (hl : t ∈ lonelySet ds) :
    ∃ x ∈ ds, ∃ y ∈ ds, IsCell ds (Localisation.lastOpening x t) (nextEntry y t) ∧
      Localisation.lastOpening x t ≤ t ∧ t ≤ nextEntry y t := by
  obtain ⟨x, hx, hT, hTs⟩ := exists_start hpos hne hl
  obtain ⟨y, hy, hS, hSs⟩ := exists_end hpos hne hl
  have hx0 := hpos x hx
  have hy0 := hpos y hy
  set T := Localisation.lastOpening x t with hTdef
  set S := nextEntry y t with hSdef
  have hsub : Set.Icc T S ⊆ lonelySet ds := by
    intro s hs
    rcases le_total s t with h | h
    · exact hTs ⟨hs.1, h⟩
    · exact hSs ⟨h, hs.2⟩
  have hTx : x * T = ((⌊x * t⌋ : ℤ) : ℝ) + 1 / 8 := mul_lastOpening hx0
  have hSy : y * S = ((⌊y * t⌋ : ℤ) : ℝ) + 7 / 8 := mul_nextEntry hy0
  refine ⟨x, hx, y, hy, ⟨lastOpening_pos hx0 ht, le_trans hT hS, hsub, ?_, ?_⟩, hT, hS⟩
  · intro u' hu' hsub'
    set s := max u' (T - 1 / (8 * x)) with hsdef
    have hq : 0 < 1 / (8 * x) := by positivity
    have hq' : 1 / (8 * x) < 1 / (4 * x) := by
      apply one_div_lt_one_div_of_lt (by positivity); linarith
    have hs1 : T - 1 / (4 * x) < s := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hs2 : s < T := max_lt hu' (by linarith)
    have hw := inWay_before_opening hx0 hTx hs1 hs2
    exact not_lonely_of_inWay hx hw (hsub' ⟨le_max_left _ _, le_trans hs2.le (le_trans hT hS)⟩)
  · intro w' hw' hsub'
    set s := min w' (S + 1 / (8 * y)) with hsdef
    have hq : 0 < 1 / (8 * y) := by positivity
    have hq' : 1 / (8 * y) < 1 / (4 * y) := by
      apply one_div_lt_one_div_of_lt (by positivity); linarith
    have hs1 : S < s := lt_min hw' (by linarith)
    have hs2 : s < S + 1 / (4 * y) := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hw := inWay_after_entry hy0 hSy hs1 hs2
    exact not_lonely_of_inWay hy hw (hsub' ⟨le_trans (le_trans hT hS) hs1.le, min_le_left _ _⟩)

#print axioms cell_of_lonely

/-- **(1c) Two cells sharing a point are equal** [L].  Pure order: the union of two overlapping intervals of the
lonely set is an interval of it, and maximality does the rest. -/
theorem cell_unique {ds : Finset ℝ} {u w u' w' t : ℝ} (h : IsCell ds u w) (h' : IsCell ds u' w')
    (ht : t ∈ Set.Icc u w) (ht' : t ∈ Set.Icc u' w') : u = u' ∧ w = w' := by
  have hU : Set.Icc (min u u') (max w w') ⊆ lonelySet ds := by
    intro s hs
    rcases le_or_gt s t with hst | hst
    · by_cases hsu : u ≤ s
      · exact h.2.2.1 ⟨hsu, le_trans hst ht.2⟩
      · have : u' ≤ s := by
          rcases min_le_iff.mp hs.1 with h1 | h1
          · exact absurd h1 hsu
          · exact h1
        exact h'.2.2.1 ⟨this, le_trans hst ht'.2⟩
    · rcases le_max_iff.mp hs.2 with h1 | h1
      · exact h.2.2.1 ⟨le_trans ht.1 hst.le, h1⟩
      · exact h'.2.2.1 ⟨le_trans ht'.1 hst.le, h1⟩
  have hsub1 : Set.Icc (min u u') w ⊆ lonelySet ds :=
    fun s hs => hU ⟨hs.1, le_trans hs.2 (le_max_left _ _)⟩
  have hsub2 : Set.Icc (min u u') w' ⊆ lonelySet ds :=
    fun s hs => hU ⟨hs.1, le_trans hs.2 (le_max_right _ _)⟩
  have hsub3 : Set.Icc u (max w w') ⊆ lonelySet ds :=
    fun s hs => hU ⟨le_trans (min_le_left _ _) hs.1, hs.2⟩
  have hsub4 : Set.Icc u' (max w w') ⊆ lonelySet ds :=
    fun s hs => hU ⟨le_trans (min_le_right _ _) hs.1, hs.2⟩
  constructor
  · apply le_antisymm
    · by_contra hc; push Not at hc
      exact h.2.2.2.1 _ (min_lt_iff.mpr (Or.inr hc)) hsub1
    · by_contra hc; push Not at hc
      exact h'.2.2.2.1 _ (min_lt_iff.mpr (Or.inl hc)) hsub2
  · apply le_antisymm
    · by_contra hc; push Not at hc
      exact h'.2.2.2.2 _ (lt_max_iff.mpr (Or.inl hc)) hsub4
    · by_contra hc; push Not at hc
      exact h.2.2.2.2 _ (lt_max_iff.mpr (Or.inr hc)) hsub3

#print axioms cell_unique

/-- A cell exists only if some disparity is present (with none, the lonely set is all of `ℝ` and has no maximal
bounded interval). -/
theorem nonempty_of_cell {ds : Finset ℝ} {u w : ℝ} (h : IsCell ds u w) : ds.Nonempty := by
  by_contra hc
  rw [Finset.not_nonempty_iff_eq_empty] at hc
  subst hc
  exact h.2.2.2.1 (u - 1) (by linarith) (by rw [lonelySet_empty]; exact Set.subset_univ _)

#print axioms nonempty_of_cell

/-! ## (2) Cell ends -/

/-- **(2a) `cell_left_end_is_opening`** [L]: the left end `u` of a cell is an opening `(k + 1/8)/x` of some runner
`x ∈ ds` (`k` a natural number): `x` stands at exactly `1/8` past its lap line `k` at `u`, and is in the way on
`(u − 1/(4x), u)`. -/
theorem cell_left_end_is_opening {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {u w : ℝ} (h : IsCell ds u w) :
    ∃ x ∈ ds, ∃ k : ℕ, u = ((k : ℝ) + 1 / 8) / x ∧ x * u = (k : ℝ) + 1 / 8 ∧ distInt (x * u) = 1 / 8 ∧
      ∀ s, u - 1 / (4 * x) < s → s < u → InWay x s := by
  have hne := nonempty_of_cell h
  have hl : u ∈ lonelySet ds := h.2.2.1 ⟨le_rfl, h.2.1⟩
  obtain ⟨x, hx, y, hy, hc, hT, hS⟩ := cell_of_lonely hpos hne h.1 hl
  have hu := (cell_unique hc h ⟨hT, hS⟩ ⟨le_rfl, h.2.1⟩).1
  have hx0 := hpos x hx
  have hfl : (0 : ℤ) ≤ ⌊x * u⌋ := Int.floor_nonneg.mpr (by have := h.1; positivity)
  have hcast : ((⌊x * u⌋.toNat : ℕ) : ℝ) = ((⌊x * u⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hfl
  have hxu : x * u = ((⌊x * u⌋ : ℤ) : ℝ) + 1 / 8 := by
    have := mul_lastOpening (x := x) (t := u) hx0
    rwa [hu] at this
  refine ⟨x, hx, ⌊x * u⌋.toNat, ?_, ?_, ?_, ?_⟩
  · rw [hcast, ← hxu]; field_simp
  · rw [hcast]; exact hxu
  · rw [hxu, add_comm]; exact Cascade.distInt_eighth_add_int _
  · intro s h1 h2
    exact inWay_before_opening hx0 hxu h1 h2

#print axioms cell_left_end_is_opening

/-- **(2b) `cell_right_end_is_entry`** [L]: the right end `w` of a cell is an entry `(k' + 7/8)/y` of some runner
`y ∈ ds`: `y` stands at exactly `7/8` past its lap line `k'` at `w` (circle distance `1/8`), and is in the way on
`(w, w + 1/(4y))`: it enters its zone just after `w`. -/
theorem cell_right_end_is_entry {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {u w : ℝ} (h : IsCell ds u w) :
    ∃ y ∈ ds, ∃ k' : ℕ, w = ((k' : ℝ) + 7 / 8) / y ∧ y * w = (k' : ℝ) + 7 / 8 ∧ distInt (y * w) = 1 / 8 ∧
      ∀ s, w < s → s < w + 1 / (4 * y) → InWay y s := by
  have hne := nonempty_of_cell h
  have hw0 : 0 < w := lt_of_lt_of_le h.1 h.2.1
  have hl : w ∈ lonelySet ds := h.2.2.1 ⟨h.2.1, le_rfl⟩
  obtain ⟨x, hx, y, hy, hc, hT, hS⟩ := cell_of_lonely hpos hne hw0 hl
  have hw := (cell_unique hc h ⟨hT, hS⟩ ⟨h.2.1, le_rfl⟩).2
  have hy0 := hpos y hy
  have hfl : (0 : ℤ) ≤ ⌊y * w⌋ := Int.floor_nonneg.mpr (by positivity)
  have hcast : ((⌊y * w⌋.toNat : ℕ) : ℝ) = ((⌊y * w⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hfl
  have hyw : y * w = ((⌊y * w⌋ : ℤ) : ℝ) + 7 / 8 := by
    have := mul_nextEntry (x := y) (t := w) hy0
    rwa [hw] at this
  refine ⟨y, hy, ⌊y * w⌋.toNat, ?_, ?_, ?_, ?_⟩
  · rw [hcast, ← hyw]; field_simp
  · rw [hcast]; exact hyw
  · rw [hyw]
    have e : ((⌊y * w⌋ : ℤ) : ℝ) + 7 / 8 = -(1 / 8) + (((⌊y * w⌋ + 1 : ℤ)) : ℝ) := by push_cast; ring
    rw [e, Localisation.distInt_add_int, Localisation.distInt_neg]
    have := Cascade.distInt_eighth_add_int 0
    simpa using this
  · intro s h1 h2
    exact inWay_after_entry hy0 hyw h1 h2

#print axioms cell_right_end_is_entry

/-! ## (1d) Finitely many cells below any bound, and the lonely set is their union -/

/-- The left end of a cell at or below `b` is one of the finitely many openings up to `b`. -/
theorem cell_left_end_mem_openings {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {u w b : ℝ} (h : IsCell ds u w)
    (hb : u ≤ b) : u ∈ Cascade.openingsUpTo ds b := by
  obtain ⟨x, hx, k, hu, hxu, -, -⟩ := cell_left_end_is_opening hpos h
  have hx0 := hpos x hx
  have hkb : (k : ℝ) ≤ x * b := by
    have := mul_le_mul_of_nonneg_left hb hx0.le
    linarith
  have hkc : (k : ℤ) ≤ ⌈x * b⌉ := by
    have h1 := Int.le_ceil (x * b)
    have : ((k : ℤ) : ℝ) ≤ (⌈x * b⌉ : ℝ) := by push_cast; linarith
    exact_mod_cast this
  refine Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨(k : ℤ), Finset.mem_Icc.mpr ⟨by omega, hkc⟩, ?_⟩⟩
  rw [hu]; push_cast; rfl

#print axioms cell_left_end_mem_openings

/-- **(1d) Finitely many cells start at or below any `b`** [L].
[PROVISIONAL: counting tool] the last step (a subset of a finite set is finite, and a cell is determined by its left
end) supports the claim "finitely many cells meet `(0, b]`".  Nothing counts moves or bounds a chain. -/
theorem cells_upTo_finite {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (b : ℝ) :
    {p : ℝ × ℝ | IsCell ds p.1 p.2 ∧ p.1 ≤ b}.Finite := by
  have hsub : Prod.fst '' {p : ℝ × ℝ | IsCell ds p.1 p.2 ∧ p.1 ≤ b} ⊆ ↑(Cascade.openingsUpTo ds b) := by
    rintro _ ⟨p, hp, rfl⟩
    exact cell_left_end_mem_openings hpos hp.1 hp.2
  -- [PROVISIONAL: counting tool] supporting "finitely many cells meet (0, b]".
  have hfin := (Cascade.openingsUpTo ds b).finite_toSet.subset hsub
  refine Set.Finite.of_finite_image hfin ?_
  intro p hp q hq hpq
  have hq' : p.1 ∈ Set.Icc q.1 q.2 := by rw [hpq]; exact ⟨le_rfl, hq.1.2.1⟩
  obtain ⟨h1, h2⟩ := cell_unique hp.1 hq.1 ⟨le_rfl, hp.1.2.1⟩ hq'
  exact Prod.ext h1 h2

#print axioms cells_upTo_finite

/-- **(1e) The bounded part of the positive lonely set is the union of the cells starting at or below `b`** [L]
(clipped at `b`); with (1d), a finite union of closed intervals, possibly points. -/
theorem lonely_upTo_iff_cells {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hne : ds.Nonempty) (b t : ℝ) :
    (0 < t ∧ t ≤ b ∧ t ∈ lonelySet ds) ↔
      ∃ p ∈ {p : ℝ × ℝ | IsCell ds p.1 p.2 ∧ p.1 ≤ b}, t ∈ Set.Icc p.1 p.2 ∧ t ≤ b := by
  constructor
  · rintro ⟨ht, htb, hl⟩
    obtain ⟨x, _, y, _, hc, hT, hS⟩ := cell_of_lonely hpos hne ht hl
    exact ⟨(_, _), ⟨hc, le_trans hT htb⟩, ⟨hT, hS⟩, htb⟩
  · rintro ⟨p, hp, ht, htb⟩
    exact ⟨lt_of_lt_of_le hp.1.1 ht.1, htb, hp.1.2.2.1 ht⟩

#print axioms lonely_upTo_iff_cells

/-! ## (3) The landing is the left end of the first cell -/

/-- **(3a) The first isolation is the left end of the first cell, and conversely** [L]: `u` is the least positive
lonely instant iff `u` is the left end of a cell and no cell starts before it. -/
theorem first_cell_iff {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hne : ds.Nonempty) {u : ℝ} :
    IsLeast {t | 0 < t ∧ t ∈ lonelySet ds} u ↔
      ∃ w, IsCell ds u w ∧ ∀ u' w', IsCell ds u' w' → u ≤ u' := by
  constructor
  · rintro ⟨⟨hu, hl⟩, hlow⟩
    obtain ⟨x, _, y, _, hc, hT, hS⟩ := cell_of_lonely hpos hne hu hl
    have hTl : Localisation.lastOpening x u ∈ lonelySet ds := hc.2.2.1 ⟨le_rfl, hc.2.1⟩
    have hTu : u ≤ Localisation.lastOpening x u := hlow ⟨hc.1, hTl⟩
    have he : Localisation.lastOpening x u = u := le_antisymm hT hTu
    rw [he] at hc
    refine ⟨_, hc, fun u' w' hc' => hlow ⟨hc'.1, hc'.2.2.1 ⟨le_rfl, hc'.2.1⟩⟩⟩
  · rintro ⟨w, hc, hfirst⟩
    refine ⟨⟨hc.1, hc.2.2.1 ⟨le_rfl, hc.2.1⟩⟩, ?_⟩
    rintro t ⟨ht, hl⟩
    obtain ⟨x, _, y, _, hc', hT, _⟩ := cell_of_lonely hpos hne ht hl
    exact le_trans (hfirst _ _ hc') hT

#print axioms first_cell_iff

/-- Isolation of an arrangement's subject, as the positive lonely set of its disparities. -/
theorem isolation_set_eq {v : Fin 8 → ℝ} (k : Fin 8) :
    {t : ℝ | 0 < t ∧ IsolatedAt v k t} = {t | 0 < t ∧ t ∈ lonelySet (disparitySet v k)} := by
  ext t
  simp only [Set.mem_setOf_eq, lonelySet, Cascade.isolatedAt_iff_lonelyAt]

#print axioms isolation_set_eq

/-- **(3b) `landing_is_first_cell_left_end`** [L]: if the cascade from `1/(8 d_min)` reaches a fixed point `t⋆`, then
`t⋆` is the left end of a cell `[t⋆, w]`, no cell starts before it, and `t⋆` is an opening `(j + 1/8)/x` of a runner
`x` of the subject (which stands at exactly `1/8` there).  Every later isolation lies in the lonely set, i.e. in a
later cell or in `[t⋆, w]` (`cell_of_lonely`). -/
theorem landing_is_first_cell_left_end {v : Fin 8 → ℝ} (hv : IsArrangement v) {k : Fin 8} {m : ℝ}
    (hm : IsDmin v k m) {tStar : ℝ} (hr : Where.CascadeReaches (disparitySet v k) (1 / (8 * m)) tStar) :
    ∃ w, IsCell (disparitySet v k) tStar w ∧ (∀ u' w', IsCell (disparitySet v k) u' w' → tStar ≤ u') ∧
      ∃ x ∈ disparitySet v k, ∃ j : ℕ, tStar = ((j : ℝ) + 1 / 8) / x ∧ x * tStar = (j : ℝ) + 1 / 8 := by
  have hpos := Cascade.disparitySet_pos hv k
  have hne := Localisation.disparitySet_nonempty v k
  have hL := WhereProofs.landingIsFirstIsolation v hv k m hm tStar hr
  rw [isolation_set_eq] at hL
  obtain ⟨w, hc, hfirst⟩ := (first_cell_iff hpos hne).mp hL
  obtain ⟨x, hx, j, h1, h2, -, -⟩ := cell_left_end_is_opening hpos hc
  exact ⟨w, hc, hfirst, x, hx, j, h1, h2⟩

#print axioms landing_is_first_cell_left_end

/-- **(3c) If the first cell is `[u, w]`, the cascade's landing is `u`** [L]. -/
theorem landing_eq_first_cell_left_end {v : Fin 8 → ℝ} (hv : IsArrangement v) {k : Fin 8} {m : ℝ}
    (hm : IsDmin v k m) {tStar u w : ℝ} (hr : Where.CascadeReaches (disparitySet v k) (1 / (8 * m)) tStar)
    (hc : IsCell (disparitySet v k) u w) (hfirst : ∀ u' w', IsCell (disparitySet v k) u' w' → u ≤ u') :
    tStar = u := by
  obtain ⟨w', hc', hfirst', -⟩ := landing_is_first_cell_left_end hv hm hr
  exact le_antisymm (hfirst' u w hc) (hfirst tStar w' hc')

#print axioms landing_eq_first_cell_left_end

/-- **(3d) Given a cell that is first, the cascade from the bound reaches its left end** [L].  The finiteness of the
run is `WhereProofs.cascadeFindsIsolation`, which rests on `Cascade.exists_fixed_of_lonely`, whose last step is tagged
there [PROVISIONAL: counting tool] (supports "the run from the bound is finite below a given isolation").  This is
not an existence claim: the cell is a hypothesis. -/
theorem cascade_lands_at_first_cell {v : Fin 8 → ℝ} (hv : IsArrangement v) {k : Fin 8} {m : ℝ}
    (hm : IsDmin v k m) {u w : ℝ} (hc : IsCell (disparitySet v k) u w)
    (hfirst : ∀ u' w', IsCell (disparitySet v k) u' w' → u ≤ u') :
    Where.CascadeReaches (disparitySet v k) (1 / (8 * m)) u := by
  have hl : u ∈ lonelySet (disparitySet v k) := hc.2.2.1 ⟨le_rfl, hc.2.1⟩
  have hiso : IsolatedAt v k u := (Cascade.isolatedAt_iff_lonelyAt v k u).mpr hl
  -- [PROVISIONAL: counting tool] (inside `exists_fixed_of_lonely`) supporting "the run below `u` is finite".
  obtain ⟨tStar, -, hr⟩ := WhereProofs.cascadeFindsIsolation v hv k m hm u hc.1 hiso
  have he := landing_eq_first_cell_left_end hv hm hr hc hfirst
  rw [he] at hr
  exact hr

#print axioms cascade_lands_at_first_cell

/-! ## (5) The cascade's states stay below the first cell until the final move -/

/-- **(5a) `states_below_landing`** [L]: along a cascade run from `1/(8m)` (`m ∈ ds`) to its fixed point `t⋆`, every
state is at most `t⋆`, and every state other than `t⋆` is strictly below `t⋆` and NOT lonely: the cascade visits no
cell before it lands on the left end of the first one.  (From `Fresh.Cascade`'s no overshoot and the first-ness of the
landing.) -/
theorem states_below_landing {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds)
    {seq : ℕ → ℝ} {N : ℕ} {tStar : ℝ} (h0 : seq 0 = 1 / (8 * m))
    (hmv : ∀ n, n < N → IsMove ds (seq n) (seq (n + 1))) (hN : seq N = tStar) (hfix : IsMove ds tStar tStar) :
    ∀ n, n ≤ N → seq n ≤ tStar ∧ (seq n ≠ tStar → seq n < tStar ∧ seq n ∉ lonelySet ds) := by
  have hm0 := hpos m hm
  have hb : 0 < 1 / (8 * m) := by positivity
  have hge : ∀ n, n ≤ N → 1 / (8 * m) ≤ seq n := by
    intro n
    induction n with
    | zero => intro _; rw [h0]
    | succ n ih =>
      intro hn
      exact le_trans (ih (by omega)) (Cascade.le_of_isMove hpos (hmv n (by omega)))
  -- every state lies at or below every positive lonely instant (no overshoot)
  have hbelow : ∀ s, 0 < s → Cascade.LonelyAt ds s → ∀ n, n ≤ N → seq n ≤ s := by
    intro s hs hl n
    induction n with
    | zero => intro _; rw [h0]; exact Cascade.bound_le_of_lonely hm hm0 hl hs
    | succ n ih =>
      intro hn
      exact Cascade.isMove_le_of_lonely hpos hl (ih (by omega)) (hmv n (by omega))
  have hlStar : Cascade.LonelyAt ds tStar := (Cascade.isMove_self_iff hpos).mp hfix
  have hStar0 : 0 < tStar := lt_of_lt_of_le hb (hN ▸ hge N le_rfl)
  intro n hn
  have hle := hbelow tStar hStar0 hlStar n hn
  refine ⟨hle, fun hne => ⟨lt_of_le_of_ne hle hne, fun hl => hne ?_⟩⟩
  have hsn : 0 < seq n := lt_of_lt_of_le hb (hge n hn)
  have := hbelow (seq n) hsn hl N le_rfl
  rw [hN] at this
  exact le_antisymm hle this

#print axioms states_below_landing

/-- **(5b) The setter of a forward move opens at the landing** [L]: if a move goes `t → t'` with `t' ≠ t`, its setter
`x` is in the way on all of `[t, t')`, stands at exactly `1/8` at `t'`, and `t'` is its own last opening there.  Applied
to the final move of a run, `t' = t⋆` is the left end of the first cell (`landing_is_first_cell_left_end`) and the
setter is an opener of that cell in the sense of `cell_left_end_is_opening`. -/
theorem final_setter_opens_cell {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {t t' : ℝ} (hmv : IsMove ds t t')
    (hne : t' ≠ t) :
    ∃ x ∈ ds, InWay x t ∧ t' = nextOpening x t ∧ distInt (x * t') = 1 / 8 ∧
      Localisation.lastOpening x t' = t' ∧ ∀ s, t ≤ s → s < t' → InWay x s := by
  rcases hmv with ⟨_, rfl⟩ | ⟨x, hx, hw, rfl, _⟩
  · exact absurd rfl hne
  have hx0 := hpos x hx
  refine ⟨x, hx, hw, rfl, Cascade.distInt_at_nextOpening hx0, ?_,
    fun s h1 h2 => Cascade.inWay_until_opening hx0 hw h1 h2⟩
  have hs := Dilation.setter_reading hx0 hw
  have hfl : ⌊x * nextOpening x t⌋ = Dilation.lap x t := by
    rw [hs, Int.floor_eq_iff]; constructor <;> norm_num
  unfold Localisation.lastOpening
  rw [hfl, ← Dilation.nextOpening_eq_lap hw]

#print axioms final_setter_opens_cell

/-! ## (4) Opener, closer, width, and the touch -/

/-- **(4a) The width of a cell** [L]: with opener `x` on lap `k` and closer `y` on lap `k'` (from (2)),
`w − u = (k' + 7/8)/y − (k + 1/8)/x`.  Valid for every `ds`; with two constraining runners it is the closed formula of
the two-runner case. -/
theorem cell_width {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {u w : ℝ} (h : IsCell ds u w) :
    ∃ x ∈ ds, ∃ k : ℕ, ∃ y ∈ ds, ∃ k' : ℕ, u = ((k : ℝ) + 1 / 8) / x ∧ w = ((k' : ℝ) + 7 / 8) / y ∧
      w - u = ((k' : ℝ) + 7 / 8) / y - ((k : ℝ) + 1 / 8) / x := by
  obtain ⟨x, hx, k, hu, -⟩ := cell_left_end_is_opening hpos h
  obtain ⟨y, hy, k', hw, -⟩ := cell_right_end_is_entry hpos h
  exact ⟨x, hx, k, y, hy, k', hu, hw, by rw [hu, hw]⟩

#print axioms cell_width

/-- **(4b) Non-degenerate iff the opening is not simultaneous with the entry** [L]. -/
theorem cell_nondegenerate_iff {ds : Finset ℝ} {u w x y : ℝ} {k k' : ℕ} (h : IsCell ds u w)
    (hu : u = ((k : ℝ) + 1 / 8) / x) (hw : w = ((k' : ℝ) + 7 / 8) / y) :
    u < w ↔ ((k : ℝ) + 1 / 8) / x ≠ ((k' : ℝ) + 7 / 8) / y := by
  rw [← hu, ← hw]
  exact ⟨ne_of_lt, fun hne => lt_of_le_of_ne h.2.1 hne⟩

#print axioms cell_nondegenerate_iff

/-- **(4c) When the opener is also the closer, the cell is that runner's whole window** [L]: if one runner `x ∈ ds`
stands at `k + 1/8` at `u` and at `k' + 7/8` at `w` and `[u, w]` is lonely, then `k' = k` and
`w − u = 3/(4x)`: the cell is `[(k + 1/8)/x, (k + 7/8)/x]`.  (If `k' > k`, the instant `(k+1)/x`, where `x` is at a
lap line, would lie inside the cell.) -/
theorem opener_eq_closer_window {ds : Finset ℝ} {x u w : ℝ} (hx : x ∈ ds) (hx0 : 0 < x) {k k' : ℤ}
    (hu : x * u = (k : ℝ) + 1 / 8) (hw : x * w = (k' : ℝ) + 7 / 8) (hle : u ≤ w)
    (hsub : Set.Icc u w ⊆ lonelySet ds) : k' = k ∧ w - u = 3 / (4 * x) := by
  have hxle : x * u ≤ x * w := mul_le_mul_of_nonneg_left hle hx0.le
  have hkk : k ≤ k' := by
    have : (k : ℝ) < (k' : ℝ) + 1 := by linarith
    have : k < k' + 1 := by exact_mod_cast this
    omega
  have hkeq : k' = k := by
    by_contra hne
    have hk1 : k + 1 ≤ k' := by omega
    have hk1' : (k : ℝ) + 1 ≤ (k' : ℝ) := by exact_mod_cast hk1
    set s := ((k : ℝ) + 1) / x with hsdef
    have hxs : x * s = (k : ℝ) + 1 := by rw [hsdef]; field_simp
    have hus : u ≤ s := by
      by_contra hc; push Not at hc
      have := mul_lt_mul_of_pos_left hc hx0
      linarith
    have hsw : s ≤ w := by
      by_contra hc; push Not at hc
      have := mul_lt_mul_of_pos_left hc hx0
      linarith
    have hl := hsub ⟨hus, hsw⟩ x hx
    rw [hxs] at hl
    have h0 : distInt ((k : ℝ) + 1) = 0 := by
      have := Localisation.distInt_intCast (k + 1)
      push_cast at this
      exact this
    rw [h0] at hl
    norm_num at hl
  refine ⟨hkeq, ?_⟩
  rw [hkeq] at hw
  have : x * (w - u) = 3 / 4 := by linarith
  field_simp
  linarith

#print axioms opener_eq_closer_window

/-- **(4d) In a single-point cell (a touch) the opener and the closer are different runners** [L]: one runner cannot
stand at `k + 1/8` and at `k' + 7/8` at the same instant.  So `u = w` means the exit `(k + 1/8)/x` of `x`'s zone equals
the entry `(k' + 7/8)/y` of another runner `y`'s zone: the record's touch (v9 L7). -/
theorem degenerate_opener_ne_closer {u x y : ℝ} {k k' : ℤ} (hxu : x * u = (k : ℝ) + 1 / 8)
    (hyu : y * u = (k' : ℝ) + 7 / 8) : x ≠ y := by
  rintro rfl
  have h : ((k - k' : ℤ) : ℝ) = 3 / 4 := by push_cast; linarith
  have h1 : (0 : ℝ) < ((k - k' : ℤ) : ℝ) := by rw [h]; norm_num
  have h2 : ((k - k' : ℤ) : ℝ) < 1 := by rw [h]; norm_num
  have h1' : 0 < k - k' := by exact_mod_cast h1
  have h2' : k - k' < 1 := by exact_mod_cast h2
  omega

#print axioms degenerate_opener_ne_closer

/-- **(4e) A single-point cell is an isolated point of the lonely set** [L]: its opener blocks just before and its
closer just after, so no other lonely instant lies within `min (1/(4x)) (1/(4y))`. -/
theorem degenerate_cell_isolated {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {u : ℝ} (h : IsCell ds u u) :
    ∃ δ > 0, ∀ s, |s - u| < δ → s ∈ lonelySet ds → s = u := by
  obtain ⟨x, hx, k, -, hxu, -, hbx⟩ := cell_left_end_is_opening hpos h
  obtain ⟨y, hy, k', -, hyu, -, hby⟩ := cell_right_end_is_entry hpos h
  have hx0 := hpos x hx
  have hy0 := hpos y hy
  refine ⟨min (1 / (4 * x)) (1 / (4 * y)), lt_min (by positivity) (by positivity), ?_⟩
  intro s hs hl
  have hs' := abs_lt.mp hs
  rcases lt_trichotomy s u with hlt | heq | hgt
  · exfalso
    have : u - 1 / (4 * x) < s := by linarith [min_le_left (1 / (4 * x)) (1 / (4 * y))]
    exact not_lonely_of_inWay hx (hbx s this hlt) hl
  · exact heq
  · exfalso
    have : s < u + 1 / (4 * y) := by linarith [min_le_right (1 / (4 * x)) (1 / (4 * y))]
    exact not_lonely_of_inWay hy (hby s hgt this) hl

#print axioms degenerate_cell_isolated

/-! ## The touch at the AP: the first cell is a single point -/

/-- The disparities of the AP subject at the slowest speed: `1, 2, …, 7`. -/
noncomputable def apSet : Finset ℝ := {1, 2, 3, 4, 5, 6, 7}

theorem apSet_pos : ∀ d ∈ apSet, (0 : ℝ) < d := by
  intro d hd
  simp only [apSet, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

#print axioms apSet_pos

/-- **The AP's first cell is the touch `[1/8, 1/8]`** [L]: runner `1` opens at `1/8` (it stands at `1/8`) and runner
`7` closes at `1/8` (it stands at `7/8`); the cell is a single point, it is the first cell, and the opener `1` and
closer `7` are distinct, as (4d) requires.  This is the AP's isolation instant `1/8` read as a cell. -/
theorem ap_first_cell_is_touch :
    IsCell apSet (1 / 8) (1 / 8) ∧ ∀ u' w', IsCell apSet u' w' → (1 / 8 : ℝ) ≤ u' := by
  have hl : (1 / 8 : ℝ) ∈ lonelySet apSet := by
    intro d hd
    simp only [apSet, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Localisation.clear_of_window 0 (by norm_num) (by norm_num)
  have h1 : (1 : ℝ) ∈ apSet := by simp [apSet]
  have h7 : (7 : ℝ) ∈ apSet := by simp [apSet]
  refine ⟨⟨by norm_num, le_rfl, ?_, ?_, ?_⟩, ?_⟩
  · intro s hs
    have : s = 1 / 8 := le_antisymm hs.2 hs.1
    rw [this]; exact hl
  · intro u' hu' hsub
    set s := max u' (1 / 16) with hsdef
    have hs2 : s < 1 / 8 := max_lt hu' (by norm_num)
    have hs1 : (1 / 16 : ℝ) ≤ s := le_max_right _ _
    have hw : InWay 1 s := inWay_of_near 0 (by rw [abs_lt]; push_cast; constructor <;> linarith)
    exact not_lonely_of_inWay h1 hw (hsub ⟨le_max_left _ _, hs2.le⟩)
  · intro w' hw' hsub
    set s := min w' (1 / 8 + 1 / 112) with hsdef
    have hs1 : 1 / 8 < s := lt_min hw' (by norm_num)
    have hs2 : s ≤ 1 / 8 + 1 / 112 := min_le_right _ _
    have hw : InWay 7 s := inWay_of_near 1 (by rw [abs_lt]; push_cast; constructor <;> linarith)
    exact not_lonely_of_inWay h7 hw (hsub ⟨hs1.le, min_le_left _ _⟩)
  · intro u' w' hc
    exact Cascade.bound_le_of_lonely (m := 1) h1 one_pos (hc.2.2.1 ⟨le_rfl, hc.2.1⟩) hc.1 |>.trans' (by norm_num)

#print axioms ap_first_cell_is_touch

end Fresh.LonelyCells
