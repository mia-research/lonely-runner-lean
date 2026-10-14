import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.LonelyCells
import Fresh.Carving
import Fresh.DispCell
import Fresh.NormalForm
import Fresh.RealCase
import Fresh.FourDistinct

/-!
# Coarse to fine: inserting the readings from the smallest, and what scale separation does and does not give (Task BB)

Written 2026-10-09.  Imports Mathlib and the Fresh modules named in the task; nothing from the existing `LonelyRunner`
repo.  Exact reals; every reading `x` is a positive real, every set of readings a finite set of reals.  Symbolic
statements; the exact data are in `experiments/n8/scale_hierarchy_v1.py/.out`.

Setting.  The readings of a subject are inserted into the lonely set one at a time (`Carving.lonelySet_insert`:
`lonelySet (insert x S) = lonelySet S ∩ clearSet x`).  A cell `[u, w]` of the first `k` readings is a maximal interval
of the lonely set `lonelySet S`.  The next reading `x` displaces the left end `u` to `disp x u` (`DispCell.disp`, the
least `x`-clear point at or after `u`); the cell survives iff `disp x u ≤ w` (`DispCell.survive_iff`).  The framework
splits the question in two, which is the structure studied here:

* the SCALE of `x` against the cell: a cell of length at least `1/(4x)` (a zone width of `x`) is never skipped
  (`DispCell.long_cell_survives`, "long-cell survival", LC);
* the PHASE of `x` at the cell: otherwise the cell survives iff `x` is clear at the left end `u` (CL) or an opening of
  `x` falls inside the cell (OP) (`DispCell.survives_iff_opening_or_clear`); these are arithmetic of the grid, not of scale.

Results (grades in the docstrings; each [L] theorem has its `#print axioms` line):
* (1) `cell_in_window`, `cell_length_le`, `scale_needed`: a cell of `S` lies in one clear window of EVERY `d ∈ S`, so
  its length is at most `3/(4d)`; long-cell survival by `x` therefore needs `x ≥ d/3` for every `d ∈ S`.
* (2) `longCell_iff_ratio`, `ratio_ge_third`, `scale_separation`: with `λ` the length of the cell as a fraction of the
  window `3/(4y)` of a reading `y ∈ S`, `1/(4x) ≤ length ↔ x ≥ y/(3λ)`: the exact scale `T_need = 1/(3λ) ≥ 1/3`.
* (3) the exact coarse-to-fine step: `new_cell_left`, `ret`-lemmas, `new_cell_right`, `cell_hull`, `long_cell_new_cells`,
  and the stage form `stage_insert`, `stage_step_iff`, `stage_exists_antitone`.
* (4) what is NOT covered by scale separation: `touch_cell_not_long`, `touch_survives_iff`, `clear_at_eighths_iff`,
  `touch_survives_at_eighths`, `ap6_cell_scale`, `ap6_cell_survives_not_long`, `H_cell_fails`, `survive_dichotomy`,
  `clear_left_iff_ratio`.
* (5) each hypothesis tested by dropping it: `cell_length_le_needs_mem`, `new_cell_left_needs_pos`,
  `scale_separation_needs_lt`, `clear_left_needs_pos` (counterexamples); the hypotheses found NOT REQUIRED are named in
  the docstrings (`stage_step_iff`: positivity of the earlier readings and any order; `cell_in_window`: positivity of the
  other members of `S`).

Not done here: no statement about WHICH arrangements reach which stage by which mechanism (that classification is data:
`scale_hierarchy_v1.out`), no lower bound on the longest cell of a stage (the data show none uniform in the readings: touch
cells occur), and nothing on the comparable-scale regime beyond the dichotomy `survive_dichotomy` and the grid facts
`clear_left_iff_ratio`, `clear_at_eighths_iff`.  `Fresh.NormalForm`, `Fresh.RealCase`, `Fresh.FourDistinct` are imported as
the brief names them; no declaration from them is used.

Provenance (declarations of the existing repo that correspond; none was copied, the proofs here were written for this
file): `DispCell.survive_iff`, `DispCell.long_cell_survives`, `DispCell.exists_lonely_iff_cell` are the existing
`Fresh` statements re-used as stated; the existing repo's `Spec/DoorFlank` was not used.  The window bound
`cell_in_window` follows the pattern of `Carving.cell_insert_is_piece` (its step `hw'hi`).
-/

open Classical

namespace Fresh.ScaleHierarchy

open Fresh Fresh.LonelyCells Fresh.Carving Fresh.DispCell

/-! ## (1) A cell lies in one clear window of each of its runners -/

/-- **A cell of `S` lies inside one clear window of every `d ∈ S`** [L] (NEW as a standalone statement; the same step
as `Carving.cell_insert_is_piece`, `hw'hi`).  Hypotheses: `0 < d` and `d ∈ S` REQUIRED; no hypothesis on the other
members of `S` (their positivity is NOT REQUIRED); no order of the readings is used. -/
theorem cell_in_window {S : Finset ℝ} {d u w : ℝ} (hd : 0 < d) (hdS : d ∈ S) (h : IsCell S u w) :
    ∃ N : ℤ, winLo d N ≤ u ∧ w ≤ winHi d N := by
  have hl : ∀ s ∈ Set.Icc u w, (1 / 8 : ℝ) ≤ distInt (d * s) := fun s hs => h.2.2.1 hs d hdS
  have hf := (Localisation.clear_iff_fract (d * u)).mp (hl u ⟨le_rfl, h.2.1⟩)
  unfold Int.fract at hf
  set N := ⌊d * u⌋ with hN
  have hmem : u ∈ Set.Icc (winLo d N) (winHi d N) := (mem_window_iff hd N).mpr ⟨by linarith [hf.1], by linarith [hf.2]⟩
  refine ⟨N, hmem.1, ?_⟩
  by_contra hcon
  push Not at hcon
  have hq : 0 < 1 / (8 * d) := by positivity
  have hq' : 1 / (8 * d) < 1 / (4 * d) := by
    apply one_div_lt_one_div_of_lt (by positivity); linarith
  set s := min w (winHi d N + 1 / (8 * d)) with hsdef
  have hs1 : winHi d N < s := lt_min hcon (by linarith)
  have hs2 : s < winHi d N + 1 / (4 * d) := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hw := inWay_after_entry hd (mul_winHi hd N) hs1 hs2
  exact Cascade.not_inWay_iff.mpr (hl s ⟨le_trans hmem.2 hs1.le, min_le_left _ _⟩) hw

#print axioms cell_in_window

/-- **A cell has length at most the window of each of its runners** [L] (NEW): `w - u ≤ 3/(4d)` for every `d ∈ S`.
Hypotheses as in `cell_in_window`. -/
theorem cell_length_le {S : Finset ℝ} {d u w : ℝ} (hd : 0 < d) (hdS : d ∈ S) (h : IsCell S u w) :
    w - u ≤ 3 / (4 * d) := by
  obtain ⟨N, h1, h2⟩ := cell_in_window hd hdS h
  have := window_length hd N
  linarith

#print axioms cell_length_le

/-- **Long-cell survival by `x` needs `x ≥ d/3` for every `d ∈ S`** [L] (NEW).  If a cell of `S` has length at least
`1/(4x)` (so that `DispCell.long_cell_survives` applies) then `d ≤ 3x` for every `d ∈ S`.  So the readings smaller than
a third of the largest member can never be inserted by long-cell survival; a reading at least the largest member
satisfies this necessary condition for free.  `0 < x`, `0 < d` REQUIRED; the order of insertion NOT REQUIRED. -/
theorem scale_needed {S : Finset ℝ} {x d u w : ℝ} (hx : 0 < x) (hd : 0 < d) (hdS : d ∈ S) (h : IsCell S u w)
    (hlong : 1 / (4 * x) ≤ w - u) : d ≤ 3 * x := by
  have h1 := cell_length_le hd hdS h
  have h2 : 1 / (4 * x) ≤ 3 / (4 * d) := le_trans hlong h1
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at h2
  nlinarith

#print axioms scale_needed

/-! ## (2) The exact scale at which a cell becomes long -/

/-- **The exact scale of long-cell survival** [L] (NEW).  A cell of length `ℓ = 3 λ/(4 y)` (`λ` its length as a
fraction of the window `3/(4y)` of the reading `y`) is long for `x` iff `x ≥ y/(3 λ)`.  `0 < x`, `0 < y`, `0 < λ`
REQUIRED (each is used to clear a denominator). -/
theorem longCell_iff_ratio {x y lam : ℝ} (hx : 0 < x) (hy : 0 < y) (hl : 0 < lam) :
    1 / (4 * x) ≤ 3 * lam / (4 * y) ↔ y / (3 * lam) ≤ x := by
  rw [div_le_div_iff₀ (by positivity) (by positivity), div_le_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

#print axioms longCell_iff_ratio

/-- **The fraction `λ` of a cell is at most `1`, so the scale needed is at least `1/3`** [L] (NEW): for a cell `[u, w]`
of `S` and `y ∈ S`, `λ = 4 y (w - u)/3 ≤ 1`, hence `x ≥ y/(3λ) ≥ y/3`. -/
theorem ratio_ge_third {S : Finset ℝ} {y u w : ℝ} (hy : 0 < y) (hyS : y ∈ S) (h : IsCell S u w) :
    4 * y * (w - u) / 3 ≤ 1 := by
  have h1 := cell_length_le hy hyS h
  have h2 : (w - u) * (4 * y) ≤ 3 := by
    have := (le_div_iff₀ (show (0 : ℝ) < 4 * y by positivity)).mp h1
    exact this
  nlinarith

#print axioms ratio_ge_third

/-- **Scale separation, exact** [L] (NEW).  For a cell `[u, w]` of `S` with `u < w`, a reading `y ∈ S` and
`λ := 4 y (w - u)/3` (a number in `(0, 1]`), the cell is long for `x` iff `x ≥ y/(3λ)`: the scale `T_need = 1/(3λ)`
times `y`.  Both directions; no order of the readings and no integrality; `[PROVISIONAL: covering]` at this step: a
cell length against a zone width, supporting only the statement `x ≥ T_need·y ⇒ the cell survives`, which asserts
no existence. -/
theorem scale_separation {S : Finset ℝ} {x y u w : ℝ} (hx : 0 < x) (hy : 0 < y) (hyS : y ∈ S) (h : IsCell S u w)
    (huw : u < w) :
    (1 / (4 * x) ≤ w - u ↔ y / (3 * (4 * y * (w - u) / 3)) ≤ x) ∧ 0 < 4 * y * (w - u) / 3 ∧
      4 * y * (w - u) / 3 ≤ 1 := by
  have hpos : 0 < 4 * y * (w - u) / 3 := by
    have : 0 < w - u := by linarith
    positivity
  refine ⟨?_, hpos, ratio_ge_third hy hyS h⟩
  have e : w - u = 3 * (4 * y * (w - u) / 3) / (4 * y) := by field_simp
  conv_lhs => rw [e]
  exact longCell_iff_ratio hx hy hpos

#print axioms scale_separation

/-- **Consequence: a cell survives by length once `x ≥ y/(3λ)`** [L] (NEW; `scale_separation` with
`DispCell.long_cell_survives`).  `[PROVISIONAL: covering]` as in `scale_separation`. -/
theorem survives_of_scale {S : Finset ℝ} {x y u w : ℝ} (hx : 0 < x) (hy : 0 < y) (hyS : y ∈ S) (h : IsCell S u w)
    (huw : u < w) (hscale : y / (3 * (4 * y * (w - u) / 3)) ≤ x) :
    disp x u < w ∧ ∃ s ∈ Set.Icc u w, s ∈ lonelySet (insert x S) := by
  have hlong := ((scale_separation hx hy hyS h huw).1).mpr hscale
  exact long_cell_survives hx h.2.2.1 hlong

#print axioms survives_of_scale

/-! ## (3) The exact coarse-to-fine step -/

/-- **The leftmost new cell begins exactly at the displaced end** [L] (NEW; `Carving.piece_isCell` with the
characterisation `DispCell.disp_le_of_clear`).  If `[u, w]` is a cell of `S` and `disp x u ≤ w`, then
`[disp x u, min w (winHi x N)]` is a cell of `insert x S`, where `N = ⌊x · disp x u⌋` is the lap of the displaced end.
No positivity of the members of `S` and no nonemptiness is needed; `0 < x` REQUIRED. -/
theorem new_cell_left {S : Finset ℝ} {x u w : ℝ} (hx : 0 < x) (h : IsCell S u w) (hd : disp x u ≤ w) :
    ∃ N : ℤ, winLo x N ≤ disp x u ∧ disp x u ≤ min w (winHi x N) ∧
      IsCell (insert x S) (disp x u) (min w (winHi x N)) := by
  set p := disp x u with hp
  have hcl := clear_disp hx u
  rw [← hp] at hcl
  have hf := (Localisation.clear_iff_fract (x * p)).mp hcl
  unfold Int.fract at hf
  set N := ⌊x * p⌋ with hN
  have hmem : p ∈ Set.Icc (winLo x N) (winHi x N) := (mem_window_iff hx N).mpr ⟨by linarith [hf.1], by linarith [hf.2]⟩
  have hup : u ≤ p := le_disp hx u
  have hle : max u (winLo x N) ≤ min w (winHi x N) :=
    max_le (le_min (hup.trans hd) (hup.trans hmem.2)) (le_min (hmem.1.trans hd) (hmem.1.trans hmem.2))
  have hcell := piece_isCell hx h hle
  have hmax : max u (winLo x N) = p := by
    apply le_antisymm (max_le hup hmem.1)
    have hq := piece_subset hx h N ⟨le_rfl, hle⟩
    rw [lonelySet_insert] at hq
    exact disp_le_of_clear hx (le_max_left _ _) hq.2
  rw [hmax] at hcell
  exact ⟨N, hmem.1, le_min hd hmem.2, hcell⟩


#print axioms new_cell_left

/-- **The right end of the leftmost new cell** [L] (NEW): it is `w` (the old right end) or an entry of `x`
(`x e = N + 7/8`).  So the new cell is `[disp x u, w]` of length `w - u - displacement x u > (w - u) - 1/(4x)` whenever
the cell fits in the window of `x` that holds the displaced end, and otherwise ends at an entry of `x` inside the old
cell. -/
theorem new_cell_left_shape {S : Finset ℝ} {x u w : ℝ} (hx : 0 < x) (h : IsCell S u w) (hd : disp x u ≤ w) :
    ∃ e : ℝ, IsCell (insert x S) (disp x u) e ∧ e ≤ w ∧ (e = w ∨ ∃ N : ℤ, x * e = (N : ℝ) + 7 / 8) ∧
      (e = w → (w - u) - 1 / (4 * x) < e - disp x u) := by
  obtain ⟨N, -, -, hc⟩ := new_cell_left hx h hd
  refine ⟨min w (winHi x N), hc, min_le_left _ _, ?_, ?_⟩
  · rcases min_choice w (winHi x N) with e | e
    · exact Or.inl e
    · exact Or.inr ⟨N, by rw [e]; exact mul_winHi hx N⟩
  · intro he
    have := disp_lt hx u
    rw [he]; linarith

#print axioms new_cell_left_shape

/-! ### The mirror: the retreated right end -/

/-- The retreated right end of `w` under `x`: the greatest `x`-clear point at or before `w` (the mirror image of
`DispCell.disp`, `t ↦ -t`). -/
noncomputable def ret (x w : ℝ) : ℝ := - disp x (-w)

theorem ret_le {x : ℝ} (hx : 0 < x) (w : ℝ) : ret x w ≤ w := by
  unfold ret; linarith [le_disp hx (-w)]

#print axioms ret_le

theorem clear_ret {x : ℝ} (hx : 0 < x) (w : ℝ) : (1 / 8 : ℝ) ≤ distInt (x * ret x w) := by
  unfold ret
  have := clear_disp hx (-w)
  rw [mul_neg, Cascade.distInt_neg]
  exact this

#print axioms clear_ret

theorem le_ret_of_clear {x s w : ℝ} (hx : 0 < x) (hsw : s ≤ w) (hs : (1 / 8 : ℝ) ≤ distInt (x * s)) :
    s ≤ ret x w := by
  unfold ret
  have := disp_le_of_clear hx (a := -w) (s := -s) (by linarith) (by rw [mul_neg, Cascade.distInt_neg]; exact hs)
  linarith

#print axioms le_ret_of_clear

/-- **The retreat is below the zone width** [L] (NEW): `w - 1/(4x) < ret x w`. -/
theorem ret_gt {x : ℝ} (hx : 0 < x) (w : ℝ) : w - 1 / (4 * x) < ret x w := by
  unfold ret
  have := disp_lt hx (-w)
  linarith

#print axioms ret_gt

/-- **The rightmost new cell ends exactly at the retreated end** [L] (NEW, mirror of `new_cell_left`).  If `[u, w]` is a
cell of `S` and `disp x u ≤ w` then `[max u (winLo x N), ret x w]` is a cell of `insert x S`, `N = ⌊x · ret x w⌋`.
`0 < x` REQUIRED; nothing on `S`. -/
theorem new_cell_right {S : Finset ℝ} {x u w : ℝ} (hx : 0 < x) (h : IsCell S u w) (hd : disp x u ≤ w) :
    ∃ N : ℤ, winLo x N ≤ ret x w ∧ max u (winLo x N) ≤ ret x w ∧
      IsCell (insert x S) (max u (winLo x N)) (ret x w) := by
  set p := ret x w with hp
  have hcl := clear_ret hx w
  rw [← hp] at hcl
  have hf := (Localisation.clear_iff_fract (x * p)).mp hcl
  unfold Int.fract at hf
  set N := ⌊x * p⌋ with hN
  have hmem : p ∈ Set.Icc (winLo x N) (winHi x N) :=
    (mem_window_iff hx N).mpr ⟨by linarith [hf.1], by linarith [hf.2]⟩
  have hpw : p ≤ w := ret_le hx w
  have hup : u ≤ p := le_trans (le_disp hx u) (le_ret_of_clear hx hd (clear_disp hx u))
  have hle : max u (winLo x N) ≤ min w (winHi x N) :=
    max_le (le_min (hup.trans hpw) (hup.trans hmem.2)) (le_min (hmem.1.trans hpw) (hmem.1.trans hmem.2))
  have hcell := piece_isCell hx h hle
  have hmin : min w (winHi x N) = p := by
    apply le_antisymm
    · have hq := piece_subset hx h N ⟨hle, le_rfl⟩
      rw [lonelySet_insert] at hq
      exact le_ret_of_clear hx (min_le_left _ _) hq.2
    · exact le_min hpw hmem.2
  rw [hmin] at hcell hle
  exact ⟨N, hmem.1, hle, hcell⟩

#print axioms new_cell_right

/-- **The hull of the survivors** [L] (NEW).  If `[u, w]` is a cell of `S` and `x` is positive then, when the cell
survives (`disp x u ≤ w`): the displaced left end and the retreated right end each move by less than the zone width
`1/(4x)`, the hull `[disp x u, ret x w]` lies in `[u, w]` and has length greater than `(w - u) - 1/(2x)`, a cell of
`insert x S` begins at `disp x u` and a cell of `insert x S` ends at `ret x w`.  This is the cell shape of a
coarse-to-fine step. -/
theorem cell_hull {S : Finset ℝ} {x u w : ℝ} (hx : 0 < x) (h : IsCell S u w) (hd : disp x u ≤ w) :
    u ≤ disp x u ∧ disp x u - u < 1 / (4 * x) ∧ disp x u ≤ ret x w ∧ ret x w ≤ w ∧ w - ret x w < 1 / (4 * x) ∧
      (w - u) - 1 / (2 * x) < ret x w - disp x u ∧
      (∃ e, IsCell (insert x S) (disp x u) e ∧ e ≤ w) ∧ (∃ b, IsCell (insert x S) b (ret x w) ∧ u ≤ b) := by
  have h1 := disp_lt hx u
  have h2 := ret_gt hx w
  have e : 1 / (2 * x) = 1 / (4 * x) + 1 / (4 * x) := by field_simp; ring
  refine ⟨le_disp hx u, by linarith, le_ret_of_clear hx hd (clear_disp hx u), ret_le hx w, by linarith,
    by rw [e]; linarith, ?_, ?_⟩
  · obtain ⟨N, -, -, hc⟩ := new_cell_left hx h hd
    exact ⟨_, hc, min_le_left _ _⟩
  · obtain ⟨N, -, -, hc⟩ := new_cell_right hx h hd
    exact ⟨_, hc, le_max_left _ _⟩

#print axioms cell_hull

/-- **A long cell leaves cells at both ends** [L] (NEW; `cell_hull` with `DispCell.long_cell_survives`).  If a cell of
`S` has length at least `1/(4x)` then `insert x S` has a cell starting in `[u, u + 1/(4x))` and a cell ending in
`(w - 1/(4x), w]`, both inside `[u, w]`.  This is the scale-separation lemma: the long cell is not skipped and each end
moves by less than a zone width.  `[PROVISIONAL: covering]` at this step: a cell length against a zone width;
supports the shape statement and asserts no existence. -/
theorem long_cell_new_cells {S : Finset ℝ} {x u w : ℝ} (hx : 0 < x) (h : IsCell S u w) (hlong : 1 / (4 * x) ≤ w - u) :
    (∃ a e, IsCell (insert x S) a e ∧ u ≤ a ∧ a < u + 1 / (4 * x) ∧ e ≤ w) ∧
      (∃ b f, IsCell (insert x S) b f ∧ w - 1 / (4 * x) < f ∧ f ≤ w ∧ u ≤ b) := by
  have hd : disp x u ≤ w := (long_cell_survives hx h.2.2.1 hlong).1.le
  obtain ⟨h1, h2, -, h4, h5, -, ⟨e, he, hew⟩, ⟨b, hb, hub⟩⟩ := cell_hull hx h hd
  exact ⟨⟨_, e, he, h1, by linarith, hew⟩, ⟨b, _, hb, by linarith, h4, hub⟩⟩

#print axioms long_cell_new_cells

/-! ### The stage form: readings inserted one at a time -/

/-- The set of the first `k` readings `r 0, …, r (k-1)`. -/
noncomputable def stageSet (r : ℕ → ℝ) (k : ℕ) : Finset ℝ := (Finset.range k).image r

theorem stage_insert (r : ℕ → ℝ) (k : ℕ) : stageSet r (k + 1) = insert (r k) (stageSet r k) := by
  unfold stageSet
  rw [Finset.range_add_one, Finset.image_insert]

#print axioms stage_insert

theorem stage_pos {r : ℕ → ℝ} (hr : ∀ i, 0 < r i) (k : ℕ) : ∀ d ∈ stageSet r k, 0 < d := by
  intro d hd
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hd
  exact hr i

theorem stage_nonempty (r : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k) : (stageSet r k).Nonempty :=
  ⟨r 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩

/-- **The exact coarse-to-fine step** [L] (NEW as a stage statement; `DispCell.exists_lonely_iff_cell_general` for
`S = stageSet r k`, `x = r k`).  A positive lonely instant exists for the first `k + 1` readings iff some cell
`[u, w]` of the first `k` readings has displaced left end `disp (r k) u ≤ w`.  Hypotheses: `0 < r k` REQUIRED (for
`r k < 0` the displaced end `disp` leaves the positive axis: `new_cell_left_needs_pos`), `1 ≤ k` REQUIRED
(`DispCell.exists_iff_fails_empty`).  NOT REQUIRED: positivity (or non-vanishing) of the earlier readings, and any
order, distinctness or integrality of the readings: the order of insertion is not used. -/
theorem stage_step_iff {r : ℕ → ℝ} {k : ℕ} (hk : 1 ≤ k) (hrk : 0 < r k) :
    (∃ t : ℝ, 0 < t ∧ t ∈ lonelySet (stageSet r (k + 1))) ↔
      ∃ u w, IsCell (stageSet r k) u w ∧ disp (r k) u ≤ w := by
  rw [stage_insert, exists_lonely_iff_cell_general (stage_nonempty r hk) hrk.ne', abs_of_pos hrk]

#print axioms stage_step_iff

/-- **Existence passes down the stages** [L] (NEW): if the first `k` readings have a lonely instant then so do the
first `j ≤ k`.  (Nothing is claimed upward: that is `stage_step_iff`.) -/
theorem stage_exists_antitone (r : ℕ → ℝ) {j k : ℕ} (hjk : j ≤ k) {t : ℝ} (ht : t ∈ lonelySet (stageSet r k)) :
    t ∈ lonelySet (stageSet r j) := by
  intro d hd
  apply ht
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hjk), rfl⟩

#print axioms stage_exists_antitone

/-- **The stage step with long-cell survival** [L] (NEW): if a cell of the first `k` readings has length at least
`1/(4 · r k)` then the first `k + 1` readings have a lonely instant, namely `disp (r k) u`, inside
`[u, u + 1/(4 r k))`.  `0 < r k` REQUIRED; positivity of the earlier readings and the order NOT REQUIRED; `1 ≤ k` is automatic from the cell.
`[PROVISIONAL: covering]` at this step (a cell length against a zone width); the premise (a long cell exists) is the
content owed and is not asserted. -/
theorem stage_step_of_long {r : ℕ → ℝ} {k : ℕ} (hrk : 0 < r k) {u w : ℝ} (h : IsCell (stageSet r k) u w)
    (hlong : 1 / (4 * r k) ≤ w - u) :
    disp (r k) u ∈ lonelySet (stageSet r (k + 1)) ∧ u ≤ disp (r k) u ∧ disp (r k) u < u + 1 / (4 * r k) := by
  have hx := hrk
  have hd : disp (r k) u ≤ w := (long_cell_survives hx h.2.2.1 hlong).1.le
  refine ⟨?_, le_disp hx u, disp_lt hx u⟩
  rw [stage_insert, lonelySet_insert, ← lonelySet_singleton]
  exact ⟨h.2.2.1 ⟨le_disp hx u, hd⟩, Fresh.BlockLanding.mem_lonelySet_singleton.mpr (clear_disp hx u)⟩

#print axioms stage_step_of_long

/-! ## (4) What scale separation does not cover -/

/-- **A touch cell is never long** [L] (NEW): a cell of length `0` is not long for any `x > 0`; no scale `T_need`
exists.  It survives iff `x` is clear at it (`touch_survives_iff`). -/
theorem touch_cell_not_long {x u : ℝ} (hx : 0 < x) : ¬ (1 / (4 * x) ≤ u - u) := by
  have : 0 < 1 / (4 * x) := by positivity
  intro h; linarith

#print axioms touch_cell_not_long

theorem touch_survives_iff {x u : ℝ} (hx : 0 < x) : disp x u ≤ u ↔ (1 / 8 : ℝ) ≤ distInt (x * u) := by
  rw [← disp_eq_self_iff hx u]
  exact ⟨fun h => le_antisymm h (le_disp hx u), fun h => h.le⟩

#print axioms touch_survives_iff

/-- **Survival without length is a dichotomy** [L] (NEW; `DispCell.survives_iff_opening_or_clear`): a cell survives iff
`x` is clear at its left end or an opening of `x` lies inside it; both are statements about the phase of `x`, none about
its scale. -/
theorem survive_dichotomy {S : Finset ℝ} {x u w : ℝ} (hx : 0 < x) (h : IsCell S u w) :
    disp x u ≤ w ↔ (1 / 8 : ℝ) ≤ distInt (x * u) ∨ ∃ N : ℤ, u ≤ winLo x N ∧ winLo x N ≤ w := by
  rw [survives_iff_opening_or_clear hx]
  constructor
  · rintro (⟨hc, -⟩ | ho)
    · exact Or.inl hc
    · exact Or.inr ho
  · rintro (hc | ho)
    · exact Or.inl ⟨hc, h.2.1⟩
    · exact Or.inr ho

#print axioms survive_dichotomy

/-- **The left end is an opening of a member, so clear-left is a ratio condition** [L] (NEW): the left end of a cell
is `(k + 1/8)/y` for some `y ∈ S`, and `x` is clear there iff `‖(x/y)(k + 1/8)‖ ≥ 1/8`: it depends on the ratio
`x / y` and the lap `k` only, not on the scale of `x` and `y` separately.  Positivity of the members of `S` REQUIRED
(it is used by `cell_left_end_is_opening`). -/
theorem clear_left_iff_ratio {S : Finset ℝ} (hpos : ∀ d ∈ S, 0 < d) {x u w : ℝ} (h : IsCell S u w) :
    ∃ y ∈ S, ∃ k : ℕ, u = ((k : ℝ) + 1 / 8) / y ∧
      ((1 / 8 : ℝ) ≤ distInt (x * u) ↔ (1 / 8 : ℝ) ≤ distInt ((x / y) * ((k : ℝ) + 1 / 8))) := by
  obtain ⟨y, hy, k, hu, -, -, -⟩ := cell_left_end_is_opening hpos h
  refine ⟨y, hy, k, hu, ?_⟩
  have hy0 := hpos y hy
  have e : x * u = (x / y) * ((k : ℝ) + 1 / 8) := by rw [hu]; field_simp
  rw [e]

#print axioms clear_left_iff_ratio

/-- The AP cell of `{1, …, 6}`: `[1/8, 7/48]` (`Carving.ap_first_cell_carving`). -/
theorem ap6_cell : IsCell (apPrefix 6) (1 / 8) (7 / 48) := by
  have := ap_first_cell_carving 6 (by norm_num) (by norm_num)
  norm_num at this
  exact this

#print axioms ap6_cell

/-- **The AP cell of the first six readings becomes long exactly at `x = 12`** [L] (NEW): its length is `1/48`, so it is
long for `x` iff `x ≥ 12`, i.e. `x/6 ≥ 2`: `T_need = 2` against the top reading `6`. -/
theorem ap6_cell_scale {x : ℝ} (hx : 0 < x) : 1 / (4 * x) ≤ 7 / 48 - 1 / 8 ↔ 12 ≤ x := by
  rw [div_le_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

#print axioms ap6_cell_scale

/-- **The reading `7` survives the AP cell of `{1, …, 6}` without being long, by being clear at its left end** [L]
(NEW): `7` is far below the scale `12` needed, `7/6` is comparable to `6`, and the cell survives because
`‖7 · 1/8‖ = 1/8` (clear-left, no length).  The result is the touch cell `[1/8, 1/8]` of the AP (`ap_touch_by_carving`).
This is the case scale separation does not cover. -/
theorem ap6_cell_survives_not_long :
    ¬ (1 / (4 * (7 : ℝ)) ≤ 7 / 48 - 1 / 8) ∧ disp 7 (1 / 8) = 1 / 8 ∧ disp 7 (1 / 8) ≤ 7 / 48 ∧
      IsCell (insert (7 : ℝ) (apPrefix 6)) (1 / 8) (1 / 8) := by
  have hc : (1 / 8 : ℝ) ≤ distInt (7 * (1 / 8)) := by
    apply Localisation.clear_of_window 0 <;> norm_num
  have hdisp : disp 7 (1 / 8) = 1 / 8 := (disp_eq_self_iff (by norm_num) _).mpr hc
  refine ⟨fun h => ?_, hdisp, by rw [hdisp]; norm_num, ?_⟩
  · have := (ap6_cell_scale (x := 7) (by norm_num)).mp h
    norm_num at this
  · have h7 := apPrefix_succ 6
    have h7' := ap_touch_by_carving
    norm_num at h7
    rw [← h7]
    exact h7'.1 ▸ h7'.2

#print axioms ap6_cell_survives_not_long

/-- **The cell-level scale hypothesis `x ≥ T y ⇒ long` fails for every `0 < T < 2`** [L] (NEW; a counterexample, not a
patched hypothesis): for the cell `[1/8, 7/48]` of `{1, …, 6}` with `y = 6`, the reading `x = 3T + 6` satisfies
`T y ≤ x < 12` and the cell is not long for it.  The reason is the exact scale `T_need = 2` of `ap6_cell_scale`: the
cell is `1/48` long, `λ = 1/6` of the window `3/(4·6)`.  Cell level only: the data of `scale_hierarchy_v1.out` test the
window level (some cell long). -/
theorem H_cell_fails {T : ℝ} (hT0 : 0 < T) (hT : T < 2) :
    ∃ x : ℝ, 0 < x ∧ T * 6 ≤ x ∧ ¬ (1 / (4 * x) ≤ 7 / 48 - 1 / 8) := by
  refine ⟨3 * T + 6, by linarith, by linarith, fun h => ?_⟩
  have := (ap6_cell_scale (x := 3 * T + 6) (by linarith)).mp h
  linarith

#print axioms H_cell_fails


/-- **At a whole number of eighths the quotient is invisible** [L] (NEW; `Fresh.distInt_int_div_eight` and
`Fresh.distInt_int_div_eight_of_dvd`): `x` is clear at an instant `u` with `x u = M/8`, `M` an integer, iff `8 ∤ M`.
Only `M mod 8` matters, not the size of `x` or of `u`.  This is the grid handling the scale at the touch cells
(`scale_hierarchy_v1.out`, the touch cells at the integer instants `R = 9, 15`). -/
theorem clear_at_eighths_iff (M : ℤ) : (1 / 8 : ℝ) ≤ distInt ((M : ℝ) / 8) ↔ ¬ (8 : ℤ) ∣ M := by
  constructor
  · intro h h8
    rw [Fresh.distInt_int_div_eight_of_dvd h8] at h
    norm_num at h
  · exact Fresh.distInt_int_div_eight

#print axioms clear_at_eighths_iff

/-- **A touch cell at a whole number of eighths survives a reading iff the reading's numerator is not a multiple of
`8`** [L] (NEW): if `x u = M/8` then `disp x u ≤ u` iff `8 ∤ M`.  Any positive `x` with `x u = M/8` behaves as its
residue `M mod 8`: the scale of `x` is not seen. -/
theorem touch_survives_at_eighths {x u : ℝ} (hx : 0 < x) {M : ℤ} (hM : x * u = (M : ℝ) / 8) :
    disp x u ≤ u ↔ ¬ (8 : ℤ) ∣ M := by
  rw [touch_survives_iff hx, hM]
  exact clear_at_eighths_iff M

#print axioms touch_survives_at_eighths

/-! ## (5) The hypotheses tested: counterexamples when one is dropped -/

/-- `IsCell` depends on the set of readings only through its lonely set. -/
theorem isCell_congr {ds ds' : Finset ℝ} (h : lonelySet ds = lonelySet ds') (u w : ℝ) : IsCell ds u w ↔ IsCell ds' u w := by
  unfold IsCell; rw [h]

/-- **`d ∈ S` is REQUIRED in `cell_length_le`** [L] (counterexample): `[1/8, 7/8]` is a cell of `{1}` and has length
`3/4`, more than the window `3/32` of `d = 8 ∉ {1}`.  The window bound is a fact about the members of `S`, not about
every reading. -/
theorem cell_length_le_needs_mem :
    ∃ (S : Finset ℝ) (d u w : ℝ), IsCell S u w ∧ 0 < d ∧ d ∉ S ∧ ¬ (w - u ≤ 3 / (4 * d)) := by
  refine ⟨{1}, 8, 1 / 8, 7 / 8, ?_, by norm_num, by simp, by norm_num⟩
  have := window_isCell (d := 1) (by norm_num) 0
  unfold winLo winHi at this
  norm_num at this
  exact this

#print axioms cell_length_le_needs_mem

/-- **`0 < x` is REQUIRED in `new_cell_left`** [L] (counterexample): for `S = {2}` (cell `[1/16, 7/16]`) and `x = -1`
the displaced end is `-1/8`, outside the positive axis, so no cell of `insert x S` begins there. -/
theorem new_cell_left_needs_pos :
    ∃ (S : Finset ℝ) (x u w : ℝ), IsCell S u w ∧ x < 0 ∧ disp x u ≤ w ∧
      ∀ N : ℤ, ¬ IsCell (insert x S) (disp x u) (min w (winHi x N)) := by
  have hc : IsCell ({2} : Finset ℝ) (1 / 16) (7 / 16) := by
    have := window_isCell (d := 2) (by norm_num) 0
    unfold winLo winHi at this
    norm_num at this
    exact this
  have hdisp : disp (-1) (1 / 16) = -1 / 8 := by
    have := disp_of_near (x := -1) (a := 1 / 16) (k := 0) (by norm_num)
    rw [this]; norm_num
  refine ⟨{2}, -1, 1 / 16, 7 / 16, hc, by norm_num, by rw [hdisp]; norm_num, fun N hN => ?_⟩
  have := hN.1
  rw [hdisp] at this
  norm_num at this

#print axioms new_cell_left_needs_pos

/-- **`u < w` is REQUIRED in `scale_separation`** [L] (counterexample): for a touch cell (`u = w`, `λ = 0`) the
right side `y/(3·0) ≤ x` holds by division by zero while the left side `1/(4x) ≤ 0` is false (`touch_cell_not_long`);
the correct statement for a touch is `touch_cell_not_long`: no scale makes it long. -/
theorem scale_separation_needs_lt {x y u : ℝ} (hx : 0 < x) :
    ¬ (1 / (4 * x) ≤ u - u ↔ y / (3 * (4 * y * (u - u) / 3)) ≤ x) := by
  intro h
  have h1 := h.mpr (by simp [hx.le])
  exact touch_cell_not_long hx h1

#print axioms scale_separation_needs_lt

/-- **Positivity of the members of `S` is REQUIRED in `clear_left_iff_ratio`** [L] (counterexample): `S = {-1}` has the
cell `[1/8, 7/8]` (`clearSet (-1) = clearSet 1`), and no `y ∈ S`, `k ∈ ℕ` has `1/8 = (k + 1/8)/y`. -/
theorem clear_left_needs_pos :
    ∃ (S : Finset ℝ) (u w : ℝ), IsCell S u w ∧ ¬ ∃ y ∈ S, ∃ k : ℕ, u = ((k : ℝ) + 1 / 8) / y := by
  have hset : lonelySet ({-1} : Finset ℝ) = lonelySet ({1} : Finset ℝ) := by
    rw [lonelySet_singleton, lonelySet_singleton]
    have := clearSet_abs (-1)
    simpa using this.symm
  have hc : IsCell ({1} : Finset ℝ) (1 / 8) (7 / 8) := by
    have := window_isCell (d := 1) (by norm_num) 0
    unfold winLo winHi at this
    norm_num at this
    exact this
  refine ⟨{-1}, 1 / 8, 7 / 8, (isCell_congr hset _ _).mpr hc, ?_⟩
  rintro ⟨y, hy, k, hk⟩
  rw [Finset.mem_singleton] at hy
  subst hy
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  norm_num at hk
  linarith

#print axioms clear_left_needs_pos

end Fresh.ScaleHierarchy
