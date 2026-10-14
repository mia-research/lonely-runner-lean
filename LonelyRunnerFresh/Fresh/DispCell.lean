import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.LonelyCells
import Fresh.Carving
import Fresh.BlockLanding
import Fresh.BlockLanding2
import Fresh.TwoScale
import Fresh.OneMultiple

/-!
# The displacement of a cell by one added runner (Task AV)

Written 2026-10-09.  Imports Mathlib and the Fresh modules named in the task.  Nothing is imported from the existing
`LonelyRunner` repo.  Exact reals; the added runner `x` is an arbitrary positive real (the multiple `8c` of the integer
case is the instance `x = 8c`), `S` an arbitrary finite set of reals.  Every statement is symbolic.

Objects.  `disp x a` is the DISPLACED END of `a` under `x`: `a` itself if `x` is clear at `a`, else the next opening of
`x` after `a`.  In the integer case with `s = 8t`, `disp (8c) (x/8)` is the `w_c(x)` of the brief
(`ceil(c x - 1/8) + 1/8)/c`).  `displacement x a = disp x a - a`.

Results (grade [L] = compiled by `check.sh`, with the `#print axioms` line after each theorem):
* displacement law: `isClearFirst_disp` (`disp x a` is the least `x`-clear point at or after `a`), `disp_lt`
  (`displacement < 1/(4x)`), `disp_eq_self_iff`, `disp_of_near`, `mul_displacement` (`x * displacement = k + 1/8 - x a`);
* long cell: `not_subset_zone_of_long`, `long_cell_not_covered`, `long_cell_clear_point` (a clear point already in
  `[a, a + 1/(4x))`), sharpness `short_fits_in_zone`;
* cell level: `survive_iff` (`[u,w]` has a point lonely for `insert x S` iff `disp x u <= w`), `skipped_iff`,
  `skipped_iff_zone`, `skipped_lt_zone_width`;
* existence consequence: `exists_lonely_iff_cell`, `exists_lonely_iff_displacement_le_length`,
  `landing_iff_disp`, and the sign/zero reductions `exists_lonely_iff_cell_general`;
* exact mechanism: `survives_iff_opening_or_clear` (a cell survives iff the left end is clear for `x` or an opening of
  `x` falls inside the cell), `mul_displacement`, `survives_of_phase`, `survives_of_opener`, `survives_of_small_opener`,
  `displacement_of_integer_phase`.

Provenance.  Corresponds to `Fresh.BlockLanding` (`clearFirst_single_clear`, `clearFirst_single_inWay`, `nextOpening_lt`,
`not_typeX_of_wide`, `typeX_single_iff`, `single_block_landing`), `Fresh.BlockLanding2` (`landing_iff_first_open_cell`),
`Fresh.Carving` (`killed_iff`, `cell_killed_iff`, `survives_of_wide`, `cell_survives_of_wide`).  Those are reused
as stated; the new statements here are marked NEW in the docstring.  The existing repo's `Spec/DoorFlank` was not used.
-/

open Classical

namespace Fresh.DispCell

open Fresh Fresh.LonelyCells Fresh.Carving Fresh.BlockLanding Fresh.BlockLanding2

/-! ## (1) The displacement law of one added runner at a point -/

/-- The displaced end of `a` under the runner `x`: `a` if `x` is clear there, else `x`'s next opening. -/
noncomputable def disp (x a : ℝ) : ℝ := if InWay x a then nextOpening x a else a

/-- The displacement of `a` under `x`. -/
noncomputable def displacement (x a : ℝ) : ℝ := disp x a - a

/-- **The displaced end is the least `x`-clear point at or after `a`** [L] (NEW as one statement; the two cases are
`BlockLanding.clearFirst_single_clear` and `clearFirst_single_inWay`).  Hypothesis `0 < x`: REQUIRED (for `x = 0` no
point is clear, `lonelySet {0} = ∅`; see `isClearFirst_zero_false`). -/
theorem isClearFirst_disp {x : ℝ} (hx : 0 < x) (a : ℝ) : IsClearFirst {x} a (disp x a) := by
  unfold disp
  split_ifs with h
  · exact clearFirst_single_inWay hx h
  · exact clearFirst_single_clear (Cascade.not_inWay_iff.mp h)

#print axioms isClearFirst_disp

theorem isClearFirst_zero_false (a u : ℝ) : ¬ IsClearFirst ({0} : Finset ℝ) a u := by
  intro h
  have := mem_lonelySet_singleton.mp h.1.2
  simp [distInt] at this
  linarith

#print axioms isClearFirst_zero_false

theorem le_disp {x : ℝ} (hx : 0 < x) (a : ℝ) : a ≤ disp x a := (isClearFirst_disp hx a).1.1

#print axioms le_disp

/-- `x` is clear at its displaced end. -/
theorem clear_disp {x : ℝ} (hx : 0 < x) (a : ℝ) : (1 / 8 : ℝ) ≤ distInt (x * disp x a) :=
  mem_lonelySet_singleton.mp (isClearFirst_disp hx a).1.2

#print axioms clear_disp

/-- The displaced end is the least clear point: any clear `s ≥ a` is `≥ disp x a`. -/
theorem disp_le_of_clear {x a s : ℝ} (hx : 0 < x) (has : a ≤ s) (hs : (1 / 8 : ℝ) ≤ distInt (x * s)) :
    disp x a ≤ s :=
  (isClearFirst_disp hx a).2 ⟨has, mem_lonelySet_singleton.mpr hs⟩

#print axioms disp_le_of_clear

/-- **The displacement is below the zone width** [L] (NEW as one statement for both cases; in the way it is
`BlockLanding.nextOpening_lt`): `disp x a < a + 1/(4x)`.  `0 < x` REQUIRED (for `x < 0` the right side is below `a`). -/
theorem disp_lt {x : ℝ} (hx : 0 < x) (a : ℝ) : disp x a < a + 1 / (4 * x) := by
  have hq : 0 < 1 / (4 * x) := by positivity
  unfold disp
  split_ifs with h
  · exact nextOpening_lt hx h
  · linarith

#print axioms disp_lt

theorem displacement_nonneg_lt {x : ℝ} (hx : 0 < x) (a : ℝ) : 0 ≤ displacement x a ∧ displacement x a < 1 / (4 * x) := by
  unfold displacement
  have := le_disp hx a
  have := disp_lt hx a
  constructor <;> linarith

#print axioms displacement_nonneg_lt

/-- The displacement is zero iff `x` is clear at `a` [L]. -/
theorem disp_eq_self_iff {x : ℝ} (hx : 0 < x) (a : ℝ) : disp x a = a ↔ (1 / 8 : ℝ) ≤ distInt (x * a) := by
  constructor
  · intro h
    have := clear_disp hx a
    rwa [h] at this
  · intro h
    unfold disp
    rw [if_neg (Cascade.not_inWay_iff.mpr h)]

#print axioms disp_eq_self_iff

/-- In the way within `1/8` of lap `k`: the displaced end is the opening `(k + 1/8)/x` [L]. -/
theorem disp_of_near {x a : ℝ} {k : ℤ} (hk : |x * a - k| < 1 / 8) : disp x a = ((k : ℝ) + 1 / 8) / x := by
  have hw : InWay x a := by
    unfold InWay
    exact lt_of_le_of_lt (Cascade.distInt_le (x * a) k) hk
  unfold disp
  rw [if_pos hw, Cascade.nextOpening_eq hk]

#print axioms disp_of_near

/-- **The exact displacement** [L] (NEW): within `1/8` of lap `k`, `x * displacement x a = k + 1/8 - x a`, i.e. the
displacement is `(1/8 - r)/x` with `r = x a - k` the signed phase, a number in `[0, 1/(4x))`. -/
theorem mul_displacement {x a : ℝ} (hx : 0 < x) {k : ℤ} (hk : |x * a - k| < 1 / 8) :
    x * displacement x a = (k : ℝ) + 1 / 8 - x * a := by
  unfold displacement
  rw [disp_of_near hk]
  field_simp

#print axioms mul_displacement

/-- The sign reduction: a negative or positive `x` has the same clear set as `|x|`. -/
theorem clearSet_abs (x : ℝ) : clearSet |x| = clearSet x := by
  ext t
  simp [clearSet, Cascade.distInt_abs_mul]

#print axioms clearSet_abs

/-! ## (2) The long cell is never covered; the short cell can be -/

/-- **A closed interval of length at least `1/(4x)` is never inside one open zone of `x`** [L] (zone width exactly
`1/(4x)`).  Re-derivation of the step inside `Carving.survives_of_wide` as a standalone statement (the existing
theorems conclude the existence of a clear point).  `[PROVISIONAL: covering]` at this step: a cell length against a
zone width; supports the displacement-against-cell statement `exists_lonely_iff_displacement_le_length` and no
existence claim.  `0 < x` REQUIRED (zone width `1/(4x)` is a positive length only then); `N` arbitrary. -/
theorem not_subset_zone_of_long {x a b : ℝ} (hx : 0 < x) (N : ℤ) (h : 1 / (4 * x) ≤ b - a) :
    ¬ Set.Icc a b ⊆ zone x N := by
  intro hs
  have hq : 0 < 1 / (4 * x) := by positivity
  have hab : a ≤ b := by linarith
  have h1 := (hs (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩)).1
  have h2 := (hs (show b ∈ Set.Icc a b from ⟨hab, le_rfl⟩)).2
  have := zone_width' hx N
  linarith

#print axioms not_subset_zone_of_long

/-- The sharpness: for every length `L < 1/(4x)` some closed interval of length `L` lies inside one open zone [L]
(NEW).  So `1/(4x)` is the exact threshold of the covering step: `≥` REQUIRED, and nothing smaller works. -/
theorem short_fits_in_zone {x L : ℝ} (hx : 0 < x) (N : ℤ) (hL : L < 1 / (4 * x)) :
    ∃ a b : ℝ, b - a = L ∧ Set.Icc a b ⊆ zone x N := by
  have e := zone_width' hx N
  set ε := (1 / (4 * x) - L) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  refine ⟨((N : ℝ) - 1 / 8) / x + ε, ((N : ℝ) - 1 / 8) / x + ε + L, by ring, ?_⟩
  intro s hs
  constructor
  · linarith [hs.1]
  · linarith [hs.2]

#print axioms short_fits_in_zone

/-- **The long cell is never covered by the zones of `x`** [L] (NEW as a `ZoneCover` statement; consequence of
`not_subset_zone_of_long` and `BlockLanding2.cover_singleton_iff`).  `[PROVISIONAL: covering]` supports the same
displacement-against-cell statement. -/
theorem long_cell_not_covered {x a b : ℝ} (hx : 0 < x) (h : 1 / (4 * x) ≤ b - a) : ¬ ZoneCover {x} a b := by
  intro hc
  have hab : a ≤ b := by
    have : 0 < 1 / (4 * x) := by positivity
    linarith
  obtain ⟨N, h1, h2⟩ := (cover_singleton_iff hx hab).mp hc
  have := zone_width' hx N
  linarith

#print axioms long_cell_not_covered

/-- **A clear point in the first quarter-lap** [L] (NEW, strengthens `Carving.survives_of_wide`): the clear point
`disp x a` lies in `[a, a + 1/(4x))`, so an interval `[a, b]` with `b - a ≥ 1/(4x)` contains it with room to spare:
`disp x a < b`. -/
theorem long_cell_clear_point {x a b : ℝ} (hx : 0 < x) (h : 1 / (4 * x) ≤ b - a) :
    a ≤ disp x a ∧ disp x a < b ∧ (1 / 8 : ℝ) ≤ distInt (x * disp x a) :=
  ⟨le_disp hx a, by linarith [disp_lt hx a], clear_disp hx a⟩

#print axioms long_cell_clear_point

/-! ## (3) The cell level: survival, skipping -/

section CellLevel

variable {S : Finset ℝ} {x u w : ℝ}

/-- **A cell survives iff the displaced left end is inside it** [L] (NEW).  Hypothesis: only `[u, w] ⊆ lonelySet S`
(the cell's maximality is NOT REQUIRED; `u ≤ w` NOT REQUIRED; `0 < u` NOT REQUIRED).  `0 < x` REQUIRED. -/
theorem survive_iff (hx : 0 < x) (hsub : Set.Icc u w ⊆ lonelySet S) :
    (∃ s ∈ Set.Icc u w, s ∈ lonelySet (insert x S)) ↔ disp x u ≤ w := by
  constructor
  · rintro ⟨s, hs, hl⟩
    rw [lonelySet_insert, ← lonelySet_singleton] at hl
    exact le_trans (disp_le_of_clear hx hs.1 (mem_lonelySet_singleton.mp hl.2)) hs.2
  · intro h
    refine ⟨disp x u, ⟨le_disp hx u, h⟩, ?_⟩
    rw [lonelySet_insert, ← lonelySet_singleton]
    exact ⟨hsub ⟨le_disp hx u, h⟩, mem_lonelySet_singleton.mpr (clear_disp hx u)⟩

#print axioms survive_iff

/-- **Skipped iff the displaced left end is past the cell** [L] (NEW): no point of `[u, w]` is lonely for
`insert x S` iff `w < disp x u`.  Same hypotheses as `survive_iff`. -/
theorem skipped_iff (hx : 0 < x) (hsub : Set.Icc u w ⊆ lonelySet S) :
    (∀ s ∈ Set.Icc u w, s ∉ lonelySet (insert x S)) ↔ w < disp x u := by
  rw [← not_le, ← survive_iff hx hsub]
  push Not
  rfl

#print axioms skipped_iff

/-- **Skipped iff inside one open zone** [L] (`Carving.cell_killed_iff` restated for a set with `[u,w] ⊆ lonelySet S`
instead of a cell, with `u ≤ w` REQUIRED here: for `u > w` the left side is vacuous and the right side can fail). -/
theorem skipped_iff_zone (hx : 0 < x) (huw : u ≤ w) (hsub : Set.Icc u w ⊆ lonelySet S) :
    (∀ s ∈ Set.Icc u w, s ∉ lonelySet (insert x S)) ↔
      ∃ N : ℤ, ((N : ℝ) - 1 / 8) / x < u ∧ w < ((N : ℝ) + 1 / 8) / x := by
  rw [← killed_iff hx huw]
  refine forall₂_congr fun s hs => ?_
  rw [lonelySet_insert]
  exact ⟨fun h1 h2 => h1 ⟨hsub hs, h2⟩, fun h1 h2 => h1 h2.2⟩

#print axioms skipped_iff_zone

/-- **A skipped cell is shorter than the zone width** [L] (NEW as one statement; `BlockLanding.typeX_imp_narrow` for
`{x}`): if `[u, w]` is skipped then `w - u < disp x u - u < 1/(4x)`.  Not `≤`: the bound is strict. -/
theorem skipped_lt_zone_width (hx : 0 < x) (hsub : Set.Icc u w ⊆ lonelySet S)
    (h : ∀ s ∈ Set.Icc u w, s ∉ lonelySet (insert x S)) :
    w - u < displacement x u ∧ displacement x u < 1 / (4 * x) := by
  have h1 := (skipped_iff hx hsub).mp h
  have h2 := disp_lt hx u
  unfold displacement
  constructor <;> linarith

#print axioms skipped_lt_zone_width

/-- **A cell of length at least `1/(4x)` is never skipped, and survives with its displaced end strictly inside**
[L] (NEW as a cell statement).  `[PROVISIONAL: covering]` (a cell length against a zone width); supports the
displacement-against-cell statement and no existence claim. -/
theorem long_cell_survives (hx : 0 < x) (hsub : Set.Icc u w ⊆ lonelySet S) (h : 1 / (4 * x) ≤ w - u) :
    disp x u < w ∧ ∃ s ∈ Set.Icc u w, s ∈ lonelySet (insert x S) := by
  have h1 : disp x u < w := by linarith [disp_lt hx u]
  exact ⟨h1, (survive_iff hx hsub).mpr h1.le⟩

#print axioms long_cell_survives

end CellLevel

/-! ## (4) The exact existence consequence -/

section Existence

variable {S : Finset ℝ} {x : ℝ}

/-- **Existence for `S ∪ {x}`, exactly** [L] (NEW; assembled from `survive_iff` and `LonelyCells.cell_of_lonely`):
a positive lonely instant exists for `insert x S` iff some cell `[u, w]` of `S` has displaced left end `disp x u ≤ w`.
Hypotheses: `S` nonempty REQUIRED (`exists_iff_fails_empty`: with `S = ∅` the left side holds and no cell exists);
`0 < x` REQUIRED (`exists_iff_fails_zero`); `∀ d ∈ S, 0 < d` NOT REQUIRED (see `exists_lonely_iff_cell_general`,
which drops it and replaces `x` by `|x|`; kept here only because `cell_of_lonely` uses it). -/
theorem exists_lonely_iff_cell (hpos : ∀ d ∈ S, 0 < d) (hne : S.Nonempty) (hx : 0 < x) :
    (∃ t : ℝ, 0 < t ∧ t ∈ lonelySet (insert x S)) ↔ ∃ u w, IsCell S u w ∧ disp x u ≤ w := by
  constructor
  · rintro ⟨t, ht0, htl⟩
    have hS : t ∈ lonelySet S := by rw [lonelySet_insert] at htl; exact htl.1
    obtain ⟨p, -, q, -, hc, h1, h2⟩ := cell_of_lonely hpos hne ht0 hS
    refine ⟨_, _, hc, ?_⟩
    exact (survive_iff hx hc.2.2.1).mp ⟨t, ⟨h1, h2⟩, htl⟩
  · rintro ⟨u, w, hc, h⟩
    obtain ⟨s, hs, hl⟩ := (survive_iff hx hc.2.2.1).mpr h
    exact ⟨s, lt_of_lt_of_le hc.1 hs.1, hl⟩

#print axioms exists_lonely_iff_cell

theorem exists_iff_fails_empty : ¬ ((∃ t : ℝ, 0 < t ∧ t ∈ lonelySet (insert (1 : ℝ) (∅ : Finset ℝ))) ↔
    ∃ u w, IsCell (∅ : Finset ℝ) u w ∧ disp 1 u ≤ w) := by
  intro h
  have h1 : ∃ t : ℝ, 0 < t ∧ t ∈ lonelySet (insert (1 : ℝ) (∅ : Finset ℝ)) := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    rw [Finset.insert_empty, mem_lonelySet_singleton]
    have : distInt (1 * (1 / 2 : ℝ)) = 1 / 2 := by
      unfold distInt
      have : round (1 * (1 / 2 : ℝ)) = 1 := by
        rw [round_eq, Int.floor_eq_iff]; constructor <;> norm_num
      rw [this]; norm_num [abs_of_neg]
    rw [this]; norm_num
  obtain ⟨u, w, hc, -⟩ := h.mp h1
  exact absurd (nonempty_of_cell hc) (by simp)

#print axioms exists_iff_fails_empty

theorem exists_iff_fails_zero : ¬ ((∃ t : ℝ, 0 < t ∧ t ∈ lonelySet (insert (0 : ℝ) ({1} : Finset ℝ))) ↔
    ∃ u w, IsCell ({1} : Finset ℝ) u w ∧ disp 0 u ≤ w) := by
  intro h
  have hc := singleton_isCell (m := (1 : ℝ)) one_pos
  have hd : disp 0 (1 / (8 * 1)) ≤ 7 / (8 * 1) := by
    have hw : InWay (0 : ℝ) (1 / (8 * 1)) := by
      unfold InWay distInt; simp
    unfold disp
    rw [if_pos hw]
    unfold nextOpening
    simp
    norm_num
  obtain ⟨t, -, ht⟩ := h.mpr ⟨_, _, hc, hd⟩
  rw [lonelySet_insert] at ht
  have := ht.2
  simp [clearSet, distInt] at this
  linarith

#print axioms exists_iff_fails_zero

/-- **Existence in terms of displacement against cell length** [L] (NEW; restates `exists_lonely_iff_cell`).  The
quantity to be controlled is `displacement x u` against `w - u`; its bound `displacement x u < 1/(4x)` is
`displacement_nonneg_lt`.  `[PROVISIONAL: covering]` NAMED, NOT ASSERTED: that for the cell lengths at hand the
displacement stays within the cell is the content owed (it supports the conjecture itself); nothing here asserts it. -/
theorem exists_lonely_iff_displacement_le_length (hpos : ∀ d ∈ S, 0 < d) (hne : S.Nonempty) (hx : 0 < x) :
    (∃ t : ℝ, 0 < t ∧ t ∈ lonelySet (insert x S)) ↔ ∃ u w, IsCell S u w ∧ displacement x u ≤ w - u := by
  rw [exists_lonely_iff_cell hpos hne hx]
  unfold displacement
  refine exists_congr fun u => exists_congr fun w => and_congr_right fun _ => ?_
  constructor <;> intro h <;> linarith

#print axioms exists_lonely_iff_displacement_le_length

/-- The sign and positivity reductions: only `S` nonempty and `x ≠ 0` are needed [L] (NEW).  Every disparity of `S`
may have any sign or be zero, and `x` any sign: `|x|` replaces `x`.  (A zero in `S` makes both sides false.) -/
theorem exists_lonely_iff_cell_general (hne : S.Nonempty) (hx : x ≠ 0) :
    (∃ t : ℝ, 0 < t ∧ t ∈ lonelySet (insert x S)) ↔ ∃ u w, IsCell S u w ∧ disp |x| u ≤ w := by
  by_cases h0 : (0 : ℝ) ∈ S
  · have hempty : lonelySet S = ∅ := by
      ext t
      simp only [lonelySet, Cascade.LonelyAt, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hl
      have := hl 0 h0
      simp [distInt] at this
      linarith
    constructor
    · rintro ⟨t, -, htl⟩
      rw [lonelySet_insert, hempty] at htl
      exact absurd htl (by simp)
    · rintro ⟨u, w, hc, -⟩
      have := hc.2.2.1 (show u ∈ Set.Icc u w from ⟨le_rfl, hc.2.1⟩)
      rw [hempty] at this
      exact absurd this (by simp)
  · set T : Finset ℝ := S.image (fun d => |d|) with hT
    have hTl : lonelySet T = lonelySet S := by
      ext t
      simp only [lonelySet, Cascade.LonelyAt, Set.mem_setOf_eq, hT, Finset.forall_mem_image]
      refine forall₂_congr fun d _ => ?_
      rw [Cascade.distInt_abs_mul]
    have hTpos : ∀ d ∈ T, 0 < d := by
      intro d hd
      rw [hT, Finset.mem_image] at hd
      obtain ⟨e, he, rfl⟩ := hd
      exact abs_pos.mpr (fun h => h0 (h ▸ he))
    have hTne : T.Nonempty := hne.image _
    have hcell : ∀ u w, IsCell T u w ↔ IsCell S u w := by
      intro u w; unfold IsCell; rw [hTl]
    have hins : lonelySet (insert x S) = lonelySet (insert |x| T) := by
      rw [lonelySet_insert, lonelySet_insert, hTl, clearSet_abs]
    have hx' : 0 < |x| := abs_pos.mpr hx
    rw [hins, exists_lonely_iff_cell hTpos hTne hx']
    simp only [hcell]

#print axioms exists_lonely_iff_cell_general

/-- **The landing of `insert x S` is a displaced left end** [L] (NEW form; `BlockLanding2.landing_iff_first_open_cell`
with `F = {x}`, where the prefix condition becomes `w' < disp x u'` by `skipped_iff`): `t` is the landing iff there is
a cell `[u, w]` of `S` with `disp x u ≤ w`, `t = disp x u`, and every earlier cell `[u', w']` (`u' < u`) is skipped,
`w' < disp x u'`.  `S` positive and nonempty: as in `landing_iff_first_open_cell`; REQUIRED there; here
`exists_lonely_iff_cell_general` shows the existence part does not need positivity. -/
theorem landing_iff_disp (hpos : ∀ d ∈ S, 0 < d) (hne : S.Nonempty) (hx : 0 < x) {t : ℝ} :
    IsLanding (insert x S) t ↔
      ∃ u w, IsCell S u w ∧ (∀ u' w', IsCell S u' w' → u' < u → w' < disp x u') ∧ disp x u ≤ w ∧
        t = disp x u := by
  have hI : insert x S = S ∪ {x} := by
    rw [Finset.insert_eq, Finset.union_comm]
  rw [hI, landing_iff_first_open_cell (F := {x}) hpos hne]
  constructor
  · rintro ⟨a, b, u, hc, hpre, hu, hub, htu⟩
    have hud : u = disp x a := hu.unique (isClearFirst_disp hx a)
    rw [hud] at hub htu
    refine ⟨a, b, hc, fun u' w' hc' hlt => ?_, hub, htu⟩
    have hu' := isClearFirst_disp hx u'
    exact (typeX_iff hu').mpr (hpre u' w' hc' hlt)
  · rintro ⟨a, b, hc, hpre, hub, rfl⟩
    refine ⟨a, b, disp x a, hc, fun u' w' hc' hlt => ?_, isClearFirst_disp hx a, hub, rfl⟩
    exact (typeX_iff (isClearFirst_disp hx u')).mp (hpre u' w' hc' hlt)

#print axioms landing_iff_disp

end Existence

/-! ## (5) The exact mechanism: the opening of `x` falls inside the cell; the phase of the left end -/

section Mechanism

variable {x u w : ℝ}

/-- `[u, w]` contains a point clear for `x` iff `disp x u ≤ w` [L] (NEW; `S`-free form of `survive_iff`). -/
theorem exists_clear_iff_disp_le (hx : 0 < x) :
    (∃ s ∈ Set.Icc u w, (1 / 8 : ℝ) ≤ distInt (x * s)) ↔ disp x u ≤ w :=
  ⟨fun ⟨_, hs, h⟩ => le_trans (disp_le_of_clear hx hs.1 h) hs.2,
   fun h => ⟨disp x u, ⟨le_disp hx u, h⟩, clear_disp hx u⟩⟩

#print axioms exists_clear_iff_disp_le

/-- **The exact extra mechanism** [L] (NEW): the displaced left end is inside `[u, w]` iff either `x` is clear at the
left end `u` (and `u ≤ w`), or an OPENING `(N + 1/8)/x` of `x` falls inside `[u, w]`.  A short cell survives only by the
second alternative with `x` in the way at `u`: its left end is pushed to that opening, which lies in the cell.
No hypothesis on `S`: the statement concerns `x`, `u`, `w` only; `0 < x` REQUIRED. -/
theorem survives_iff_opening_or_clear (hx : 0 < x) :
    disp x u ≤ w ↔ ((1 / 8 : ℝ) ≤ distInt (x * u) ∧ u ≤ w) ∨ ∃ N : ℤ, u ≤ winLo x N ∧ winLo x N ≤ w := by
  constructor
  · intro h
    by_cases hc : (1 / 8 : ℝ) ≤ distInt (x * u)
    · left
      refine ⟨hc, ?_⟩
      rwa [(disp_eq_self_iff hx u).mpr hc] at h
    · right
      have hw : InWay x u := not_le.mp hc
      obtain ⟨k, hk⟩ := Cascade.exists_near_int hw
      have hd := disp_of_near hk
      refine ⟨k, ?_, ?_⟩
      · have := le_disp hx u
        unfold winLo; rw [← hd]; exact this
      · unfold winLo; rw [← hd]; exact h
  · rintro (⟨hc, huw⟩ | ⟨N, h1, h2⟩)
    · rwa [(disp_eq_self_iff hx u).mpr hc]
    · have hclear : (1 / 8 : ℝ) ≤ distInt (x * winLo x N) := by
        rw [mul_winLo hx, add_comm, Cascade.distInt_eighth_add_int]
      exact le_trans (disp_le_of_clear hx h1 hclear) h2

#print axioms survives_iff_opening_or_clear

/-- **Survival in phase form** [L] (NEW): for `x` within `1/8` of lap `k` at `u`, `disp x u ≤ w` iff
`k + 1/8 - x u ≤ x (w - u)`: the cell length against the displacement `(1/8 - r)/x`, `r = x u - k`. -/
theorem survives_iff_phase (hx : 0 < x) {k : ℤ} (hk : |x * u - k| < 1 / 8) :
    disp x u ≤ w ↔ (k : ℝ) + 1 / 8 - x * u ≤ x * (w - u) := by
  rw [← mul_displacement hx hk]
  unfold displacement
  rw [mul_le_mul_iff_right₀ hx]
  constructor <;> intro h <;> linarith

#print axioms survives_iff_phase

/-- **The displacement at an integer phase is exactly `1/(8x)`** [L] (NEW): if `x u` is an integer then `x` is in the
way at `u` and `x * displacement x u = 1/8`.  So no threshold below `1/8` in `x (w - u)` can be sufficient for such a
left end: the bound of `survives_of_small_opener` is attained. -/
theorem displacement_of_integer_phase (hx : 0 < x) {M : ℤ} (hM : x * u = M) : x * displacement x u = 1 / 8 := by
  have hk : |x * u - M| < 1 / 8 := by rw [hM]; simp
  rw [mul_displacement hx hk, hM]; ring

#print axioms displacement_of_integer_phase

/-- **A sufficient condition from the phase denominator** [L] (NEW).  If `d * (x u)` is an integer, `d` a positive
natural number, then `x (w - u) ≥ 1/8 + ⌊(d-1)/8⌋/d` implies `disp x u ≤ w`.  Hypotheses: `0 < x` REQUIRED (division by
`x`); `d ≥ 1` REQUIRED; `x u ∈ (1/d) ℤ` is the only property of `u` used; no hypothesis on `S`.  The constant is
exact for `d ≤ 8` (`displacement_of_integer_phase`) and is below `1/4` for every `d`. -/
theorem survives_of_phase (hx : 0 < x) (d : ℕ) (hd : 0 < d) (M : ℤ) (hM : (d : ℝ) * (x * u) = M)
    (hL : 1 / 8 + (((d - 1) / 8 : ℕ) : ℝ) / d ≤ x * (w - u)) : disp x u ≤ w := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hqnn : (0 : ℝ) ≤ (((d - 1) / 8 : ℕ) : ℝ) / d := by positivity
  by_cases hw : InWay x u
  · obtain ⟨k, hk⟩ := Cascade.exists_near_int hw
    have hmd := mul_displacement hx hk
    have h1 := abs_lt.mp hk
    obtain ⟨m, hm⟩ : ∃ m : ℤ, m = M - (d : ℤ) * k := ⟨_, rfl⟩
    have hmR : (d : ℝ) * (x * u - k) = m := by
      rw [hm]; push_cast; rw [← hM]; ring
    have hlt := mul_lt_mul_of_pos_left h1.1 hdR
    have hlt2 : -(d : ℝ) < 8 * m := by
      have : (d : ℝ) * (x * u - k) = m := hmR
      nlinarith
    have hlt3 : -(d : ℤ) < 8 * m := by exact_mod_cast hlt2
    have hq : -m ≤ (((d - 1) / 8 : ℕ) : ℤ) := by omega
    have hqR : -(m : ℝ) ≤ (((d - 1) / 8 : ℕ) : ℝ) := by
      have := (Int.cast_le (R := ℝ)).mpr hq
      push_cast at this
      exact this
    have hphase : x * u = k + m / d := by
      field_simp; linarith [hmR]
    have e : (k : ℝ) + 1 / 8 - x * u = 1 / 8 + (-(m : ℝ)) / d := by
      rw [hphase]; ring
    have hle : (-(m : ℝ)) / d ≤ (((d - 1) / 8 : ℕ) : ℝ) / d := div_le_div_of_nonneg_right hqR hdR.le
    have : x * displacement x u ≤ x * (w - u) := by
      rw [hmd, e]; linarith
    have := le_of_mul_le_mul_left this hx
    unfold displacement at this
    linarith
  · unfold disp
    rw [if_neg hw]
    by_contra hlt
    push Not at hlt
    nlinarith

#print axioms survives_of_phase

/-- **The opener form** [L] (NEW): the left end `u = (k + 1/8)/d` is the opening of a disparity `d` (a positive natural
number, as for an integer disparity set) and `x (k + 1/8)` is an integer.  Then `x (w - u) ≥ 1/8 + ⌊(d-1)/8⌋/d` implies
`disp x u ≤ w`.  In the integer case `x = 8c` the integrality holds for every `k` (`M = 8 c k + c`). -/
theorem survives_of_opener (hx : 0 < x) (d : ℕ) (hd : 0 < d) (k M : ℤ) (hu : u = ((k : ℝ) + 1 / 8) / d)
    (hM : x * ((k : ℝ) + 1 / 8) = M) (hL : 1 / 8 + (((d - 1) / 8 : ℕ) : ℝ) / d ≤ x * (w - u)) :
    disp x u ≤ w := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  refine survives_of_phase hx d hd M ?_ hL
  rw [hu]
  have : (d : ℝ) * (x * (((k : ℝ) + 1 / 8) / d)) = x * ((k : ℝ) + 1 / 8) := by
    field_simp
  rw [this, hM]

#print axioms survives_of_opener

/-- **Small opener: threshold `1/(8x)`** [L] (NEW): for `d ≤ 8` the condition is `x (w - u) ≥ 1/8`, twice as weak a
length requirement as `x (w - u) ≥ 1/4` (`1/(4x)`), and exact by `displacement_of_integer_phase`. -/
theorem survives_of_small_opener (hx : 0 < x) (d : ℕ) (hd : 0 < d) (hd8 : d ≤ 8) (k M : ℤ)
    (hu : u = ((k : ℝ) + 1 / 8) / d) (hM : x * ((k : ℝ) + 1 / 8) = M) (hL : 1 / 8 ≤ x * (w - u)) :
    disp x u ≤ w := by
  refine survives_of_opener hx d hd k M hu hM ?_
  have : (d - 1) / 8 = 0 := by omega
  rw [this]; simpa using hL

#print axioms survives_of_small_opener

/-- **The integer multiple `x = 8c`**: `M = 8 c k + c` [L] (NEW). -/
theorem survives_of_opener_mult (c : ℤ) (hc : 0 < c) (d : ℕ) (hd : 0 < d) (k : ℤ)
    (hu : u = ((k : ℝ) + 1 / 8) / d) (hL : 1 / 8 + (((d - 1) / 8 : ℕ) : ℝ) / d ≤ (8 * (c : ℝ)) * (w - u)) :
    disp (8 * (c : ℝ)) u ≤ w := by
  have hx : (0 : ℝ) < 8 * (c : ℝ) := by
    have : (0 : ℝ) < c := by exact_mod_cast hc
    linarith
  refine survives_of_opener hx d hd k (8 * c * k + c) hu ?_ hL
  push_cast; ring

#print axioms survives_of_opener_mult

/-- **Instance: the length `1/(8x)` is not sufficient for an opener `d = 9`** [L] (NEW; the pair `(u, w)` is the cell
of `{9, 11}` at `c = 1` found by the exact search [OBS]; here only the arithmetic is proved): `x = 8`,
`u = 17/72`, `w = 23/88`, `x (w - u) = 20/99 ≥ 1/8` and yet `disp 8 u > w`.  The phase of `x u = 17/9` is `-1/9`, so
the displacement is `(1/8 + 1/9)/x`, above `20/99 /x`.  This is why the threshold of `survives_of_opener` is
`1/8 + ⌊(d-1)/8⌋/d` and not `1/8` for `d > 8`. -/
theorem eighth_insufficient_instance : ∃ u w : ℝ, 1 / 8 ≤ 8 * (w - u) ∧ ¬ disp 8 u ≤ w := by
  refine ⟨17 / 72, 23 / 88, by norm_num, ?_⟩
  have hk : |(8 : ℝ) * (17 / 72) - ((2 : ℤ) : ℝ)| < 1 / 8 := by
    rw [abs_lt]; constructor <;> norm_num
  rw [survives_iff_phase (by norm_num) hk]
  norm_num

#print axioms eighth_insufficient_instance

/-- **Instance: a short cell survives by displacement** [L] (NEW; arithmetic of the exact-search record for
`D' = {1, 4, 10}`, `c = 3`, cell `[17/80, 7/32]` [OBS]): `x = 24`, `x (w - u) = 3/20 < 1/4`, `x` is in the way at `u`
(`x u = 51/10`, phase `1/10`) and the next opening falls inside: `disp 24 u ≤ w`.  The displacement is `1/40` in
`x`-units, below `x (w - u)`; the threshold `1/8 + ⌊(d-1)/8⌋/d` of `survives_of_opener` is not necessary. -/
theorem short_cell_survives_instance :
    ∃ u w : ℝ, 24 * (w - u) < 1 / 4 ∧ InWay 24 u ∧ disp 24 u ≤ w := by
  refine ⟨17 / 80, 7 / 32, by norm_num, ?_, ?_⟩
  · have hk : |(24 : ℝ) * (17 / 80) - ((5 : ℤ) : ℝ)| < 1 / 8 := by
      rw [abs_lt]; constructor <;> norm_num
    unfold InWay
    exact lt_of_le_of_lt (Cascade.distInt_le _ _) hk
  · have hk : |(24 : ℝ) * (17 / 80) - ((5 : ℤ) : ℝ)| < 1 / 8 := by
      rw [abs_lt]; constructor <;> norm_num
    rw [survives_iff_phase (by norm_num) hk]
    norm_num

#print axioms short_cell_survives_instance

end Mechanism

end Fresh.DispCell
