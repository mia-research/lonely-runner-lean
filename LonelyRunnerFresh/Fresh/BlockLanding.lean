import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Localisation
import Fresh.LonelyCells
import Fresh.Carving
import Fresh.WhereProofs

/-!
# Block landing: where the landing of `C ∪ F` is, given the landing cell of `C` (Task AC)

Written 2026-10-08.  Imports `Mathlib` and the Fresh modules `Framework`, `Cascade`, `Localisation`, `LonelyCells`,
`Carving`, `WhereProofs`; nothing from the existing `LonelyRunner` repo.  Exact reals only; every disparity is positive
(no runner is stationary).  Every statement is symbolic, for all finite sets.

Setting.  `S = C ∪ F`, finite sets of positive disparities, `C` nonempty.  The LANDING of a set `ds` is its least
positive lonely instant (`IsLanding`), which by `Cascade.fixed_is_first_isolation` and
`WhereProofs.landingIsFirstIsolation` is the fixed point of the cascade from `1/(8 min)` (`cascade_landing_isLanding`,
`cascade_landing_isLanding_arr`).  `t_C` is the landing of `C`, `[t_C, w_C]` the cell of `C` that starts there
(`LonelyCells.IsCell`; `w_C` is the right end, which equals the least zone start at or after `t_C`, the data's
`tclose_C`), `u` the least point at or after `t_C` that is lonely for `F` alone (`IsClearFirst`).

NOTHING here asserts that a landing, a cell or `u` exists: each theorem is conditional on the object it names, or
derives it from a lonely point of `S` (`decomposition_of_lonely`).  No count, cap, move budget or threshold on a
block's size is the shape of any statement; `4·L·x ≥ 1` below is a width comparison inside one cell.

Findings.
* (1) `landing_union_ge_u`: every positive lonely point of `C ∪ F` is at least `u`, in every case.
  `landing_union_eq_u`: if `u ≤ w_C` the landing of `C ∪ F` is `u`.  `landing_union_gt_wC`: if `w_C < u`, every lonely
  point of `C ∪ F` is `> w_C`.  `landing_eq_u_iff`: the landing is `u` iff `u` is lonely for `C`.  `typeX_iff`:
  `w_C < u` iff no point of the cell is lonely for `F`.  The hypothesis in the brief that every element of `F` is
  `≥` every element of `C` is IDLE in all of this (nothing uses it; the exact-data check ran with `F` elements below
  `C` elements).
* (2) `u_at_bound`: for `t_C = 1/(8m)` the first clear point of one runner `x` has `8m·u = 1` if `|s| ≥ m` and
  `8m·u = 1 + (m − s)/x` if `|s| < m`, `s = x − 8m·round(x/(8m))` (`sres`).  `core_displacement`: with
  `1/(4x) ≤ w_C − t_C` the landing of `C ∪ {x}` is that `u`.  `singleton_core_displacement`: `C = {m}`, `m ≤ 3x`.
  `u_multiple`: `x = 8mk` gives `R* = 1 + m/x`.
* (3) `typeX_single_iff`, `typeX_imp_narrow`, `not_typeX_of_wide`: for one block runner, `w_C < u` iff `x` is in the way
  at `t_C` and its next opening is beyond `w_C`; so `w_C < u` forces `4·L·x < 1` (`L = w_C − t_C`).
  `cell_degenerate_iff`: `L = 0` iff some `z ∈ C` reads exactly `k + 7/8` at `t_C`; `degenerate_at_bound`: at
  `t_C = 1/(8m)` that is `z = m(8k+7)`; `typeX_of_degenerate`: then every in-the-way block runner gives `w_C < u`.
  Exact examples: `touch_block_example` (`C = {1,7}`, `x = 8`) and `narrow_cell_example` (`C = {2,12}`, `x = 15`).

Provenance.  The least-element arguments and the decomposition are new to this file (the data are
`experiments/n8/block_rule_cascade_v1.out`, types U, D, X).  The carving fact `lonelySet_insert` of `Fresh.Carving` is
the same intersection as `lonelySet_union` here for two sets.  The single-runner facts reuse `Cascade.nextOpening_eq`,
`Cascade.inWay_until_opening`, `Cascade.not_inWay_at_nextOpening`.  Existing-repo declarations corresponding:
`LRC/Spec/DoorFlank` and `Cascade/Iteration.lean` (read for the idea only); no proof was copied that was not
understood, and every proof was written for this file.
-/

open Classical

namespace Fresh.BlockLanding

open Fresh Fresh.LonelyCells Fresh.Carving

/-! ## Objects -/

/-- The landing of `ds`: its least positive lonely instant. -/
-- STANDING: DEFINITION
def IsLanding (ds : Finset ℝ) (t : ℝ) : Prop := IsLeast {s : ℝ | 0 < s ∧ s ∈ lonelySet ds} t

/-- `u` is the least point at or after `a` that is lonely for `ds`. -/
-- STANDING: DEFINITION
def IsClearFirst (ds : Finset ℝ) (a u : ℝ) : Prop := IsLeast {s : ℝ | a ≤ s ∧ s ∈ lonelySet ds} u

/-- The signed residue of `x` modulo `8m`: `x − 8m·round(x/(8m))`, in `[−4m, 4m]`. -/
noncomputable def sres (m x : ℝ) : ℝ := x - 8 * m * (round (x / (8 * m)) : ℝ)

/-! ## Basic facts -/

theorem lonelySet_union (C F : Finset ℝ) : lonelySet (C ∪ F) = lonelySet C ∩ lonelySet F := by
  ext t
  simp only [lonelySet, Cascade.LonelyAt, Set.mem_setOf_eq, Set.mem_inter_iff, Finset.mem_union]
  constructor
  · intro h; exact ⟨fun d hd => h d (Or.inl hd), fun d hd => h d (Or.inr hd)⟩
  · rintro ⟨h1, h2⟩ d (hd | hd)
    · exact h1 d hd
    · exact h2 d hd

#print axioms lonelySet_union

/-- A least point at or after `a` of the lonely set exists as soon as one point at or after `a` is lonely: the set
`[a, ∞) ∩ lonelySet ds` is closed, nonempty and bounded below.  (Closedness is `isClosed_lonelySet`; this is not a
counting or covering step.) -/
theorem exists_clearFirst (ds : Finset ℝ) (a : ℝ) (h : ∃ s, a ≤ s ∧ s ∈ lonelySet ds) :
    ∃ u, IsClearFirst ds a u := by
  obtain ⟨s, hs⟩ := h
  have hcl : IsClosed {s : ℝ | a ≤ s ∧ s ∈ lonelySet ds} :=
    (isClosed_Ici (a := a)).inter (isClosed_lonelySet ds)
  have hne : ({s : ℝ | a ≤ s ∧ s ∈ lonelySet ds}).Nonempty := ⟨s, hs⟩
  have hbdd : BddBelow {s : ℝ | a ≤ s ∧ s ∈ lonelySet ds} := ⟨a, fun y hy => hy.1⟩
  exact ⟨_, hcl.csInf_mem hne hbdd, fun y hy => csInf_le hbdd hy⟩

#print axioms exists_clearFirst

/-- The landing is the first lonely point at or after the bound `1/(8m)`, for any `m ∈ ds`. -/
theorem isLanding_iff_clearFirst {ds : Finset ℝ} {m : ℝ} (hm : m ∈ ds) (hm0 : 0 < m) {t : ℝ} :
    IsLanding ds t ↔ IsClearFirst ds (1 / (8 * m)) t := by
  have hb : 0 < 1 / (8 * m) := by positivity
  constructor
  · rintro ⟨⟨ht, hl⟩, hle⟩
    refine ⟨⟨Cascade.bound_le_of_lonely hm hm0 hl ht, hl⟩, fun s hs => hle ⟨lt_of_lt_of_le hb hs.1, hs.2⟩⟩
  · rintro ⟨⟨ht, hl⟩, hle⟩
    refine ⟨⟨lt_of_lt_of_le hb ht, hl⟩, fun s hs => hle ⟨Cascade.bound_le_of_lonely hm hm0 hs.2 hs.1, hs.2⟩⟩

#print axioms isLanding_iff_clearFirst

/-- A landing exists as soon as some positive instant is lonely (conditional; not an existence claim). -/
theorem exists_landing {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hne : ds.Nonempty)
    (h : ∃ s, 0 < s ∧ s ∈ lonelySet ds) : ∃ t, IsLanding ds t := by
  obtain ⟨m, hm⟩ := hne
  obtain ⟨s, hs, hl⟩ := h
  obtain ⟨u, hu⟩ := exists_clearFirst ds (1 / (8 * m)) ⟨s, Cascade.bound_le_of_lonely hm (hpos m hm) hl hs, hl⟩
  exact ⟨u, (isLanding_iff_clearFirst hm (hpos m hm)).mpr hu⟩

#print axioms exists_landing

/-- The cascade's fixed point from the bound is the landing (set form). -/
theorem cascade_landing_isLanding {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {m : ℝ} (hm : m ∈ ds)
    {seq : ℕ → ℝ} (h0 : seq 0 = 1 / (8 * m)) (hmv : ∀ n, IsMove ds (seq n) (seq (n + 1)))
    {N : ℕ} (hN : seq (N + 1) = seq N) : IsLanding ds (seq N) := by
  have hf := Cascade.fixed_is_first_isolation hpos hm h0 hmv hN
  have hm0 := hpos m hm
  have hge : seq 0 ≤ seq N := Cascade.start_le_seq hpos hmv N
  have hb : 0 < 1 / (8 * m) := by positivity
  exact ⟨⟨lt_of_lt_of_le (h0 ▸ hb) hge, hf.1⟩, fun s hs => hf.2 s hs.1 hs.2⟩

#print axioms cascade_landing_isLanding

/-- The cascade's landing of an arrangement's subject is the landing of its disparity set. -/
theorem cascade_landing_isLanding_arr {v : Fin 8 → ℝ} (hv : IsArrangement v) {k : Fin 8} {m : ℝ}
    (hm : IsDmin v k m) {tStar : ℝ} (hr : Where.CascadeReaches (disparitySet v k) (1 / (8 * m)) tStar) :
    IsLanding (disparitySet v k) tStar := by
  have hL := WhereProofs.landingIsFirstIsolation v hv k m hm tStar hr
  rw [isolation_set_eq] at hL
  exact hL

#print axioms cascade_landing_isLanding_arr

/-! ## (1) The decomposition: types U, D, X -/

section Decomposition

variable {C F : Finset ℝ} {tC wC u : ℝ}

/-- **(1a) The landing of `C ∪ F` is never before `u`** [L]. -/
theorem landing_union_ge_u (hC : IsLanding C tC) (hu : IsClearFirst F tC u) {s : ℝ}
    (hs : 0 < s) (hl : s ∈ lonelySet (C ∪ F)) : u ≤ s := by
  rw [lonelySet_union] at hl
  exact hu.2 ⟨hC.2 ⟨hs, hl.1⟩, hl.2⟩

#print axioms landing_union_ge_u

/-- **(1b) If `u ≤ w_C`, the landing of `C ∪ F` is `u`** [L]: the point `u` lies in the cell of `C` (lonely for `C`)
and is lonely for `F`; nothing positive and lonely for `C ∪ F` is earlier (1a). -/
theorem landing_union_eq_u (hC : IsLanding C tC) (hcell : IsCell C tC wC) (hu : IsClearFirst F tC u)
    (huw : u ≤ wC) : IsLanding (C ∪ F) u := by
  have hu0 : 0 < u := lt_of_lt_of_le hC.1.1 hu.1.1
  refine ⟨⟨hu0, ?_⟩, fun s hs => landing_union_ge_u hC hu hs.1 hs.2⟩
  rw [lonelySet_union]
  exact ⟨hcell.2.2.1 ⟨hu.1.1, huw⟩, hu.1.2⟩

#print axioms landing_union_eq_u

/-- **(1c) If `w_C < u`, every positive lonely point of `C ∪ F` is `> w_C`** [L]. -/
theorem landing_union_gt_wC (hC : IsLanding C tC) (hu : IsClearFirst F tC u) (huw : wC < u) {s : ℝ}
    (hs : 0 < s) (hl : s ∈ lonelySet (C ∪ F)) : wC < s :=
  lt_of_lt_of_le huw (landing_union_ge_u hC hu hs hl)

#print axioms landing_union_gt_wC

/-- **(1d) The landing is `u` exactly when `u` is lonely for `C`** [L] (given that `C ∪ F` has a landing `t`).
In particular type X (`w_C < u`) can still have landing `u`, when `u` lies in a later cell of `C`. -/
theorem landing_eq_u_iff (hC : IsLanding C tC) (hu : IsClearFirst F tC u) {t : ℝ}
    (ht : IsLanding (C ∪ F) t) : t = u ↔ u ∈ lonelySet C := by
  have hut : u ≤ t := landing_union_ge_u hC hu ht.1.1 ht.1.2
  have hu0 : 0 < u := lt_of_lt_of_le hC.1.1 hu.1.1
  constructor
  · intro h
    have := ht.1.2
    rw [lonelySet_union] at this
    rw [← h]; exact this.1
  · intro h
    refine le_antisymm (ht.2 ⟨hu0, ?_⟩) hut
    rw [lonelySet_union]; exact ⟨h, hu.1.2⟩

#print axioms landing_eq_u_iff

/-- **(1e) `w_C < u` iff no point of the cell of `C` is lonely for `F`** [L]. -/
theorem typeX_iff (hu : IsClearFirst F tC u) :
    wC < u ↔ ¬ ∃ s ∈ Set.Icc tC wC, s ∈ lonelySet F := by
  constructor
  · rintro hw ⟨s, hs, hl⟩
    exact absurd (lt_of_lt_of_le hw (hu.2 ⟨hs.1, hl⟩)) (not_lt.mpr hs.2)
  · intro h
    by_contra hc
    exact h ⟨u, ⟨hu.1.1, not_lt.mp hc⟩, hu.1.2⟩

#print axioms typeX_iff

/-- **(1) The decomposition theorem** [L], all parts together.  Given the landing `tC` of `C`, its cell `[tC, wC]`
and `u` the first `F`-lonely point at or after `tC`, and a landing `t` of `C ∪ F`:
`tC ≤ u ≤ t`; `u ≤ wC → t = u`; `wC < u → wC < t`; and `t = u ↔ u` lonely for `C`.  No ordering of `F` against `C` is
used. -/
theorem landing_decomposition (hC : IsLanding C tC) (hcell : IsCell C tC wC) (hu : IsClearFirst F tC u)
    {t : ℝ} (ht : IsLanding (C ∪ F) t) :
    tC ≤ u ∧ u ≤ t ∧ (u ≤ wC → t = u) ∧ (wC < u → wC < t) ∧ (t = u ↔ u ∈ lonelySet C) := by
  have hut : u ≤ t := landing_union_ge_u hC hu ht.1.1 ht.1.2
  refine ⟨hu.1.1, hut, fun huw => ?_, fun huw => lt_of_lt_of_le huw hut, landing_eq_u_iff hC hu ht⟩
  exact (ht.unique (landing_union_eq_u hC hcell hu huw)).symm.symm

#print axioms landing_decomposition

/-- Types, as the three cases of `u` against `tC` and `wC` (exhaustive and exclusive). -/
theorem type_trichotomy (hu : IsClearFirst F tC u) :
    (u = tC) ∨ (tC < u ∧ u ≤ wC) ∨ wC < u := by
  rcases eq_or_lt_of_le hu.1.1 with h | h
  · exact Or.inl h.symm
  · rcases le_or_gt u wC with h' | h'
    · exact Or.inr (Or.inl ⟨h, h'⟩)
    · exact Or.inr (Or.inr h')

#print axioms type_trichotomy

/-- **Type U** [L]: `u = tC`, the landing of `C ∪ F` is the landing of `C` (the block does not move it). -/
theorem type_U (hC : IsLanding C tC) (hcell : IsCell C tC wC) (hu : IsClearFirst F tC u) (h : u = tC) :
    IsLanding (C ∪ F) tC := by
  rw [← h]; exact landing_union_eq_u hC hcell hu (h ▸ hcell.2.1)

#print axioms type_U

/-- **Type D** [L]: `tC < u ≤ wC`, the landing of `C ∪ F` is `u`, strictly after the landing of `C`. -/
theorem type_D (hC : IsLanding C tC) (hcell : IsCell C tC wC) (hu : IsClearFirst F tC u) (h1 : tC < u)
    (h2 : u ≤ wC) : IsLanding (C ∪ F) u ∧ tC < u := ⟨landing_union_eq_u hC hcell hu h2, h1⟩

#print axioms type_D

end Decomposition

/-- Packaging with existence derived from a lonely point of `C ∪ F` (not assumed): the landing `tC` of `C`, its cell,
`u`, and a landing `t` of `C ∪ F` exist, and the decomposition holds.  Hypotheses: positivity, `C` nonempty, and one
positive lonely point of `C ∪ F` (a hypothesis on the arrangement, not a claim that one exists). -/
theorem decomposition_of_lonely {C F : Finset ℝ} (hCpos : ∀ d ∈ C, 0 < d) (hFpos : ∀ d ∈ F, 0 < d)
    (hne : C.Nonempty) (hex : ∃ s, 0 < s ∧ s ∈ lonelySet (C ∪ F)) :
    ∃ tC wC u t, IsLanding C tC ∧ IsCell C tC wC ∧ IsClearFirst F tC u ∧ IsLanding (C ∪ F) t ∧
      tC ≤ u ∧ u ≤ t ∧ (u ≤ wC → t = u) ∧ (wC < u → wC < t) ∧ (t = u ↔ u ∈ lonelySet C) := by
  obtain ⟨s, hs, hl⟩ := hex
  have hlC : s ∈ lonelySet C := ((lonelySet_union C F) ▸ hl : s ∈ lonelySet C ∩ lonelySet F).1
  have hlF : s ∈ lonelySet F := ((lonelySet_union C F) ▸ hl : s ∈ lonelySet C ∩ lonelySet F).2
  obtain ⟨tC, hC⟩ := exists_landing hCpos hne ⟨s, hs, hlC⟩
  obtain ⟨wC, hcell, -⟩ := (first_cell_iff hCpos hne).mp hC
  obtain ⟨u, hu⟩ := exists_clearFirst F tC ⟨s, hC.2 ⟨hs, hlC⟩, hlF⟩
  have hUpos : ∀ d ∈ C ∪ F, 0 < d := by
    intro d hd
    rcases Finset.mem_union.mp hd with h | h
    · exact hCpos d h
    · exact hFpos d h
  obtain ⟨t, ht⟩ := exists_landing hUpos (hne.mono Finset.subset_union_left) ⟨s, hs, hl⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := landing_decomposition hC hcell hu ht
  exact ⟨tC, wC, u, t, hC, hcell, hu, ht, h1, h2, h3, h4, h5⟩

#print axioms decomposition_of_lonely

/-- **Cascade form of (1)** [L]: for an arrangement whose subject's disparities split as `C ∪ F`, if the cascade from
the bound `1/(8 d_min)` reaches `t⋆` and `u ≤ w_C`, then `t⋆ = u`; if `w_C < u` then `t⋆ > w_C`. -/
theorem cascade_landing_decomposition {v : Fin 8 → ℝ} (hv : IsArrangement v) {k : Fin 8} {m : ℝ}
    (hm : IsDmin v k m) {C F : Finset ℝ} (hsplit : disparitySet v k = C ∪ F) {tC wC u tStar : ℝ}
    (hC : IsLanding C tC) (hcell : IsCell C tC wC) (hu : IsClearFirst F tC u)
    (hr : Where.CascadeReaches (disparitySet v k) (1 / (8 * m)) tStar) :
    (u ≤ wC → tStar = u) ∧ (wC < u → wC < tStar) := by
  have ht := cascade_landing_isLanding_arr hv hm hr
  rw [hsplit] at ht
  obtain ⟨-, -, h3, h4, -⟩ := landing_decomposition hC hcell hu ht
  exact ⟨h3, h4⟩

#print axioms cascade_landing_decomposition

/-! ## (2) One block runner: where `u` is, and the displacement formula -/

theorem mem_lonelySet_singleton {x s : ℝ} : s ∈ lonelySet {x} ↔ (1 / 8 : ℝ) ≤ distInt (x * s) := by
  simp [lonelySet, Cascade.LonelyAt]

#print axioms mem_lonelySet_singleton

/-- A runner clear at `a` is its own first clear point at or after `a` [L]. -/
theorem clearFirst_single_clear {x a : ℝ} (h : (1 / 8 : ℝ) ≤ distInt (x * a)) : IsClearFirst {x} a a :=
  ⟨⟨le_rfl, mem_lonelySet_singleton.mpr h⟩, fun _ hs => hs.1⟩

#print axioms clearFirst_single_clear

/-- A runner in the way at `a` has its next opening as first clear point at or after `a` [L]. -/
theorem clearFirst_single_inWay {x a : ℝ} (hx : 0 < x) (hw : InWay x a) :
    IsClearFirst {x} a (nextOpening x a) := by
  refine ⟨⟨(Cascade.lt_nextOpening hx hw).le, mem_lonelySet_singleton.mpr
    (Cascade.not_inWay_iff.mp (Cascade.not_inWay_at_nextOpening hx))⟩, ?_⟩
  rintro s ⟨has, hs⟩
  by_contra hlt
  push Not at hlt
  have := Cascade.inWay_until_opening hx hw has hlt
  exact Cascade.not_inWay_iff.mpr (mem_lonelySet_singleton.mp hs) this

#print axioms clearFirst_single_inWay

/-- The push is shorter than a quarter of a lap of `x`: `nextOpening x a < a + 1/(4x)` for `x` in the way [L]. -/
theorem nextOpening_lt {x a : ℝ} (hx : 0 < x) (hw : InWay x a) : nextOpening x a < a + 1 / (4 * x) := by
  obtain ⟨k, hk⟩ := Cascade.exists_near_int hw
  rw [Cascade.nextOpening_eq hk]
  have h1 := (abs_lt.mp hk).1
  have e : a + 1 / (4 * x) = (x * a + 1 / 4) / x := by field_simp
  rw [e]
  exact div_lt_div_of_pos_right (by linarith) hx

#print axioms nextOpening_lt

section OneBlock

variable {C : Finset ℝ} {tC wC u x : ℝ}

/-- **(2a) Type X for one block runner, exactly** [L]: `w_C < u` iff `x` is in the way at `t_C` and its next opening is
beyond `w_C`.  (Equivalently, `x` is in the way on all of the cell.) -/
theorem typeX_single_iff (hcell : IsCell C tC wC) (hx : 0 < x) (hu : IsClearFirst {x} tC u) :
    wC < u ↔ InWay x tC ∧ wC < nextOpening x tC := by
  by_cases hw : InWay x tC
  · have := hu.unique (clearFirst_single_inWay hx hw)
    rw [this]; simp [hw]
  · have := hu.unique (clearFirst_single_clear (Cascade.not_inWay_iff.mp hw))
    rw [this]; simp [hw]; exact hcell.2.1

#print axioms typeX_single_iff

/-- **(2b) Type X forces a narrow cell** [L]: if `w_C < u` then `w_C − t_C < 1/(4x)`, i.e. `4·L·x < 1`. -/
theorem typeX_imp_narrow (hcell : IsCell C tC wC) (hx : 0 < x) (hu : IsClearFirst {x} tC u) (h : wC < u) :
    wC - tC < 1 / (4 * x) := by
  obtain ⟨hw, hn⟩ := (typeX_single_iff hcell hx hu).mp h
  have := nextOpening_lt hx hw
  linarith

#print axioms typeX_imp_narrow

/-- **(2c) A wide cell is never type X** [L]: if `1/(4x) ≤ w_C − t_C` then `u < w_C`. -/
theorem not_typeX_of_wide (hx : 0 < x) (hu : IsClearFirst {x} tC u) (hwide : 1 / (4 * x) ≤ wC - tC) :
    u < wC := by
  have hq : 0 < 1 / (4 * x) := by positivity
  by_cases hw : InWay x tC
  · have := hu.unique (clearFirst_single_inWay hx hw)
    rw [this]
    have := nextOpening_lt hx hw
    linarith
  · have := hu.unique (clearFirst_single_clear (Cascade.not_inWay_iff.mp hw))
    rw [this]; linarith

#print axioms not_typeX_of_wide

/-- **(2d) Landing of `C ∪ {x}` for a wide cell** [L]: if `1/(4x) ≤ w_C − t_C` the landing is `t_C` when `x` is clear
at `t_C` and the next opening of `x` after `t_C` when it is in the way. -/
theorem single_block_landing (hC : IsLanding C tC) (hcell : IsCell C tC wC) (hx : 0 < x)
    (hwide : 1 / (4 * x) ≤ wC - tC) :
    IsLanding (C ∪ {x}) (if InWay x tC then nextOpening x tC else tC) := by
  by_cases hw : InWay x tC
  · rw [if_pos hw]
    have hu := clearFirst_single_inWay hx hw
    exact landing_union_eq_u hC hcell hu (not_typeX_of_wide hx hu hwide).le
  · rw [if_neg hw]
    have hu := clearFirst_single_clear (Cascade.not_inWay_iff.mp hw) (x := x) (a := tC)
    exact landing_union_eq_u hC hcell hu hcell.2.1

#print axioms single_block_landing

end OneBlock

/-! ### The displacement formula at the bound `t_C = 1/(8m)` (R coordinate `R = 8 m t`) -/

section Bound

variable {m x : ℝ}

theorem distInt_bound (hm : 0 < m) : distInt (x * (1 / (8 * m))) = |sres m x| / (8 * m) := by
  unfold distInt sres
  have e : x * (1 / (8 * m)) = x / (8 * m) := by ring
  rw [e]
  have e2 : x / (8 * m) - ((round (x / (8 * m)) : ℤ) : ℝ) = (x - 8 * m * (round (x / (8 * m)) : ℝ)) / (8 * m) := by
    field_simp
  rw [e2, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 8 * m)]

#print axioms distInt_bound

/-- **At the bound, `x` is in the way iff `|s| < m`**, `s = x − 8m·round(x/(8m))` the signed residue [L]. -/
theorem inWay_bound_iff (hm : 0 < m) : InWay x (1 / (8 * m)) ↔ |sres m x| < m := by
  unfold InWay
  rw [distInt_bound hm, div_lt_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

#print axioms inWay_bound_iff

/-- The same in the record's terms [L]: `x` is clear at `t = 1/(8m)` iff `8·frac(x/(8m)) ∈ [1, 7]`, i.e. the
reading `ρ = x/m` has residue `ρ mod 8 ∈ [1, 7]`. -/
theorem clear_bound_iff_residue :
    ¬ InWay x (1 / (8 * m)) ↔ 1 ≤ 8 * Int.fract (x / m / 8) ∧ 8 * Int.fract (x / m / 8) ≤ 7 := by
  rw [Cascade.not_inWay_iff, Localisation.clear_iff_fract]
  have e : x * (1 / (8 * m)) = x / m / 8 := by ring
  rw [e]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

#print axioms clear_bound_iff_residue

/-- **The displaced start in R coordinates** [L]: if `x` is in the way at `1/(8m)`, then
`8m · nextOpening x (1/(8m)) = 1 + (m − s)/x` with `s = sres m x` (so `R* = 1 + (m − s)/x`). -/
theorem nextOpening_bound (_hm : 0 < m) (hx : 0 < x) (hw : InWay x (1 / (8 * m))) :
    8 * m * nextOpening x (1 / (8 * m)) = 1 + (m - sres m x) / x := by
  have e : x * (1 / (8 * m)) = x / (8 * m) := by ring
  have hk : |x * (1 / (8 * m)) - ((round (x / (8 * m)) : ℤ) : ℝ)| < 1 / 8 := by
    unfold InWay distInt at hw
    rw [e] at hw ⊢
    exact hw
  rw [Cascade.nextOpening_eq hk]
  unfold sres
  field_simp
  ring

#print axioms nextOpening_bound

/-- **(2e) The first clear point of one runner from the bound, in R coordinates** [L]: if `u` is the first point at or
after `1/(8m)` that is clear for `x`, then `8m·u = 1` when `|s| ≥ m` and `8m·u = 1 + (m − s)/x` when `|s| < m`,
`s = x − 8m·round(x/(8m))`.  No hypothesis on `x` besides positivity. -/
theorem u_at_bound (hm : 0 < m) (hx : 0 < x) {u : ℝ} (hu : IsClearFirst {x} (1 / (8 * m)) u) :
    8 * m * u = if |sres m x| < m then 1 + (m - sres m x) / x else 1 := by
  by_cases hw : InWay x (1 / (8 * m))
  · have h1 := hu.unique (clearFirst_single_inWay hx hw)
    rw [h1, nextOpening_bound hm hx hw, if_pos ((inWay_bound_iff hm).mp hw)]
  · have h1 := hu.unique (clearFirst_single_clear (Cascade.not_inWay_iff.mp hw))
    rw [h1, if_neg (fun h => hw ((inWay_bound_iff hm).mpr h))]
    field_simp

#print axioms u_at_bound

/-- **(2f) The displacement formula for a general core with `R_C = 1`** [L]: if `C` has landing `t_C = 1/(8m)` with cell
`[t_C, w_C]`, and `1/(4x) ≤ w_C − t_C`, then the landing of `C ∪ {x}` is the first clear point `u` of `x` from `t_C`
and `8m·u` is given by (2e).  The hypothesis on the cell width is the only condition. -/
theorem core_displacement {C : Finset ℝ} {tC wC m x : ℝ} (hC : IsLanding C tC) (hcell : IsCell C tC wC)
    (hm : 0 < m) (hbound : tC = 1 / (8 * m)) (hx : 0 < x) (hwide : 1 / (4 * x) ≤ wC - tC) :
    ∃ u, IsClearFirst {x} tC u ∧ IsLanding (C ∪ {x}) u ∧
      8 * m * u = if |sres m x| < m then 1 + (m - sres m x) / x else 1 := by
  by_cases hw : InWay x tC
  · have hu := clearFirst_single_inWay hx hw
    refine ⟨_, hu, landing_union_eq_u hC hcell hu (not_typeX_of_wide hx hu hwide).le, ?_⟩
    exact u_at_bound hm hx (hbound ▸ hu)
  · have hu := clearFirst_single_clear (Cascade.not_inWay_iff.mp hw) (x := x) (a := tC)
    refine ⟨_, hu, landing_union_eq_u hC hcell hu hcell.2.1, ?_⟩
    exact u_at_bound hm hx (hbound ▸ hu)

#print axioms core_displacement

/-- **The multiple case** [L]: `x = 8mk` (`k` an integer) is in the way at the bound with residue `s = 0`, and the
first clear point has `R* = 1 + m/x`. -/
theorem u_multiple (hm : 0 < m) (hx : 0 < x) (k : ℤ) (hk : x = 8 * m * k) {u : ℝ}
    (hu : IsClearFirst {x} (1 / (8 * m)) u) : 8 * m * u = 1 + m / x := by
  have hr : x / (8 * m) = (k : ℝ) := by rw [hk]; field_simp
  have hs : sres m x = 0 := by
    unfold sres; rw [hr, round_intCast, hk]; ring
  have := u_at_bound hm hx hu
  rw [hs, abs_zero, if_pos hm] at this
  rw [this]; ring

#print axioms u_multiple

/-! ### The singleton core `C = {m}` -/

theorem singleton_isCell (hm : 0 < m) : IsCell {m} (1 / (8 * m)) (7 / (8 * m)) := by
  have h := window_isCell hm 0
  have e1 : winLo m (((0 : ℕ) : ℤ)) = 1 / (8 * m) := by unfold winLo; push_cast; field_simp; ring
  have e2 : winHi m (((0 : ℕ) : ℤ)) = 7 / (8 * m) := by unfold winHi; push_cast; field_simp; ring
  rw [e1, e2] at h
  exact h

#print axioms singleton_isCell

theorem singleton_isLanding (hm : 0 < m) : IsLanding {m} (1 / (8 * m)) := by
  have hc := singleton_isCell hm
  have hb : 0 < 1 / (8 * m) := by positivity
  refine ⟨⟨hb, hc.2.2.1 ⟨le_rfl, hc.2.1⟩⟩, fun s hs => ?_⟩
  exact Cascade.bound_le_of_lonely (Finset.mem_singleton_self m) hm hs.2 hs.1

#print axioms singleton_isLanding

/-- **(2) The displacement formula for the singleton core** [L]: for `C = {m}` and a block `{x}` with `m ≤ 3x`
(in particular every `x ≥ m`), the landing of `{m} ∪ {x}` is the first clear point `u` of `x` from `1/(8m)`, with
`R* = 8m·u` equal to `1` if `|s| ≥ m` (that is, the residue of `x/m` modulo 8 lies in `[1, 7]`) and to
`1 + (m − s)/x` if `|s| < m`, where `s = x − 8m·round(x/(8m))` is the signed residue of `x` modulo `8m`. -/
theorem singleton_core_displacement (hm : 0 < m) (hx : 0 < x) (hmx : m ≤ 3 * x) :
    ∃ u, IsLanding ({m} ∪ {x}) u ∧
      8 * m * u = if |sres m x| < m then 1 + (m - sres m x) / x else 1 := by
  have hwide : 1 / (4 * x) ≤ 7 / (8 * m) - 1 / (8 * m) := by
    rw [div_sub_div_same, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  obtain ⟨u, -, hL, hR⟩ := core_displacement (singleton_isLanding hm) (singleton_isCell hm) hm rfl hx hwide
  exact ⟨u, hL, hR⟩

#print axioms singleton_core_displacement

/-- **Instance: `C = {1}`, `x = 8k` gives `R* = 1 + 1/x`** [L] (record: AB's `R* = 1 + 1/x`). -/
theorem singleton_one_multiple (k : ℕ) (hk : 1 ≤ k) :
    ∃ u, IsLanding ({1} ∪ {(8 * k : ℝ)}) u ∧ 8 * 1 * u = 1 + 1 / (8 * k : ℝ) := by
  have hx : (0 : ℝ) < 8 * k := by have : (1 : ℝ) ≤ k := by exact_mod_cast hk
                                  linarith
  obtain ⟨u, hL, hR⟩ := singleton_core_displacement (m := 1) (x := 8 * k) one_pos hx (by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith)
  refine ⟨u, hL, ?_⟩
  have hs : sres 1 (8 * k : ℝ) = 0 := by
    unfold sres
    have : (8 * (k : ℝ)) / (8 * 1) = ((k : ℤ) : ℝ) := by push_cast; ring
    rw [this, round_intCast]; push_cast; ring
  rw [hs, abs_zero, if_pos one_pos] at hR
  rw [hR]; ring

#print axioms singleton_one_multiple

end Bound

/-! ## (3) The exceptions: a degenerate cell (`L_C = 0`) and a narrow cell (`4·L_C·x < 1`) -/

/-- A closed interval of the lonely set whose left end is an opening and whose right end is an entry is a cell [L]
(the converse direction of `cell_left_end_is_opening` / `cell_right_end_is_entry`). -/
theorem isCell_of_ends {ds : Finset ℝ} {x y u w : ℝ} {k k' : ℤ} (hx : x ∈ ds) (hy : y ∈ ds) (hx0 : 0 < x)
    (hy0 : 0 < y) (hu : x * u = (k : ℝ) + 1 / 8) (hw : y * w = (k' : ℝ) + 7 / 8) (hu0 : 0 < u) (hle : u ≤ w)
    (hsub : Set.Icc u w ⊆ lonelySet ds) : IsCell ds u w := by
  refine ⟨hu0, hle, hsub, ?_, ?_⟩
  · intro u' hu' hsub'
    set s := max u' (u - 1 / (8 * x)) with hsdef
    have hq : 0 < 1 / (8 * x) := by positivity
    have hq' : 1 / (8 * x) < 1 / (4 * x) := by
      apply one_div_lt_one_div_of_lt (by positivity); linarith
    have hs1 : u - 1 / (4 * x) < s := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hs2 : s < u := max_lt hu' (by linarith)
    exact not_lonely_of_inWay hx (inWay_before_opening hx0 hu hs1 hs2)
      (hsub' ⟨le_max_left _ _, le_trans hs2.le hle⟩)
  · intro w' hw' hsub'
    set s := min w' (w + 1 / (8 * y)) with hsdef
    have hq : 0 < 1 / (8 * y) := by positivity
    have hq' : 1 / (8 * y) < 1 / (4 * y) := by
      apply one_div_lt_one_div_of_lt (by positivity); linarith
    have hs1 : w < s := lt_min hw' (by linarith)
    have hs2 : s < w + 1 / (4 * y) := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    exact not_lonely_of_inWay hy (inWay_after_entry hy0 hw hs1 hs2)
      (hsub' ⟨le_trans hle hs1.le, min_le_left _ _⟩)

#print axioms isCell_of_ends

/-- **(3a) A cell is a single point iff some runner of `C` reads exactly `k + 7/8` at `t_C`** [L].  (`→`: the right end
of a cell is an entry, `cell_right_end_is_entry`.  `←`: a runner at `k + 7/8` is in the way just after, so the cell
cannot extend.)  The opener at `t_C` reads `1/8` (`cell_left_end_is_opening`) and is a different runner
(`degenerate_opener_ne_closer`): the cell collapses when one runner opens at the instant another closes. -/
theorem cell_degenerate_iff {C : Finset ℝ} (hpos : ∀ d ∈ C, 0 < d) {t w : ℝ} (h : IsCell C t w) :
    w = t ↔ ∃ z ∈ C, ∃ k : ℤ, z * t = (k : ℝ) + 7 / 8 := by
  constructor
  · intro hwt
    obtain ⟨y, hy, k', -, hyw, -, -⟩ := cell_right_end_is_entry hpos h
    exact ⟨y, hy, k', by rw [← hwt]; exact_mod_cast hyw⟩
  · rintro ⟨z, hz, k, hzt⟩
    by_contra hne
    have hlt : t < w := lt_of_le_of_ne h.2.1 (Ne.symm hne)
    have hz0 := hpos z hz
    have hq : 0 < 1 / (8 * z) := by positivity
    have hq' : 1 / (8 * z) < 1 / (4 * z) := by
      apply one_div_lt_one_div_of_lt (by positivity); linarith
    set s := min w (t + 1 / (8 * z)) with hsdef
    have hs1 : t < s := lt_min hlt (by linarith)
    have hs2 : s < t + 1 / (4 * z) := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    exact not_lonely_of_inWay hz (inWay_after_entry hz0 hzt hs1 hs2)
      (h.2.2.1 ⟨hs1.le, min_le_left _ _⟩)

#print axioms cell_degenerate_iff

/-- **(3b) Degenerate cell at the bound** [L]: if `t_C = 1/(8m)` then some `z ∈ C` reads exactly `k + 7/8` at `t_C` iff
some `z ∈ C` equals `m(8k + 7)`: the record's `L_C = 0` at `R_C = 1` is the presence of `7m, 15m, 23m, …` in the core. -/
theorem degenerate_at_bound {C : Finset ℝ} {t m : ℝ} (hm : 0 < m) (ht : t = 1 / (8 * m)) :
    (∃ z ∈ C, ∃ k : ℤ, z * t = (k : ℝ) + 7 / 8) ↔ ∃ z ∈ C, ∃ k : ℤ, z = m * (8 * k + 7) := by
  subst ht
  constructor
  · rintro ⟨z, hz, k, h⟩
    refine ⟨z, hz, k, ?_⟩
    field_simp at h
    linarith
  · rintro ⟨z, hz, k, h⟩
    refine ⟨z, hz, k, ?_⟩
    rw [h]; field_simp

#print axioms degenerate_at_bound

/-- **(3c) Type X at a degenerate cell, exactly** [L]: if `w_C = t_C`, then `w_C < u` iff some runner of `F` is in the
way at `t_C`.  The size of the block runner is irrelevant: the cell has no width to absorb the push. -/
theorem typeX_degenerate_iff {F : Finset ℝ} {tC wC u : ℝ} (hu : IsClearFirst F tC u) (hdeg : wC = tC) :
    wC < u ↔ ∃ x ∈ F, InWay x tC := by
  rw [typeX_iff hu]
  constructor
  · intro h
    by_contra hno
    push Not at hno
    exact h ⟨tC, ⟨le_rfl, hdeg.ge⟩, fun x hx => Cascade.not_inWay_iff.mp (hno x hx)⟩
  · rintro ⟨x, hx, hw⟩ ⟨s, hs, hl⟩
    have hst : s = tC := le_antisymm (hdeg ▸ hs.2) hs.1
    rw [hst] at hl
    exact Cascade.not_inWay_iff.mpr (hl x hx) hw

#print axioms typeX_degenerate_iff

/-- **(3d) The exception unifies with the narrow cell** [L]: for one block runner, `w_C < u` implies
`4·(w_C − t_C)·x < 1` (`typeX_imp_narrow`); `L_C = 0` is the case `4·L·x = 0`, where it holds for EVERY in-the-way `x`
(`typeX_degenerate_iff`), and `L_C > 0` gives type X only through `x` with `x·(w_C − t_C)` below the remaining
distance to its opening (`typeX_single_iff`). -/
theorem typeX_single_degenerate {tC wC u x : ℝ} (hu : IsClearFirst {x} tC u) (hdeg : wC = tC) : wC < u ↔ InWay x tC := by
  rw [typeX_degenerate_iff hu hdeg]; simp

#print axioms typeX_single_degenerate

/-! ### Exact examples -/

theorem inWay_of_bounds {x s : ℝ} (N : ℤ) (h1 : (N : ℝ) - 1 / 8 < x * s) (h2 : x * s < (N : ℝ) + 1 / 8) :
    InWay x s := inWay_of_near N (by rw [abs_lt]; constructor <;> linarith)

#print axioms inWay_of_bounds

/-- **`C = {1, 7}`, `x = 8`: the touch at `R = 1`, and why `R* = 1 + 1/x` fails** [L].  The core's cell is the single
point `[1/8, 1/8]` (the runner `7` reads exactly `7/8` there); `8` is in the way at `1/8`, its next opening is `9/64`,
beyond the cell, so the block is type X; but `7` is in the way at `9/64` (it reads `63/64`), and the landing of
`{1, 7, 8}` is `9/56` (`R = 9/7`, the exit of runner `7`'s zone), not `9/64` (`R = 9/8`). -/
theorem touch_block_example :
    IsCell ({1, 7} : Finset ℝ) (1 / 8) (1 / 8) ∧ IsLanding ({1, 7} : Finset ℝ) (1 / 8) ∧
    IsClearFirst {(8 : ℝ)} (1 / 8) (9 / 64) ∧ (1 / 8 : ℝ) < 9 / 64 ∧
    IsLanding (({1, 7} : Finset ℝ) ∪ {8}) (9 / 56) ∧ (9 / 64 : ℝ) < 9 / 56 := by
  have hl : (1 / 8 : ℝ) ∈ lonelySet ({1, 7} : Finset ℝ) := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl <;> exact Localisation.clear_of_window 0 (by norm_num) (by norm_num)
  have h1 : (1 : ℝ) ∈ ({1, 7} : Finset ℝ) := by simp
  have h7 : (7 : ℝ) ∈ ({1, 7} : Finset ℝ) := by simp
  have hcell : IsCell ({1, 7} : Finset ℝ) (1 / 8) (1 / 8) := by
    refine isCell_of_ends (k := 0) (k' := 0) h1 h7 one_pos (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) le_rfl ?_
    intro s hs
    have : s = 1 / 8 := le_antisymm hs.2 hs.1
    rw [this]; exact hl
  refine ⟨hcell, ⟨⟨by norm_num, hl⟩, fun s hs => ?_⟩, ?_, by norm_num, ?_, by norm_num⟩
  · have := Cascade.bound_le_of_lonely (m := 1) h1 one_pos hs.2 hs.1
    norm_num at this; exact this
  · have hw : InWay (8 : ℝ) (1 / 8) := inWay_of_bounds 1 (by norm_num) (by norm_num)
    have hno : nextOpening (8 : ℝ) (1 / 8) = 9 / 64 := by
      rw [Cascade.nextOpening_eq (k := 1) (by norm_num)]; norm_num
    rw [← hno]
    exact clearFirst_single_inWay (by norm_num) hw
  · refine ⟨⟨by norm_num, ?_⟩, fun s hs => ?_⟩
    · rw [lonelySet_union]
      refine ⟨?_, ?_⟩
      · intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl
        · exact Localisation.clear_of_window 0 (by norm_num) (by norm_num)
        · exact Localisation.clear_of_window 1 (by norm_num) (by norm_num)
      · intro d hd
        simp only [Finset.mem_singleton] at hd
        subst hd
        exact Localisation.clear_of_window 1 (by norm_num) (by norm_num)
    · obtain ⟨hs0, hsl⟩ := hs
      rw [lonelySet_union] at hsl
      have hb : (1 / 8 : ℝ) ≤ s := by
        have := Cascade.bound_le_of_lonely (m := 1) h1 one_pos hsl.1 hs0
        norm_num at this; exact this
      by_contra hlt
      push Not at hlt
      by_cases hc : s < 9 / 64
      · have hw : InWay (8 : ℝ) s := inWay_of_bounds 1 (by push_cast; linarith) (by push_cast; linarith)
        exact Cascade.not_inWay_iff.mpr (hsl.2 8 (by simp)) hw
      · push Not at hc
        have hw : InWay (7 : ℝ) s := inWay_of_bounds 1 (by push_cast; linarith) (by push_cast; linarith)
        exact Cascade.not_inWay_iff.mpr (hsl.1 7 h7) hw

#print axioms touch_block_example

/-- **`C = {2, 12}`, `x = 15`: type X with a cell of positive length `1/96`, `4·L·x = 5/8 < 1`** [L].  The cell is
`[1/16, 7/96]` (opener `2`, closer `12`); `15` is in the way on all of it (it reads `15/16` at `1/16` and
`35/32` at `7/96`, still inside `(7/8, 9/8)`), its next opening `3/40` is beyond `7/96`; the landing of `{2, 12, 15}`
is `3/32` (`R = 3/2`, the exit of runner `12`'s zone), not `3/40` (`R = 6/5`, which is
`1 + (m − s)/x` with `m = 2`, `s = −1`). -/
theorem narrow_cell_example :
    IsCell ({2, 12} : Finset ℝ) (1 / 16) (7 / 96) ∧ IsLanding ({2, 12} : Finset ℝ) (1 / 16) ∧
    IsClearFirst {(15 : ℝ)} (1 / 16) (3 / 40) ∧ (7 / 96 : ℝ) < 3 / 40 ∧
    4 * ((7 / 96 : ℝ) - 1 / 16) * 15 < 1 ∧ (1 / 16 : ℝ) < 7 / 96 ∧
    IsLanding (({2, 12} : Finset ℝ) ∪ {15}) (3 / 32) := by
  have h2 : (2 : ℝ) ∈ ({2, 12} : Finset ℝ) := by simp
  have h12 : (12 : ℝ) ∈ ({2, 12} : Finset ℝ) := by simp
  have hsub : Set.Icc (1 / 16 : ℝ) (7 / 96) ⊆ lonelySet ({2, 12} : Finset ℝ) := by
    intro s hs d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact Localisation.clear_of_window 0 (by push_cast; linarith [hs.1]) (by push_cast; linarith [hs.2])
    · exact Localisation.clear_of_window 0 (by push_cast; linarith [hs.1]) (by push_cast; linarith [hs.2])
  have hcell : IsCell ({2, 12} : Finset ℝ) (1 / 16) (7 / 96) :=
    isCell_of_ends (k := 0) (k' := 0) h2 h12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hsub
  refine ⟨hcell, ⟨⟨by norm_num, hcell.2.2.1 ⟨le_rfl, hcell.2.1⟩⟩, fun s hs => ?_⟩, ?_, by norm_num,
    by norm_num, by norm_num, ?_⟩
  · have := Cascade.bound_le_of_lonely (m := 2) h2 (by norm_num) hs.2 hs.1
    norm_num at this; exact this
  · have hw : InWay (15 : ℝ) (1 / 16) := inWay_of_bounds 1 (by norm_num) (by norm_num)
    have hno : nextOpening (15 : ℝ) (1 / 16) = 3 / 40 := by
      rw [Cascade.nextOpening_eq (k := 1) (by norm_num)]; norm_num
    rw [← hno]
    exact clearFirst_single_inWay (by norm_num) hw
  · refine ⟨⟨by norm_num, ?_⟩, fun s hs => ?_⟩
    · rw [lonelySet_union]
      refine ⟨?_, ?_⟩
      · intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl
        · exact Localisation.clear_of_window 0 (by norm_num) (by norm_num)
        · exact Localisation.clear_of_window 1 (by norm_num) (by norm_num)
      · intro d hd
        simp only [Finset.mem_singleton] at hd
        subst hd
        exact Localisation.clear_of_window 1 (by norm_num) (by norm_num)
    · obtain ⟨hs0, hsl⟩ := hs
      rw [lonelySet_union] at hsl
      have hb : (1 / 16 : ℝ) ≤ s := by
        have := Cascade.bound_le_of_lonely (m := 2) h2 (by norm_num) hsl.1 hs0
        norm_num at this; exact this
      by_contra hlt
      push Not at hlt
      by_cases hc : s ≤ 7 / 96
      · have hw : InWay (15 : ℝ) s := inWay_of_bounds 1 (by push_cast; linarith) (by push_cast; linarith)
        exact Cascade.not_inWay_iff.mpr (hsl.2 15 (by simp)) hw
      · push Not at hc
        have hw : InWay (12 : ℝ) s := inWay_of_bounds 1 (by push_cast; linarith) (by push_cast; linarith)
        exact Cascade.not_inWay_iff.mpr (hsl.1 12 h12) hw

#print axioms narrow_cell_example

end Fresh.BlockLanding
