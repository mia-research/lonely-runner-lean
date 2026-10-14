import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.LonelyCells
import Fresh.Carving
import Fresh.BlockLanding

/-!
# Multi-runner blocks: the zones of `F` against the cell of `C`, and the next-cell landing recursion (Task AG)

Written 2026-10-09.  Imports `Mathlib` and the Fresh modules `Framework`, `Cascade`, `LonelyCells`, `Carving`,
`BlockLanding`; nothing from the existing `LonelyRunner` repo.  Exact reals only; every disparity is positive.  Every
statement is symbolic, for all finite sets.  Nothing here asserts that a landing, a cell or `u` exists: each theorem
is conditional on the object it names.

Setting (as in `Fresh.BlockLanding`).  `C`, `F` finite sets of positive disparities, `[a, b]` a cell of `C`, `u` the
least point at or after `a` that is lonely for `F` (`IsClearFirst F a u`).  The open ZONES of a runner `x` are
`zone x N = ((N - 1/8)/x, (N + 1/8)/x)`: its entry before lap `N` to its opening of lap `N`.

Findings.
* (1) The ZONE FORM of `u`: `clearFirst_zone_form` says `u` is the least point at or after `a` that lies in no zone
  of `F`, i.e. `[a, u)` is covered by zones of `F` and `u` is in none.  `typeX_iff_cover`: `b < u` iff the zones of `F`
  cover `[a, b]` (this restates `BlockLanding.typeX_iff` through `Carving.notMem_clearSet_iff`).
  Single zone: `cover_singleton_iff` (one runner covers `[a,b]` iff one of its zones does), `single_zone_cover`,
  `clearFirst_ge_opening` (a zone holding `a` pushes `u` to at least its opening), `nextOpening_le_u`, and the
  cascade's own first move: `clearFirst_push` (`t1 <= u`, with equality iff `t1` is lonely for `F`).
  Two zones: `cover_two_iff` (exact interval statement), `two_zone_cover_iff`, `two_zone_needed_iff` (neither
  alone suffices: `a1 < t <= b1 < a2 <= w < b2`, i.e. the cell contains the entry of the second and the opening of the
  first), `two_zone_cover`.  The coverings are tagged `[PROVISIONAL: covering]` where they are used as steps.
* (2) The NEXT-CELL recursion: `landing_iff_first_open_cell` (exact): `t` is the landing of `C ∪ F` iff there is a cell
  `[a, b]` of `C` such that every cell of `C` starting before `a` has no `F`-lonely point (`PrefixCovered`, the "F-zones
  cover those cells" step), `u` is the first `F`-clear point from `a`, `u <= b`, and `t = u`.
  `landing_recursion`: the one-step form (`u <= b` gives the landing `u`; `b < u` makes every lonely point `> b`).
  `prefixCovered_first`, `prefixCovered_next`: the induction step along the ordered cells of `C`.
  `landing_past_cell`: if `b_C < u` for the first cell, the landing sits in a LATER cell `[a, b]` of `C` (`b_C < a`)
  with the same description.  `landing_past_least`: the landing is the least point at or after `w_C` lonely for `C`
  and for `F`.
* Instances: `touch_next_cell`, `narrow_next_cell` (the two recorded cases, whose landings `9/56`, `3/32` are in
  `BlockLanding`) exhibit the next cell.

Provenance.  The existing repo's counterpart is the block-landing material in `LRC/Cascade/Iteration.lean` and
`LRC/Spec/DoorFlank` (read for the idea only); every proof here was written for this file and none was copied that
was not understood.  `Fresh.BlockLanding` (landing_decomposition, typeX_iff) and `Fresh.Carving` (zones, cells_ordered)
are reused as stated.
-/

open Classical

namespace Fresh.BlockLanding2

open Fresh Fresh.LonelyCells Fresh.Carving Fresh.BlockLanding

/-! ## (1) Zone form of `u` and the covering statement -/

/-- The open zones of the runners of `F` cover `[a, b]`. -/
-- STANDING: DEFINITION
def ZoneCover (F : Finset ℝ) (a b : ℝ) : Prop :=
  ∀ s ∈ Set.Icc a b, ∃ x ∈ F, ∃ N : ℤ, s ∈ zone x N

theorem notMem_lonely_iff_zone {F : Finset ℝ} (hpos : ∀ d ∈ F, 0 < d) {s : ℝ} :
    s ∉ lonelySet F ↔ ∃ x ∈ F, ∃ N : ℤ, s ∈ zone x N := by
  rw [lonelySet_eq_iInter]
  simp only [Set.mem_iInter, not_forall]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, (notMem_clearSet_iff (hpos x hx)).mp h⟩
  · rintro ⟨x, hx, N, hN⟩
    exact ⟨x, hx, (notMem_clearSet_iff (hpos x hx)).mpr ⟨N, hN⟩⟩

#print axioms notMem_lonely_iff_zone

/-- **The zone form of `u`** [L]: `u` is the first point at or after `a` that lies in no zone of `F`; every point of
`[a, u)` lies in a zone of `F`. -/
theorem clearFirst_zone_form {F : Finset ℝ} (hpos : ∀ d ∈ F, 0 < d) {a u : ℝ} :
    IsClearFirst F a u ↔
      a ≤ u ∧ (¬ ∃ x ∈ F, ∃ N : ℤ, u ∈ zone x N) ∧
        ∀ s, a ≤ s → s < u → ∃ x ∈ F, ∃ N : ℤ, s ∈ zone x N := by
  constructor
  · rintro ⟨⟨hau, hl⟩, hle⟩
    refine ⟨hau, fun h => (notMem_lonely_iff_zone hpos).mpr h hl, fun s has hsu => ?_⟩
    exact (notMem_lonely_iff_zone hpos).mp (fun hl' => absurd (hle ⟨has, hl'⟩) (not_le.mpr hsu))
  · rintro ⟨hau, hz, hs⟩
    have hl : u ∈ lonelySet F := by
      by_contra h
      exact hz ((notMem_lonely_iff_zone hpos).mp h)
    refine ⟨⟨hau, hl⟩, fun s ⟨has, hls⟩ => ?_⟩
    by_contra hlt
    push Not at hlt
    exact (notMem_lonely_iff_zone hpos).mpr (hs s has hlt) hls

#print axioms clearFirst_zone_form

/-- **(1) `w_C < u` iff the zones of `F` cover the cell** [L] [PROVISIONAL: covering] (claim named: `typeX_iff`; the
covering is the form `typeX_iff` takes after `notMem_clearSet_iff`). -/
theorem typeX_iff_cover {F : Finset ℝ} (hpos : ∀ d ∈ F, 0 < d) {a b u : ℝ} (hu : IsClearFirst F a u) :
    b < u ↔ ZoneCover F a b := by
  rw [typeX_iff hu]
  constructor
  · intro h s hs
    exact (notMem_lonely_iff_zone hpos).mp (fun hl => h ⟨s, hs, hl⟩)
  · rintro h ⟨s, hs, hl⟩
    exact (notMem_lonely_iff_zone hpos).mpr (h s hs) hl

#print axioms typeX_iff_cover

/-- One runner covers `[a, b]` by its zones iff one single zone of it does [L]. -/
theorem cover_singleton_iff {x a b : ℝ} (hx : 0 < x) (hab : a ≤ b) :
    ZoneCover {x} a b ↔ ∃ N : ℤ, ((N : ℝ) - 1 / 8) / x < a ∧ b < ((N : ℝ) + 1 / 8) / x := by
  rw [← killed_iff hx hab]
  unfold ZoneCover
  constructor
  · intro h s hs hc
    obtain ⟨y, hy, N, hN⟩ := h s hs
    rw [Finset.mem_singleton] at hy
    subst hy
    exact Set.disjoint_left.mp (zone_disjoint_clearSet hx N) hN hc
  · intro h s hs
    exact ⟨x, Finset.mem_singleton_self x, (notMem_clearSet_iff hx).mp (h s hs)⟩

#print axioms cover_singleton_iff

/-- **Single-zone cover** [L]: if one zone of one runner of `F` contains `[a, b]`, the zones of `F` cover it. -/
theorem single_zone_cover {F : Finset ℝ} {x a b : ℝ} (hx : x ∈ F) {N : ℤ}
    (h1 : ((N : ℝ) - 1 / 8) / x < a) (h2 : b < ((N : ℝ) + 1 / 8) / x) : ZoneCover F a b :=
  fun s hs => ⟨x, hx, N, lt_of_lt_of_le h1 hs.1, lt_of_le_of_lt hs.2 h2⟩

#print axioms single_zone_cover

/-- **A zone holding `a` pushes `u` past its opening** [L]: if `a` lies in the zone of lap `N` of a runner `x ∈ F`,
then `(N + 1/8)/x ≤ u`. -/
theorem clearFirst_ge_opening {F : Finset ℝ} {a u x : ℝ} (hx : x ∈ F) {N : ℤ}
    (hu : IsClearFirst F a u) (h1 : ((N : ℝ) - 1 / 8) / x < a) (h2 : a < ((N : ℝ) + 1 / 8) / x)
    (hpos : ∀ d ∈ F, 0 < d) : ((N : ℝ) + 1 / 8) / x ≤ u := by
  by_contra h
  push Not at h
  exact (notMem_lonely_iff_zone hpos).mpr ⟨x, hx, N, lt_of_lt_of_le h1 hu.1.1, h⟩ hu.1.2

#print axioms clearFirst_ge_opening

/-- **A runner of `F` in the way at `a` pushes `u` to at least its next opening** [L]. -/
theorem nextOpening_le_u {F : Finset ℝ} {a u x : ℝ} (hx : x ∈ F) (hx0 : 0 < x) (hw : InWay x a)
    (hu : IsClearFirst F a u) : nextOpening x a ≤ u := by
  by_contra h
  push Not at h
  have hin := Cascade.inWay_until_opening hx0 hw hu.1.1 h
  exact Cascade.not_inWay_iff.mpr (hu.1.2 x hx) hin

#print axioms nextOpening_le_u

/-- `u = a` iff no runner of `F` is in the way at `a` [L]. -/
theorem clearFirst_eq_self_iff {F : Finset ℝ} {a u : ℝ} (hu : IsClearFirst F a u) :
    u = a ↔ ∀ x ∈ F, ¬ InWay x a := by
  constructor
  · intro h x hx
    rw [← h]
    exact Cascade.not_inWay_iff.mpr (hu.1.2 x hx)
  · intro h
    have hl : a ∈ lonelySet F := fun x hx => Cascade.not_inWay_iff.mp (h x hx)
    exact le_antisymm (hu.2 ⟨le_rfl, hl⟩) hu.1.1

#print axioms clearFirst_eq_self_iff

/-- **The cascade's first move bounds `u`, and `u` is that move exactly when it is lonely for `F`** [L]: if some
runner of `F` is in the way at `a` and `a → t1` is a cascade move for `F`, then `t1 ≤ u`, and `u = t1` iff `t1` is
lonely for `F`.  (This ties `u` to the cascade, the object.) -/
theorem clearFirst_push {F : Finset ℝ} (hpos : ∀ d ∈ F, 0 < d) {a u t1 : ℝ} (hu : IsClearFirst F a u)
    (hmv : IsMove F a t1) (hin : ∃ x ∈ F, InWay x a) : t1 ≤ u ∧ (u = t1 ↔ t1 ∈ lonelySet F) := by
  rcases hmv with ⟨hall, -⟩ | ⟨d, hd, hw, ht1, -⟩
  · obtain ⟨x, hx, hxw⟩ := hin
    exact absurd hxw (hall x hx)
  · have hle : t1 ≤ u := by rw [ht1]; exact nextOpening_le_u hd (hpos d hd) hw hu
    refine ⟨hle, ⟨fun h => h ▸ hu.1.2, fun hl => le_antisymm (hu.2 ⟨?_, hl⟩) hle⟩⟩
    rw [ht1]; exact (Cascade.lt_nextOpening (hpos d hd) hw).le

#print axioms clearFirst_push

/-! ### Two zones: the exact interval statement -/

/-- **Two open intervals cover `[t, w]`: exact condition** [L].  `A = (a1, a2)`, `B = (b1, b2)`.  Either one covers
alone, or `A` holds `t`, `B` holds `w` and they overlap (`b1 < a2`), or the same with the roles swapped. -/
theorem cover_two_iff {a1 a2 b1 b2 t w : ℝ} (htw : t ≤ w) :
    Set.Icc t w ⊆ Set.Ioo a1 a2 ∪ Set.Ioo b1 b2 ↔
      (a1 < t ∧ w < a2) ∨ (b1 < t ∧ w < b2) ∨ (a1 < t ∧ b1 < a2 ∧ w < b2) ∨ (b1 < t ∧ a1 < b2 ∧ w < a2) := by
  constructor
  · intro h
    have ht := h (show t ∈ Set.Icc t w from ⟨le_rfl, htw⟩)
    rcases ht with ⟨ta1, ta2⟩ | ⟨tb1, tb2⟩
    · by_cases hwa : w < a2
      · exact Or.inl ⟨ta1, hwa⟩
      · push Not at hwa
        have h2 := h (show a2 ∈ Set.Icc t w from ⟨ta2.le, hwa⟩)
        rcases h2 with ⟨x1, x2⟩ | ⟨y1, y2⟩
        · exact absurd x2 (lt_irrefl _)
        · by_cases hwb : w < b2
          · exact Or.inr (Or.inr (Or.inl ⟨ta1, y1, hwb⟩))
          · push Not at hwb
            have h3 := h (show b2 ∈ Set.Icc t w from ⟨by linarith, hwb⟩)
            rcases h3 with ⟨z1, z2⟩ | ⟨z1, z2⟩
            · linarith
            · exact absurd z2 (lt_irrefl _)
    · by_cases hwb : w < b2
      · exact Or.inr (Or.inl ⟨tb1, hwb⟩)
      · push Not at hwb
        have h2 := h (show b2 ∈ Set.Icc t w from ⟨tb2.le, hwb⟩)
        rcases h2 with ⟨y1, y2⟩ | ⟨x1, x2⟩
        · by_cases hwa : w < a2
          · exact Or.inr (Or.inr (Or.inr ⟨tb1, y1, hwa⟩))
          · push Not at hwa
            have h3 := h (show a2 ∈ Set.Icc t w from ⟨by linarith, hwa⟩)
            rcases h3 with ⟨z1, z2⟩ | ⟨z1, z2⟩
            · exact absurd z2 (lt_irrefl _)
            · linarith
        · exact absurd x2 (lt_irrefl _)
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) s hs
    · exact Or.inl ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · exact Or.inr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · by_cases hsa : s < a2
      · exact Or.inl ⟨by linarith [hs.1], hsa⟩
      · push Not at hsa
        exact Or.inr ⟨by linarith, by linarith [hs.2]⟩
    · by_cases hsb : s < b2
      · exact Or.inr ⟨by linarith [hs.1], hsb⟩
      · push Not at hsb
        exact Or.inl ⟨by linarith, by linarith [hs.2]⟩

#print axioms cover_two_iff

/-- **Two zones are needed: exact condition** [L].  `[t, w]` is covered by `A ∪ B` but by neither alone iff
`a1 < t ≤ b1 < a2 ≤ w < b2` or the same with `A`, `B` swapped.  In words: `A` holds `t`, the entry `b1` of `B` lies in
`[t, a2)`, the opening `a2` of `A` lies in `[b1, w]`, and `B` holds `w`. -/
theorem two_zone_needed_iff {a1 a2 b1 b2 t w : ℝ} (htw : t ≤ w) :
    (Set.Icc t w ⊆ Set.Ioo a1 a2 ∪ Set.Ioo b1 b2 ∧ ¬ Set.Icc t w ⊆ Set.Ioo a1 a2 ∧
        ¬ Set.Icc t w ⊆ Set.Ioo b1 b2) ↔
      (a1 < t ∧ t ≤ b1 ∧ b1 < a2 ∧ a2 ≤ w ∧ w < b2) ∨ (b1 < t ∧ t ≤ a1 ∧ a1 < b2 ∧ b2 ≤ w ∧ w < a2) := by
  have hI : ∀ {p q : ℝ}, Set.Icc t w ⊆ Set.Ioo p q ↔ p < t ∧ w < q := by
    intro p q
    constructor
    · intro h
      exact ⟨(h (show t ∈ Set.Icc t w from ⟨le_rfl, htw⟩)).1, (h (show w ∈ Set.Icc t w from ⟨htw, le_rfl⟩)).2⟩
    · rintro ⟨h1, h2⟩ s hs
      exact ⟨lt_of_lt_of_le h1 hs.1, lt_of_le_of_lt hs.2 h2⟩
  rw [hI, hI, cover_two_iff htw]
  constructor
  · rintro ⟨hc, hA, hB⟩
    rcases hc with c | c | ⟨c1, c2, c3⟩ | ⟨c1, c2, c3⟩
    · exact absurd c hA
    · exact absurd c hB
    · left
      refine ⟨c1, ?_, c2, ?_, c3⟩
      · by_contra h; push Not at h; exact hB ⟨h, c3⟩
      · by_contra h; push Not at h; exact hA ⟨c1, h⟩
    · right
      refine ⟨c1, ?_, c2, ?_, c3⟩
      · by_contra h; push Not at h; exact hA ⟨h, c3⟩
      · by_contra h; push Not at h; exact hB ⟨c1, h⟩
  · rintro (⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩)
    · exact ⟨Or.inr (Or.inr (Or.inl ⟨h1, h3, h5⟩)), fun ⟨_, h⟩ => by linarith, fun ⟨h, _⟩ => by linarith⟩
    · exact ⟨Or.inr (Or.inr (Or.inr ⟨h1, h3, h5⟩)), fun ⟨h, _⟩ => by linarith, fun ⟨_, h⟩ => by linarith⟩

#print axioms two_zone_needed_iff

/-- The zone of lap `N` is the open interval from the ENTRY of lap `N − 1` to the OPENING of lap `N` [L]. -/
theorem zone_eq_Ioo_entry_opening (d : ℝ) (N : ℤ) : zone d N = Set.Ioo (winHi d (N - 1)) (winLo d N) := by
  have := zone_succ_eq d (N - 1)
  rwa [sub_add_cancel] at this

#print axioms zone_eq_Ioo_entry_opening

/-- **Two zones cover `[t, w]`, in the framework's terms** [L]: for the zone of lap `N` of `x` and lap `M` of `y`,
`[t, w] ⊆ zone x N ∪ zone y M` iff one of them holds it, or `x`'s entry (before lap `N`) is before `t`, `y`'s entry
(before lap `M`) is before `x`'s opening of lap `N`, and `w` is before `y`'s opening of lap `M`; or the roles swapped. -/
theorem two_zone_cover_iff {x y t w : ℝ} {N M : ℤ} (htw : t ≤ w) :
    Set.Icc t w ⊆ zone x N ∪ zone y M ↔
      (winHi x (N - 1) < t ∧ w < winLo x N) ∨ (winHi y (M - 1) < t ∧ w < winLo y M) ∨
      (winHi x (N - 1) < t ∧ winHi y (M - 1) < winLo x N ∧ w < winLo y M) ∨
      (winHi y (M - 1) < t ∧ winHi x (N - 1) < winLo y M ∧ w < winLo x N) := by
  rw [zone_eq_Ioo_entry_opening, zone_eq_Ioo_entry_opening]
  exact cover_two_iff htw

#print axioms two_zone_cover_iff

/-- **Two-zone cover of the cell makes `w_C < u`** [L] [PROVISIONAL: covering] (claim named: `typeX_iff`, through
`typeX_iff_cover`): if `x, y ∈ F` and the zone of lap `N` of `x` and lap `M` of `y` cover `[a, b]` as in
`two_zone_cover_iff`, then `b < u`. -/
theorem two_zone_cover {F : Finset ℝ} (hpos : ∀ d ∈ F, 0 < d) {a b u x y : ℝ} {N M : ℤ} (hx : x ∈ F) (hy : y ∈ F)
    (hu : IsClearFirst F a u) (hab : a ≤ b)
    (h : Set.Icc a b ⊆ zone x N ∪ zone y M) : b < u := by
  rw [typeX_iff_cover hpos hu]
  intro s hs
  rcases h hs with h1 | h1
  · exact ⟨x, hx, N, h1⟩
  · exact ⟨y, hy, M, h1⟩

#print axioms two_zone_cover

/-! ## (2) The next-cell landing recursion -/

section Recursion

variable {C F : Finset ℝ}

/-- Every cell of `C` starting before `a` has no point lonely for `F`: the zones of `F` cover each such cell. -/
-- STANDING: DEFINITION
def PrefixCovered (C F : Finset ℝ) (a : ℝ) : Prop :=
  ∀ a' b' : ℝ, IsCell C a' b' → a' < a → ¬ ∃ s ∈ Set.Icc a' b', s ∈ lonelySet F

/-- The landing of `C` makes the prefix empty: nothing starts before the first cell [L]. -/
theorem prefixCovered_first (hCpos : ∀ d ∈ C, 0 < d) (hne : C.Nonempty) {tC : ℝ} (hC : IsLanding C tC) :
    PrefixCovered C F tC := by
  obtain ⟨w, -, hfirst⟩ := (first_cell_iff hCpos hne).mp hC
  intro a' b' hc' hlt
  exact absurd (hfirst a' b' hc') (not_le.mpr hlt)

#print axioms prefixCovered_first

/-- **One step of the recursion** [L] [PROVISIONAL: covering] (claim named: the next-cell landing recursion; the
covering is `PrefixCovered`, "the `F`-zones cover every earlier cell").  For a cell `[a, b]` of `C` with the prefix
covered and `u` the first `F`-clear point from `a`: every positive lonely point `s` of `C ∪ F` satisfies
`u ≤ b → u ≤ s` and `b < u → b < s`. -/
theorem prefix_landing_bound (hCpos : ∀ d ∈ C, 0 < d) (hne : C.Nonempty) {a b u : ℝ} (hcell : IsCell C a b)
    (hpre : PrefixCovered C F a) (hu : IsClearFirst F a u) {s : ℝ} (hs : 0 < s)
    (hl : s ∈ lonelySet (C ∪ F)) : (u ≤ b → u ≤ s) ∧ (b < u → b < s) := by
  rw [lonelySet_union] at hl
  obtain ⟨x, -, y, -, hc, hT, hS⟩ := cell_of_lonely hCpos hne hs hl.1
  rcases cells_ordered hcell hc with ⟨h1, h2⟩ | hlt | hlt
  · have hus : u ≤ s := hu.2 ⟨h1 ▸ hT, hl.2⟩
    exact ⟨fun _ => hus, fun hbu => lt_of_lt_of_le hbu hus⟩
  · exact ⟨fun hub => le_trans hub (by linarith), fun _ => by linarith⟩
  · exact absurd ⟨s, ⟨hT, hS⟩, hl.2⟩ (hpre _ _ hc (lt_of_le_of_lt hc.2.1 hlt))

#print axioms prefix_landing_bound

/-- **The recursion step** [L] [PROVISIONAL: covering] (claim named: the next-cell landing recursion): for a cell
`[a, b]` of `C` whose prefix is covered, and `u` the first `F`-clear point from `a`: if `u ≤ b` the landing of `C ∪ F`
is `u`; if `b < u` every positive lonely point of `C ∪ F` is `> b`.  (Generalises `landing_union_eq_u` and
`landing_union_gt_wC`, which are the case of the first cell, where the prefix is empty.) -/
theorem landing_recursion (hCpos : ∀ d ∈ C, 0 < d) (hne : C.Nonempty) {a b u : ℝ} (hcell : IsCell C a b)
    (hpre : PrefixCovered C F a) (hu : IsClearFirst F a u) :
    (u ≤ b → IsLanding (C ∪ F) u) ∧ (b < u → ∀ s, 0 < s → s ∈ lonelySet (C ∪ F) → b < s) := by
  refine ⟨fun hub => ?_, fun hbu s hs hl => (prefix_landing_bound hCpos hne hcell hpre hu hs hl).2 hbu⟩
  have hu0 : 0 < u := lt_of_lt_of_le hcell.1 hu.1.1
  refine ⟨⟨hu0, ?_⟩, fun s hs => (prefix_landing_bound hCpos hne hcell hpre hu hs.1 hs.2).1 hub⟩
  rw [lonelySet_union]
  exact ⟨hcell.2.2.1 ⟨hu.1.1, hub⟩, hu.1.2⟩

#print axioms landing_recursion

/-- **The next cell is covered, so the prefix extends** [L] [PROVISIONAL: covering] (claim named: the next-cell
landing recursion): if the prefix before `[a, b]` is covered and `b < u` (the zones of `F` cover `[a, b]`), then the
prefix before the NEXT cell `[a2, b2]` of `C` (the cell of least left end `> b`) is covered. -/
theorem prefixCovered_next {a b u a2 b2 : ℝ} (hcell : IsCell C a b) (hpre : PrefixCovered C F a)
    (hu : IsClearFirst F a u) (hbu : b < u) (hc2 : IsCell C a2 b2) (hba2 : b < a2)
    (hmin : ∀ a' b' : ℝ, IsCell C a' b' → b < a' → a2 ≤ a') : PrefixCovered C F a2 := by
  intro a' b' hc' hlt
  rcases cells_ordered hcell hc' with ⟨h1, h2⟩ | hlt' | hlt'
  · rintro ⟨s, hs, hl⟩
    have hsF : s ∈ Set.Icc a b := by rw [h1, h2]; exact hs
    exact (typeX_iff hu).mp hbu ⟨s, hsF, hl⟩
  · exact absurd (hmin a' b' hc' hlt') (not_le.mpr hlt)
  · exact hpre a' b' hc' (lt_of_le_of_lt hc'.2.1 hlt')

#print axioms prefixCovered_next

/-- **Where the landing is: the first cell of `C` that the zones of `F` do not cover** [L] [PROVISIONAL: covering]
(claim named: the next-cell landing recursion).  `t` is the landing of `C ∪ F` iff there is a cell `[a, b]` of `C`
such that every earlier cell of `C` has no `F`-lonely point, `u` is the first `F`-clear point from `a` (so
`u = max(a, first F-clear point of the cell)`), `u ≤ b`, and `t = u`.  Conditional on the landing or the cell
existing; no existence is asserted. -/
theorem landing_iff_first_open_cell (hCpos : ∀ d ∈ C, 0 < d) (hne : C.Nonempty) {t : ℝ} :
    IsLanding (C ∪ F) t ↔
      ∃ a b u, IsCell C a b ∧ PrefixCovered C F a ∧ IsClearFirst F a u ∧ u ≤ b ∧ t = u := by
  constructor
  · intro ht
    have hl := ht.1.2
    rw [lonelySet_union] at hl
    obtain ⟨x, -, y, -, hc, hT, hS⟩ := cell_of_lonely hCpos hne ht.1.1 hl.1
    obtain ⟨u, hu⟩ := exists_clearFirst F _ ⟨t, hT, hl.2⟩
    have hut : u ≤ t := hu.2 ⟨hT, hl.2⟩
    have hpre : PrefixCovered C F (Localisation.lastOpening x t) := by
      intro a' b' hc' hlt ⟨s, hs, hlF⟩
      have hs0 : 0 < s := lt_of_lt_of_le hc'.1 hs.1
      have hlon : s ∈ lonelySet (C ∪ F) := by
        rw [lonelySet_union]; exact ⟨hc'.2.2.1 hs, hlF⟩
      have hts : t ≤ s := ht.2 ⟨hs0, hlon⟩
      rcases cells_ordered hc' hc with ⟨h1, -⟩ | hlt' | hlt'
      · exact absurd h1 (ne_of_lt hlt)
      · linarith [hs.2]
      · linarith
    have hub : u ≤ nextEntry y t := le_trans hut hS
    have hu0 : 0 < u := lt_of_lt_of_le hc.1 hu.1.1
    have htu : t ≤ u := by
      refine ht.2 ⟨hu0, ?_⟩
      rw [lonelySet_union]
      exact ⟨hc.2.2.1 ⟨hu.1.1, hub⟩, hu.1.2⟩
    exact ⟨_, _, u, hc, hpre, hu, hub, le_antisymm htu hut⟩
  · rintro ⟨a, b, u, hc, hpre, hu, hub, rfl⟩
    exact (landing_recursion hCpos hne hc hpre hu).1 hub

#print axioms landing_iff_first_open_cell

/-- **The landing past the first cell** [L] [PROVISIONAL: covering] (claim named: the next-cell landing recursion):
if `[tC, wC]` is the first cell of `C` (landing `tC`), `wC < u` for `u` the first `F`-clear point from `tC`, and `t` is
the landing of `C ∪ F`, then `t` lies in a LATER cell `[a, b]` of `C` (`wC < a`), every cell of `C` starting before `a`
(in particular `[tC, wC]`) is covered by the zones of `F`, and `t` is the first `F`-clear point `u'` from `a`, with
`u' ≤ b`. -/
theorem landing_past_cell (hCpos : ∀ d ∈ C, 0 < d) (hne : C.Nonempty) {tC wC u t : ℝ} (hC : IsLanding C tC)
    (hcell : IsCell C tC wC) (hu : IsClearFirst F tC u) (hwu : wC < u) (ht : IsLanding (C ∪ F) t) :
    ∃ a b u', IsCell C a b ∧ wC < a ∧ PrefixCovered C F a ∧ IsClearFirst F a u' ∧ u' ≤ b ∧ t = u' := by
  obtain ⟨a, b, u', hc, hpre, hu', hub, htu⟩ := (landing_iff_first_open_cell hCpos hne).mp ht
  obtain ⟨w0, hc0, hfirst⟩ := (first_cell_iff hCpos hne).mp hC
  have hw0 : w0 = wC := (cell_unique hc0 hcell ⟨le_rfl, hc0.2.1⟩ ⟨le_rfl, hcell.2.1⟩).2
  refine ⟨a, b, u', hc, ?_, hpre, hu', hub, htu⟩
  rcases cells_ordered hcell hc with ⟨h1, h2⟩ | hlt | hlt
  · exfalso
    have : u' = u := by
      rw [← h1] at hu'
      exact hu'.unique hu
    rw [this] at hub
    linarith [h2]
  · exact hlt
  · exfalso
    exact absurd (hfirst a b hc) (not_le.mpr (by linarith [hc.2.1]))

#print axioms landing_past_cell

/-- **Past the cell, the landing is the least point at or after `w_C` lonely for `C` and for `F`** [L]
(restated through the cell recursion's output): if `w_C < u` and `t` is the landing of `C ∪ F`, then `t > w_C`
and `t` is the least `s ≥ w_C` lonely for both. -/
theorem landing_past_least {tC wC u t : ℝ} (hC : IsLanding C tC) (hcell : IsCell C tC wC)
    (hu : IsClearFirst F tC u) (hwu : wC < u) (ht : IsLanding (C ∪ F) t) :
    wC < t ∧ IsLeast {s : ℝ | wC ≤ s ∧ s ∈ lonelySet C ∧ s ∈ lonelySet F} t := by
  have hgt : wC < t := landing_union_gt_wC hC hu hwu ht.1.1 ht.1.2
  have hl := ht.1.2
  rw [lonelySet_union] at hl
  refine ⟨hgt, ⟨hgt.le, hl.1, hl.2⟩, fun s hs => ?_⟩
  have hs0 : 0 < s := lt_of_lt_of_le (lt_of_lt_of_le hC.1.1 hcell.2.1) hs.1
  refine ht.2 ⟨hs0, ?_⟩
  rw [lonelySet_union]
  exact ⟨hs.2.1, hs.2.2⟩

#print axioms landing_past_least

end Recursion

/-! ## Instances: the recorded cases exhibit their next cell -/

/-- **`C = {1, 7}`, `F = {8}`** [L]: the first cell of `C` is the point `[1/8, 1/8]`, `u = 9/64 > 1/8`, and the landing
`9/56` of `{1, 7, 8}` lies in a later cell `[a, b]` of `C` with `1/8 < a ≤ 9/56 ≤ b`; every earlier cell of `C` is covered
by the zones of `8`; and `9/56` is the first `8`-clear point from `a`. -/
theorem touch_next_cell : ∃ a b : ℝ, IsCell ({1, 7} : Finset ℝ) a b ∧ (1 / 8 : ℝ) < a ∧ a ≤ 9 / 56 ∧ 9 / 56 ≤ b ∧
    PrefixCovered ({1, 7} : Finset ℝ) {8} a ∧ IsClearFirst ({8} : Finset ℝ) a (9 / 56) := by
  obtain ⟨hcell, hC, hu, -, hL, -⟩ := touch_block_example
  have hpos : ∀ d ∈ ({1, 7} : Finset ℝ), 0 < d := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl <;> norm_num
  obtain ⟨a, b, u', hc, hwa, hpre, hu', hub, htu⟩ :=
    landing_past_cell hpos ⟨1, by simp⟩ hC hcell hu (by norm_num) hL
  subst htu
  exact ⟨a, b, hc, hwa, hu'.1.1, hub, hpre, hu'⟩

#print axioms touch_next_cell

/-- **`C = {2, 12}`, `F = {15}`** [L]: same shape; the landing `3/32` of `{2, 12, 15}` lies in a later cell of `C`. -/
theorem narrow_next_cell : ∃ a b : ℝ, IsCell ({2, 12} : Finset ℝ) a b ∧ (7 / 96 : ℝ) < a ∧ a ≤ 3 / 32 ∧ 3 / 32 ≤ b ∧
    PrefixCovered ({2, 12} : Finset ℝ) {15} a ∧ IsClearFirst ({15} : Finset ℝ) a (3 / 32) := by
  obtain ⟨hcell, hC, hu, hlt, -, -, hL⟩ := narrow_cell_example
  have hpos : ∀ d ∈ ({2, 12} : Finset ℝ), 0 < d := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl <;> norm_num
  obtain ⟨a, b, u', hc, hwa, hpre, hu', hub, htu⟩ :=
    landing_past_cell hpos ⟨2, by simp⟩ hC hcell hu hlt hL
  subst htu
  exact ⟨a, b, hc, hwa, hu'.1.1, hub, hpre, hu'⟩

#print axioms narrow_next_cell

end Fresh.BlockLanding2
