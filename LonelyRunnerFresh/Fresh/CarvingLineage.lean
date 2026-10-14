import Mathlib
import Fresh.Framework
import Fresh.LonelyCells
import Fresh.Carving

/-!
# The lineage of a cell under carving (task AJ; the owner's "tagged covering" route)

Written 2026-10-09.  Imports `Mathlib`, `Fresh.Framework`, `Fresh.LonelyCells`, `Fresh.Carving`.  Exact reals; every
disparity positive; every statement symbolic for every finite `ds`.

What the data (`experiments/n8/carving_lineage_v1.py`, `.out`) showed, and what is proved here.

* **(A) `cell_in_window`** [L]: a cell of `ds` lies inside one window of each runner of `ds`.
* **(B) `cell_insert_unilateral`** [L]: if the inserted runner `d` is at most every disparity of `ds` (fastest-first
  insertion: each new runner is the slowest so far), no cell of `insert d ds` is clipped at BOTH ends: it keeps the
  left end or the right end of its parent.  Why: a cell clipped at both ends contains a whole window of `d`, of length
  `3/(4d)`, while the parent lies in a window of any `e ∈ ds`, of length `3/(4e) ≤ 3/(4d)`.  In the data this is the
  count "0 ancestors clipped at both ends" for fastest-first, against up to 4 on the landing chain for slowest-first.
* **(C) `isCell_iff_transversal`** [L]: the cells of `ds` are exactly the nonempty intervals
  `[max_e (N e + 1/8)/e, min_e (N e + 7/8)/e]` (with positive left end) for a choice `N` of one window index per runner:
  a cell is the intersection of ONE window of each runner.  Hence the lineage of a cell in ANY insertion order is the
  prefix of its window vector (`ancestor_isCell`), a clip at an insertion is a strict new maximum opening (minimum entry).
* **(D) `ends_le_iff_pairwise`, `exists_lonely_iff_transversal`, `zones_cover_iff_all_transversals_blocked`**
  [L] with the step tagged `[PROVISIONAL: covering]`: a window vector has a common point iff its windows meet pairwise
  (one-dimensional Helly, proved directly); a lonely instant exists iff some vector is pairwise compatible; the zones
  cover `(0, ∞)` iff every vector has a blocked pair.

Provenance.  The carving theorems used are `Carving.isCell_insert_iff`/`cell_insert_is_piece` and
`LonelyCells.cell_left_end_is_opening`/`cell_right_end_is_entry`/`cell_of_lonely`.  No declaration in the existing
`LonelyRunner/LRC/` tree was copied; the proofs below were written for this file.
-/

open Classical

namespace Fresh.CarvingLineage

open Fresh Fresh.LonelyCells Fresh.Carving

/-! ## (A) A cell lies in one window of each runner -/

/-- **(A) `cell_in_window`** [L]: for a cell `[u, w]` of `ds` and `e ∈ ds` there is a lap `N` with
`[u, w] ⊆ [(N + 1/8)/e, (N + 7/8)/e]`.  (The cell is lonely, hence clear for `e`, so `u` is in some window; if `w` were
past that window's entry, the instants just after the entry would be in the way.) -/
theorem cell_in_window {ds : Finset ℝ} (hpos : ∀ e ∈ ds, 0 < e) {u w e : ℝ} (h : IsCell ds u w) (he : e ∈ ds) :
    ∃ N : ℤ, winLo e N ≤ u ∧ w ≤ winHi e N := by
  have he0 := hpos e he
  have hu : u ∈ lonelySet ds := h.2.2.1 ⟨le_rfl, h.2.1⟩
  have hc : u ∈ clearSet e := by
    rw [lonelySet_eq_iInter] at hu
    exact Set.mem_iInter₂.mp hu e he
  rw [clearSet_eq_iUnion he0] at hc
  obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hc
  refine ⟨N, hN.1, ?_⟩
  by_contra hw
  push Not at hw
  have hq : 0 < 1 / (8 * e) := by positivity
  have hq' : 1 / (8 * e) < 1 / (4 * e) := by
    apply one_div_lt_one_div_of_lt (by positivity); linarith
  set s := min w (winHi e N + 1 / (8 * e)) with hs
  have hs1 : winHi e N < s := lt_min hw (by linarith)
  have hs2 : s < winHi e N + 1 / (4 * e) := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hmem : s ∈ Set.Icc u w := ⟨le_trans hN.2 hs1.le, min_le_left _ _⟩
  exact not_lonely_of_inWay he (inWay_after_entry he0 (mul_winHi he0 N) hs1 hs2) (h.2.2.1 hmem)

#print axioms cell_in_window

/-! ## (B) Fastest-first insertion never clips a cell at both ends -/

/-- **(B) `cell_insert_unilateral`** [L]: let `d > 0` be at most every element of the nonempty `ds`.  Every cell
`[u', w']` of `insert d ds` is the piece `[max u lo_N, min w hi_N]` of a cell `[u, w]` of `ds` and keeps its parent's left
end or its parent's right end.  (A parent clipped at both ends would contain the whole window of lap `N`, of length
`3/(4d)`, but it lies in a window of any `e ∈ ds` of length `3/(4e) ≤ 3/(4d)`.)  This is the fastest-first order. -/
theorem cell_insert_unilateral {ds : Finset ℝ} (hpos : ∀ e ∈ ds, 0 < e) (hne : ds.Nonempty) {d u' w' : ℝ}
    (hd : 0 < d) (hle : ∀ e ∈ ds, d ≤ e) (h : IsCell (insert d ds) u' w') :
    ∃ u w : ℝ, ∃ N : ℤ, IsCell ds u w ∧ u' = max u (winLo d N) ∧ w' = min w (winHi d N) ∧ (u' = u ∨ w' = w) := by
  obtain ⟨u, w, N, hc, h1, h2⟩ := cell_insert_is_piece hpos hne hd h
  refine ⟨u, w, N, hc, h1, h2, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hu, hw⟩ := hcon
  have hl : u < winLo d N := by
    have : u < max u (winLo d N) := lt_of_le_of_ne (le_max_left _ _) (fun e => hu (h1.trans e.symm))
    rcases lt_max_iff.mp this with h' | h'
    · exact absurd h' (lt_irrefl _)
    · exact h'
  have hr : winHi d N < w := by
    have : min w (winHi d N) < w := lt_of_le_of_ne (min_le_left _ _) (fun e => hw (h2.trans e))
    rcases min_lt_iff.mp this with h' | h'
    · exact absurd h' (lt_irrefl _)
    · exact h'
  obtain ⟨e, he⟩ := hne
  obtain ⟨M, hM1, hM2⟩ := cell_in_window hpos hc he
  have he0 := hpos e he
  have l1 := window_length hd N
  have l2 := window_length he0 M
  have l3 : 3 / (4 * e) ≤ 3 / (4 * d) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith [hle e he])
  linarith

#print axioms cell_insert_unilateral

/-! ## (C) A cell is the intersection of one window of each runner -/

/-- **(C) `Icc_transversal_subset_lonely`** [L]: for any choice `N` of a lap per runner, every instant between the largest
opening and the smallest entry is lonely. -/
theorem Icc_transversal_subset_lonely {ds : Finset ℝ} (hpos : ∀ e ∈ ds, 0 < e) (hne : ds.Nonempty) (N : ℝ → ℤ) :
    Set.Icc (ds.sup' hne (fun e => winLo e (N e))) (ds.inf' hne (fun e => winHi e (N e))) ⊆ lonelySet ds := by
  intro s hs
  rw [lonelySet_eq_iInter]
  refine Set.mem_iInter₂.mpr fun e he => ?_
  rw [clearSet_eq_iUnion (hpos e he)]
  exact Set.mem_iUnion.mpr ⟨N e, le_trans (Finset.le_sup' (fun e => winLo e (N e)) he) hs.1,
    le_trans hs.2 (Finset.inf'_le (fun e => winHi e (N e)) he)⟩

#print axioms Icc_transversal_subset_lonely

/-- **(C) `isCell_iff_transversal`** [L]: `[u, w]` is a cell of `ds` iff for some choice `N` of one lap per runner,
`0 < u`, `u` is the largest opening `(N e + 1/8)/e`, `w` the smallest entry `(N e + 7/8)/e`, and `u ≤ w`.  The cells
of a set of runners are exactly the nonempty intersections of one window of each. -/
theorem isCell_iff_transversal {ds : Finset ℝ} (hpos : ∀ e ∈ ds, 0 < e) (hne : ds.Nonempty) {u w : ℝ} :
    IsCell ds u w ↔ ∃ N : ℝ → ℤ, 0 < u ∧ u = ds.sup' hne (fun e => winLo e (N e)) ∧
      w = ds.inf' hne (fun e => winHi e (N e)) ∧ u ≤ w := by
  constructor
  · intro h
    -- one lap per runner, chosen by `cell_in_window`
    let N : ℝ → ℤ := fun e =>
      if hh : e ∈ ds then Classical.choose (cell_in_window hpos h hh) else 0
    have hN : ∀ e ∈ ds, winLo e (N e) ≤ u ∧ w ≤ winHi e (N e) := by
      intro e he
      have := Classical.choose_spec (cell_in_window hpos h he)
      simpa only [N, dif_pos he] using this
    refine ⟨N, h.1, ?_, ?_, h.2.1⟩
    · apply le_antisymm
      · obtain ⟨x, hx, k, hu, -⟩ := cell_left_end_is_opening hpos h
        have hx0 := hpos x hx
        have huk : u = winLo x (k : ℤ) := by rw [hu]; unfold winLo; push_cast; rfl
        obtain ⟨hA, hB⟩ := hN x hx
        have e1 : (N x : ℝ) + 1 / 8 ≤ (k : ℝ) + 1 / 8 := by
          have := mul_le_mul_of_nonneg_left (huk ▸ hA : winLo x (N x) ≤ winLo x (k : ℤ)) hx0.le
          rw [mul_winLo hx0, mul_winLo hx0] at this; exact_mod_cast this
        have e2 : (k : ℝ) + 1 / 8 ≤ (N x : ℝ) + 7 / 8 := by
          have h3 : winLo x (k : ℤ) ≤ winHi x (N x) := by rw [← huk]; exact le_trans h.2.1 hB
          have := mul_le_mul_of_nonneg_left h3 hx0.le
          rw [mul_winLo hx0, mul_winHi hx0] at this; exact_mod_cast this
        have hk1 : N x ≤ (k : ℤ) := by exact_mod_cast (by linarith : (N x : ℝ) ≤ k)
        have hk2 : (k : ℤ) ≤ N x := by
          by_contra hc
          push Not at hc
          have : (N x : ℝ) + 1 ≤ k := by exact_mod_cast hc
          linarith
        have hkk : (k : ℤ) = N x := le_antisymm hk2 hk1
        rw [huk, hkk]
        exact Finset.le_sup' (fun e => winLo e (N e)) hx
      · exact Finset.sup'_le hne _ (fun e he => (hN e he).1)
    · apply le_antisymm
      · exact Finset.le_inf' hne _ (fun e he => (hN e he).2)
      · obtain ⟨y, hy, k, hw, -⟩ := cell_right_end_is_entry hpos h
        have hy0 := hpos y hy
        have hwk : w = winHi y (k : ℤ) := by rw [hw]; unfold winHi; push_cast; rfl
        obtain ⟨hA, hB⟩ := hN y hy
        have e1 : (k : ℝ) + 7 / 8 ≤ (N y : ℝ) + 7 / 8 := by
          have := mul_le_mul_of_nonneg_left (hwk ▸ hB : winHi y (k : ℤ) ≤ winHi y (N y)) hy0.le
          rw [mul_winHi hy0, mul_winHi hy0] at this; exact_mod_cast this
        have e2 : (N y : ℝ) + 1 / 8 ≤ (k : ℝ) + 7 / 8 := by
          have h3 : winLo y (N y) ≤ winHi y (k : ℤ) := by rw [← hwk]; exact le_trans hA h.2.1
          have := mul_le_mul_of_nonneg_left h3 hy0.le
          rw [mul_winLo hy0, mul_winHi hy0] at this; exact_mod_cast this
        have hk1 : (k : ℤ) ≤ N y := by exact_mod_cast (by linarith : (k : ℝ) ≤ N y)
        have hk2 : N y ≤ (k : ℤ) := by
          by_contra hc
          push Not at hc
          have : (k : ℝ) + 1 ≤ N y := by exact_mod_cast hc
          linarith
        have hkk : (k : ℤ) = N y := le_antisymm hk1 hk2
        rw [hwk, hkk]
        exact Finset.inf'_le (fun e => winHi e (N e)) hy
  · rintro ⟨N, hu0, hu, hw, huw⟩
    have hsub := Icc_transversal_subset_lonely hpos hne N
    rw [← hu, ← hw] at hsub
    refine ⟨hu0, huw, hsub, ?_, ?_⟩
    · -- left maximality: the runner attaining the largest opening is in the way just before it
      intro u'' hu'' hs''
      obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup' hne (fun e => winLo e (N e))
      have hx0 := hpos x hx
      have hux : u = winLo x (N x) := hu.trans hxe
      have hq : 0 < 1 / (8 * x) := by positivity
      have hq' : 1 / (8 * x) < 1 / (4 * x) := by
        apply one_div_lt_one_div_of_lt (by positivity); linarith
      set s := max u'' (u - 1 / (8 * x)) with hs
      have hs1 : u - 1 / (4 * x) < s := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      have hs2 : s < u := max_lt hu'' (by linarith)
      have hin : InWay x s := inWay_before_opening hx0 (by rw [hux]; exact mul_winLo hx0 (N x)) hs1 hs2
      exact not_lonely_of_inWay hx hin (hs'' ⟨le_max_left _ _, le_trans hs2.le huw⟩)
    · intro w'' hw'' hs''
      obtain ⟨y, hy, hye⟩ := Finset.exists_mem_eq_inf' hne (fun e => winHi e (N e))
      have hy0 := hpos y hy
      have hwy : w = winHi y (N y) := hw.trans hye
      have hq : 0 < 1 / (8 * y) := by positivity
      have hq' : 1 / (8 * y) < 1 / (4 * y) := by
        apply one_div_lt_one_div_of_lt (by positivity); linarith
      set s := min w'' (w + 1 / (8 * y)) with hs
      have hs1 : w < s := lt_min hw'' (by linarith)
      have hs2 : s < w + 1 / (4 * y) := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hin : InWay y s := inWay_after_entry hy0 (by rw [hwy]; exact mul_winHi hy0 (N y)) hs1 hs2
      exact not_lonely_of_inWay hy hin (hs'' ⟨le_trans huw hs1.le, min_le_left _ _⟩)

#print axioms isCell_iff_transversal

/-- **(C) `ancestor_isCell`** [L]: the lineage of a cell in ANY insertion order is the prefix of its window vector.
If `[u, w]` is a cell of `ds` with window vector `N` and `ds₀ ⊆ ds` is nonempty, then the same expressions over `ds₀`,
`[max_{e ∈ ds₀} opening, min_{e ∈ ds₀} entry]`, form a cell of `ds₀` that contains `[u, w]`. -/
theorem ancestor_isCell {ds ds₀ : Finset ℝ} (hpos : ∀ e ∈ ds, 0 < e) (hne : ds.Nonempty) (hsub : ds₀ ⊆ ds)
    (hne₀ : ds₀.Nonempty) {u w : ℝ} (h : IsCell ds u w) :
    ∃ N : ℝ → ℤ, u = ds.sup' hne (fun e => winLo e (N e)) ∧ w = ds.inf' hne (fun e => winHi e (N e)) ∧
      IsCell ds₀ (ds₀.sup' hne₀ (fun e => winLo e (N e))) (ds₀.inf' hne₀ (fun e => winHi e (N e))) ∧
      ds₀.sup' hne₀ (fun e => winLo e (N e)) ≤ u ∧ w ≤ ds₀.inf' hne₀ (fun e => winHi e (N e)) := by
  obtain ⟨N, hu0, hu, hw, huw⟩ := (isCell_iff_transversal hpos hne).mp h
  have hpos₀ : ∀ e ∈ ds₀, 0 < e := fun e he => hpos e (hsub he)
  have hle1 : ds₀.sup' hne₀ (fun e => winLo e (N e)) ≤ u := by
    rw [hu]
    exact Finset.sup'_le hne₀ _ (fun e he => Finset.le_sup' (fun e => winLo e (N e)) (hsub he))
  have hle2 : w ≤ ds₀.inf' hne₀ (fun e => winHi e (N e)) := by
    rw [hw]
    exact Finset.le_inf' hne₀ _ (fun e he => Finset.inf'_le (fun e => winHi e (N e)) (hsub he))
  have hpos_lo : 0 < ds₀.sup' hne₀ (fun e => winLo e (N e)) := by
    obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup' hne₀ (fun e => winLo e (N e))
    rw [hxe]
    -- the lap of `x` is nonnegative because the cell, which lies in that window, is at a positive instant
    obtain ⟨hA, hB⟩ : winLo x (N x) ≤ u ∧ w ≤ winHi x (N x) := by
      have hxs := hsub hx
      have hh := (Finset.le_sup' (fun e => winLo e (N e)) hxs)
      have hh2 := (Finset.inf'_le (fun e => winHi e (N e)) hxs)
      exact ⟨hh.trans hu.ge, hw.le.trans hh2⟩
    have hx0 := hpos x (hsub hx)
    have h1 : 0 < winHi x (N x) := lt_of_lt_of_le hu0 (le_trans huw hB)
    have h2 : (0 : ℝ) < (N x : ℝ) + 7 / 8 := by
      have := mul_pos hx0 h1
      rw [mul_winHi hx0] at this; exact this
    have h3 : (0 : ℤ) ≤ N x := by
      by_contra hc
      push Not at hc
      have : (N x : ℝ) + 1 ≤ 0 := by exact_mod_cast (by omega : N x + 1 ≤ 0)
      linarith
    unfold winLo
    have : (0 : ℝ) ≤ (N x : ℝ) := by exact_mod_cast h3
    positivity
  refine ⟨N, hu, hw, ?_, hle1, hle2⟩
  exact (isCell_iff_transversal hpos₀ hne₀).mpr ⟨N, hpos_lo, rfl, rfl, le_trans hle1 (le_trans huw hle2)⟩

#print axioms ancestor_isCell

/-! ## (D) The pairwise form, and the complement (covering) form -/

/-- **(D) `ends_le_iff_pairwise`** [L]: for a choice `N` of laps, the largest opening is at most the smallest entry iff
every two chosen windows meet, i.e. each opening is at most each entry (one-dimensional Helly for closed intervals). -/
theorem ends_le_iff_pairwise {ds : Finset ℝ} (hne : ds.Nonempty) (N : ℝ → ℤ) :
    ds.sup' hne (fun e => winLo e (N e)) ≤ ds.inf' hne (fun e => winHi e (N e)) ↔
      ∀ e ∈ ds, ∀ e' ∈ ds, winLo e (N e) ≤ winHi e' (N e') := by
  rw [Finset.sup'_le_iff]
  constructor
  · intro h e he e' he'
    exact le_trans (h e he) (Finset.inf'_le (fun e => winHi e (N e)) he')
  · intro h e he
    exact Finset.le_inf' hne _ (fun e' he' => h e he e' he')

#print axioms ends_le_iff_pairwise

/-- **(D) `exists_lonely_iff_transversal`** [L] [PROVISIONAL: covering]: a positive lonely instant exists iff some choice
of one lap per runner has a positive largest opening and pairwise-meeting windows.  The covering step (a transversal of
pairwise-meeting windows, equivalently "the zones do not cover") supports the claim "the isolation exists iff the zones
of the runners do not cover `(0, ∞)`"; it is a reformulation, not an existence result. -/
theorem exists_lonely_iff_transversal {ds : Finset ℝ} (hpos : ∀ e ∈ ds, 0 < e) (hne : ds.Nonempty) :
    (∃ t : ℝ, 0 < t ∧ t ∈ lonelySet ds) ↔
      ∃ N : ℝ → ℤ, 0 < ds.sup' hne (fun e => winLo e (N e)) ∧ ∀ e ∈ ds, ∀ e' ∈ ds, winLo e (N e) ≤ winHi e' (N e') := by
  constructor
  · rintro ⟨t, ht, hl⟩
    obtain ⟨x, -, y, -, hc, -, -⟩ := cell_of_lonely hpos hne ht hl
    obtain ⟨N, hu0, hu, hw, huw⟩ := (isCell_iff_transversal hpos hne).mp hc
    refine ⟨N, hu ▸ hu0, (ends_le_iff_pairwise hne N).mp ?_⟩
    rw [← hu, ← hw]; exact huw
  · rintro ⟨N, h0, hp⟩
    have hle := (ends_le_iff_pairwise hne N).mpr hp
    exact ⟨_, h0, Icc_transversal_subset_lonely hpos hne N ⟨le_rfl, hle⟩⟩

#print axioms exists_lonely_iff_transversal

/-- **(D) `no_lonely_iff_in_some_zone`** [L]: an instant is not lonely iff it lies in an open zone of some runner. -/
theorem not_lonely_iff_in_some_zone {ds : Finset ℝ} (hpos : ∀ e ∈ ds, 0 < e) {t : ℝ} :
    t ∉ lonelySet ds ↔ ∃ e ∈ ds, ∃ N : ℤ, t ∈ zone e N := by
  rw [lonelySet_eq_iInter]
  simp only [Set.mem_iInter, not_forall]
  constructor
  · rintro ⟨e, he, hn⟩
    exact ⟨e, he, (notMem_clearSet_iff (hpos e he)).mp hn⟩
  · rintro ⟨e, he, hz⟩
    exact ⟨e, he, (notMem_clearSet_iff (hpos e he)).mpr hz⟩

#print axioms not_lonely_iff_in_some_zone

/-- **(D) `zones_cover_iff_all_transversals_blocked`** [L] [PROVISIONAL: covering]: the zones of the runners cover
`(0, ∞)` iff every choice of one lap per runner either has a non-positive largest opening or contains two windows that
do not meet.  This is the complement statement of the owner's tagged-covering route, as an equivalence only: it asserts
neither side.  It supports the claim "the isolation exists iff the zones of the runners do not cover `(0, ∞)`". -/
theorem zones_cover_iff_all_transversals_blocked {ds : Finset ℝ} (hpos : ∀ e ∈ ds, 0 < e) (hne : ds.Nonempty) :
    (∀ t : ℝ, 0 < t → ∃ e ∈ ds, ∃ N : ℤ, t ∈ zone e N) ↔
      ∀ N : ℝ → ℤ, ds.sup' hne (fun e => winLo e (N e)) ≤ 0 ∨
        ∃ e ∈ ds, ∃ e' ∈ ds, winHi e' (N e') < winLo e (N e) := by
  have h1 : (∀ t : ℝ, 0 < t → ∃ e ∈ ds, ∃ N : ℤ, t ∈ zone e N) ↔ ¬ ∃ t : ℝ, 0 < t ∧ t ∈ lonelySet ds := by
    constructor
    · rintro h ⟨t, ht, hl⟩
      exact ((not_lonely_iff_in_some_zone hpos).mpr (h t ht)) hl
    · intro h t ht
      by_contra hc
      exact h ⟨t, ht, by_contra fun hn => hc ((not_lonely_iff_in_some_zone hpos).mp hn)⟩
  rw [h1, exists_lonely_iff_transversal hpos hne]
  push Not
  refine forall_congr' fun N => ?_
  constructor
  · intro h
    by_cases h0 : 0 < ds.sup' hne (fun e => winLo e (N e))
    · exact Or.inr (h h0)
    · exact Or.inl (not_lt.mp h0)
  · rintro (h | h) h0
    · exact absurd h (not_le.mpr h0)
    · exact h

#print axioms zones_cover_iff_all_transversals_blocked

end Fresh.CarvingLineage
