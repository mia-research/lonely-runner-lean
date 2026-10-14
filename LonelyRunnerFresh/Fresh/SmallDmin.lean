import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Dilation
import Fresh.Gate
import Fresh.Types
import Fresh.StrongGateStudy

/-!
# Small `d_min`: the crossing cells, exactly (Task Z1)

Written 2026-10-08.  Imports `Mathlib` and the Fresh modules `Framework`, `Cascade`, `Dilation`, `Gate`, `Types`,
`StrongGateStudy`; nothing from the existing `LonelyRunner` repo.  Exact reals only; every disparity is positive.

Question.  Integer disparity sets with `d_min = m ∈ {3, 4, 5}` have no cascade state above `R = 7` (a *crosser*:
`R = 8·m·t`, `t = 7/(8m)`) in exhaustive exact data (`a₇ ≤ 100`), while `d_min = 6, 7, 8, 9, …` have crossers.  This file
proves what is symbolic and says exactly what is not.  The exact data (own enumeration, the cell list with exact rational
vertices, the per-cell lattice facts) are in the Z1 scratch directory and are described in the task report, not here.

Results (each [L] has its `#print axioms` line below it in this file).
* (1) **The crossing cells, exactly.**  `crosser_iff_pattern` [L]: for every finite set `ds` of positive disparities with
  least element `m`, the cascade from `1/(8m)` exceeds `7/(8m)` iff `ds` admits a *setter-lap pattern*: a finite list of
  (runner `xₙ ∈ ds`, lap `kₙ`) whose open zones `((8k-1)/(8x), (8k+1)/(8x))` chain from the start to beyond `7/(8m)` (each
  zone contains the right end of the one before).  `crosser_iff_linear_pattern` [L] writes the chain without division:
  `(8k₀-1)·m < x₀ < (8k₀+1)·m`, `(8kₙ₊₁-1)·xₙ < (8kₙ+1)·xₙ₊₁ < (8kₙ₊₁+1)·xₙ`, `7·x_N < (8k_N+1)·m`: every pattern is an open
  polyhedral cell, linear in the disparities, and the crossers are exactly the union of the cells.  The forward direction
  is the cascade's own record (setter and lap of every move), the converse is the covering of `[1/(8m), 7/(8m)]` by the
  chain (`pattern_no_lonely`), through `Gate.exceeds_seven_iff`.
  `lonely_in_window_iff` / `crosser_iff_all_laps_fail` [L] give the complement: a lonely instant in the window exists iff
  some lap vector satisfies the pairwise closed conditions `(8kd+1)·e ≤ (8ke+7)·d` (1-dimensional Helly), so the
  non-crossers are the union of closed polyhedra indexed by lap vectors and the crossers are the readings that violate
  every one.  `patternLinear_iff_intPattern` [L]: for integer disparities each strict inequality holds with slack one
  (`IntPattern`), so "a crosser with `d_min = M` exists" is the feasibility of an integer program.
* (2) **Scale** `crosser_scale` [L]: crossing is invariant under `ds ↦ c·ds`, `m ↦ c·m` (R is scale free); only the
  denominator of the reading vector `ds/m` matters.
* (3) **Necessary conditions at single instants** [L]: `crosser_blocked`, `crosser_zone_at` (every `R = r ∈ [1, 7]` has a
  runner `d` with `(8j-1)m < r·d < (8j+1)m`, `j ≥ 1`), `crosser_first_zone` (`r = 1`: a disparity above `7m`),
  `crosser_last_zone` (`r = 7`: a disparity with `(8j-1)m < 7x < (8j+1)m`, for example reading in `(15/7, 17/7)`),
  `int_crosser_top` (integers: a disparity `≥ 7M + 1`), `int_crosser_near_multiple` (integers: for every `q` with
  `8M/7 ≤ q ≤ 8M` a disparity within `q/8` of a multiple of `q`; for `q ≤ 8` this is `StrongGateStudy.crosser_needs_multiple`).
* (4) **Lower bounds on the large readings** [L]: `crosser_index_ge_eight` (at least eight moves), `crosser_first_two_setters`,
  `crosser_two_large` (two distinct disparities above `49m/9`), `crosser_second_largest` (rank form, tagged counting tool),
  `int_crosser_two_large`.  With `crosser_first_zone` this is: largest reading `> 7`, second largest `> 49/9`.
* (5) **Certificates** [L]: `ex_crosser` (the set `{6,16,21,26,29,36,45}` has a 19-letter pattern, checked by `norm_num`, hence
  crosses `R = 7`); `lonely_m3`, `lonely_m4`, `lonely_m5` (the sets attaining the largest first-lonely `R*` in the data have
  an explicit lonely instant, `R = 17/3, 68/11, 125/19`).
* (6) **OWED, not proved**: `NoSmallIntegerCrosser` (the observation itself for `m ∈ {3,4,5}`), `ReadingsAboveFifteenSevenths`
  (every non-`d_min` reading of a crosser exceeds `15/7`).  Neither follows from anything here.

Provenance.  (1) corresponds in the existing tree to the chain of `LRC/Spec/FirstGateN.lean` and to the setter-lap words of
`docs/n8/MECHANISM_MAP`; both were read for the shape of the statement.  The proofs below were written for this file from
`Cascade.IsMove`, `Dilation.nextOpening_eq_lap`, `Gate.exceeds_seven_iff`, `Gate.staircase_setter`; nothing was copied.
(4) uses the staircase of `Gate.lean` (record L5) for the first two setters, which are distinct by
`Dilation.consecutive_setters_ne`.
-/

open Classical

namespace Fresh

namespace SmallDmin

open Cascade Dilation

/-! ## (1) Zones -/

/-- Left end (in `t`) of the zone of runner `d` on lap `k`: it is in the way strictly between the two ends. -/
noncomputable def zoneLo (d : ℝ) (k : ℤ) : ℝ := (8 * (k : ℝ) - 1) / (8 * d)

/-- Right end (in `t`) of the zone of runner `d` on lap `k`: the opening `(k + 1/8)/d`. -/
noncomputable def zoneHi (d : ℝ) (k : ℤ) : ℝ := (8 * (k : ℝ) + 1) / (8 * d)

/-- Strictly inside the zone `(zoneLo d k, zoneHi d k)` the runner is in the way. -/
theorem inWay_of_zone {d : ℝ} (hd : 0 < d) {k : ℤ} {s : ℝ} (h1 : zoneLo d k < s) (h2 : s < zoneHi d k) :
    InWay d s := by
  unfold zoneLo at h1
  unfold zoneHi at h2
  rw [div_lt_iff₀ (by positivity)] at h1
  rw [lt_div_iff₀ (by positivity)] at h2
  exact LonelyCells.inWay_of_near k (by rw [abs_lt]; constructor <;> nlinarith)

#print axioms inWay_of_zone

/-- A runner in the way at `s` is strictly inside its zone of lap `lap d s`, and its next opening is the right end. -/
theorem zone_of_inWay {d s : ℝ} (hd : 0 < d) (h : InWay d s) :
    zoneLo d (lap d s) < s ∧ s < zoneHi d (lap d s) ∧ nextOpening d s = zoneHi d (lap d s) := by
  have h1 := abs_lt.mp (abs_sub_lap_lt h)
  refine ⟨?_, ?_, ?_⟩
  · unfold zoneLo
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  · unfold zoneHi
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  · rw [nextOpening_eq_lap h]
    unfold zoneHi
    field_simp

#print axioms zone_of_inWay

/-! ## (2) The pattern cell -/

/-- A *setter-lap pattern* for `ds` with least element `m` (`N + 1` letters `(xₙ, kₙ)`): `xₙ ∈ ds`; the start `1/(8m)`
is strictly inside the first zone; the right end of each zone is strictly inside the next zone; the last zone ends beyond
`7/(8m)`.  In readings `ρ = x/m` the conditions are linear (see `PatternLinear`). -/
-- STANDING: DEFINITION
def PatternCell (ds : Finset ℝ) (m : ℝ) (N : ℕ) (x : ℕ → ℝ) (k : ℕ → ℤ) : Prop :=
  (∀ n, n ≤ N → x n ∈ ds) ∧
  zoneLo (x 0) (k 0) < 1 / (8 * m) ∧ 1 / (8 * m) < zoneHi (x 0) (k 0) ∧
  (∀ n, n < N → zoneLo (x (n + 1)) (k (n + 1)) < zoneHi (x n) (k n) ∧
    zoneHi (x n) (k n) < zoneHi (x (n + 1)) (k (n + 1))) ∧
  7 / (8 * m) < zoneHi (x N) (k N)

/-- The same cell without division: every condition is a linear inequality in the disparities (and `m`). -/
-- STANDING: DEFINITION
def PatternLinear (ds : Finset ℝ) (m : ℝ) (N : ℕ) (x : ℕ → ℝ) (k : ℕ → ℤ) : Prop :=
  (∀ n, n ≤ N → x n ∈ ds) ∧
  (8 * (k 0 : ℝ) - 1) * m < x 0 ∧ x 0 < (8 * (k 0 : ℝ) + 1) * m ∧
  (∀ n, n < N → (8 * (k (n + 1) : ℝ) - 1) * x n < (8 * (k n : ℝ) + 1) * x (n + 1) ∧
    (8 * (k n : ℝ) + 1) * x (n + 1) < (8 * (k (n + 1) : ℝ) + 1) * x n) ∧
  7 * x N < (8 * (k N : ℝ) + 1) * m

/-- The cell and its linear form are the same statement (all disparities and `m` positive). -/
theorem patternCell_iff_linear {ds : Finset ℝ} {m : ℝ} (hm : 0 < m) (hpos : ∀ d ∈ ds, 0 < d) {N : ℕ}
    {x : ℕ → ℝ} {k : ℕ → ℤ} : PatternCell ds m N x k ↔ PatternLinear ds m N x k := by
  have hx : ∀ n, n ≤ N → x n ∈ ds → 0 < x n := fun n _ h => hpos _ h
  constructor
  · rintro ⟨hmem, h0, h0', hstep, hend⟩
    have p0 := hpos _ (hmem 0 (Nat.zero_le _))
    refine ⟨hmem, ?_, ?_, ?_, ?_⟩
    · unfold zoneLo at h0
      rw [div_lt_div_iff₀ (by positivity) (by positivity)] at h0
      nlinarith
    · unfold zoneHi at h0'
      rw [div_lt_div_iff₀ (by positivity) (by positivity)] at h0'
      nlinarith
    · intro n hn
      have p1 := hpos _ (hmem n hn.le)
      have p2 := hpos _ (hmem (n + 1) hn)
      obtain ⟨a, b⟩ := hstep n hn
      simp only [zoneLo, zoneHi] at a b
      rw [div_lt_div_iff₀ (by positivity) (by positivity)] at a b
      constructor <;> nlinarith
    · have pN := hpos _ (hmem N le_rfl)
      unfold zoneHi at hend
      rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hend
      nlinarith
  · rintro ⟨hmem, h0, h0', hstep, hend⟩
    have p0 := hpos _ (hmem 0 (Nat.zero_le _))
    refine ⟨hmem, ?_, ?_, ?_, ?_⟩
    · unfold zoneLo
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    · unfold zoneHi
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    · intro n hn
      have p1 := hpos _ (hmem n hn.le)
      have p2 := hpos _ (hmem (n + 1) hn)
      obtain ⟨a, b⟩ := hstep n hn
      unfold zoneLo zoneHi
      constructor <;> rw [div_lt_div_iff₀ (by positivity) (by positivity)] <;> nlinarith
    · have pN := hpos _ (hmem N le_rfl)
      unfold zoneHi
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith

#print axioms patternCell_iff_linear

/-- **A pattern covers the window**: no instant of `[1/(8m), 7/(8m)]` is lonely. -/
theorem pattern_no_lonely {ds : Finset ℝ} {m : ℝ} (hpos : ∀ d ∈ ds, 0 < d) {N : ℕ} {x : ℕ → ℝ} {k : ℕ → ℤ}
    (hp : PatternCell ds m N x k) {s : ℝ} (hs1 : 1 / (8 * m) ≤ s) (hs7 : s ≤ 7 / (8 * m)) : ¬ LonelyAt ds s := by
  obtain ⟨hmem, h0, h0', hstep, hend⟩ := hp
  intro hl
  -- every right end is at most `s`
  have key : ∀ n, n ≤ N → zoneHi (x n) (k n) ≤ s := by
    intro n
    induction n with
    | zero =>
      intro _
      by_contra hc
      push Not at hc
      exact not_inWay_iff.mpr (hl _ (hmem 0 (Nat.zero_le _)))
        (inWay_of_zone (hpos _ (hmem 0 (Nat.zero_le _))) (lt_of_lt_of_le h0 hs1) hc)
    | succ n ih =>
      intro hn
      have hn' : n < N := hn
      have ihn := ih hn'.le
      obtain ⟨a, _⟩ := hstep n hn'
      by_contra hc
      push Not at hc
      exact not_inWay_iff.mpr (hl _ (hmem (n + 1) hn))
        (inWay_of_zone (hpos _ (hmem (n + 1) hn)) (lt_of_lt_of_le a ihn) hc)
  have := key N le_rfl
  linarith

#print axioms pattern_no_lonely

/-- **A crosser has a pattern**: the setters and laps of the cascade's own moves up to the first state above
`7/(8m)`. -/
theorem pattern_of_crosser {ds : Finset ℝ} {m : ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hm : IsLeast (ds : Set ℝ) m)
    (hcross : ∃ n, 7 / (8 * m) < cascadeSeq ds (1 / (8 * m)) n) :
    ∃ (N : ℕ) (x : ℕ → ℝ) (k : ℕ → ℤ), PatternCell ds m N x k := by
  set seq := cascadeSeq ds (1 / (8 * m)) with hseq
  have hmv : ∀ n, IsMove ds (seq n) (seq (n + 1)) := cascadeSeq_isMove ds (1 / (8 * m))
  have hno : ¬ ∃ t, 1 / (8 * m) ≤ t ∧ t ≤ 7 / (8 * m) ∧ LonelyAt ds t := (Gate.exceeds_seven_iff hpos hm).mp hcross
  have hm0 : 0 < m := hpos m hm.1
  have h0 : seq 0 = 1 / (8 * m) := cascadeSeq_zero _ _
  have hge : ∀ n, 1 / (8 * m) ≤ seq n := fun n => h0 ▸ start_le_seq hpos hmv n
  classical
  let N0 := Nat.find hcross
  have hN0 : 7 / (8 * m) < seq N0 := Nat.find_spec hcross
  have hlt : ∀ n, n < N0 → seq n ≤ 7 / (8 * m) := fun n hn => not_lt.mp (Nat.find_min hcross hn)
  have hN0pos : N0 ≠ 0 := by
    intro h
    have : 7 / (8 * m) < seq 0 := h ▸ hN0
    rw [h0] at this
    have : 1 / (8 * m) < 1 / (8 * m) := lt_of_le_of_lt
      (div_le_div_of_nonneg_right (by norm_num) (by positivity)) this
    exact lt_irrefl _ this
  -- for `n < N0` the move is a setter move with a zone
  have hzone : ∀ n, n < N0 → ∃ d ∈ ds, ∃ j : ℤ, zoneLo d j < seq n ∧ seq n < zoneHi d j ∧ seq (n + 1) = zoneHi d j := by
    intro n hn
    have hnl : ¬ LonelyAt ds (seq n) := fun hl => hno ⟨seq n, hge n, hlt n hn, hl⟩
    rcases hmv n with ⟨hnone, _⟩ | ⟨d, hd, hw, hsd, _⟩
    · exact absurd (fun d hd => not_inWay_iff.mp (hnone d hd)) hnl
    · obtain ⟨a, b, c⟩ := zone_of_inWay (hpos d hd) hw
      exact ⟨d, hd, lap d (seq n), a, b, hsd.trans c⟩
  choose! x hxmem k hxk using hzone
  obtain ⟨N, hN⟩ : ∃ N, N0 = N + 1 := Nat.exists_eq_succ_of_ne_zero hN0pos
  have hNlt : ∀ n, n ≤ N → n < N0 := fun n hn => by omega
  refine ⟨N, x, k, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    exact hxmem n (hNlt n hn)
  · have := (hxk 0 (hNlt 0 (Nat.zero_le _))).1
    rwa [h0] at this
  · have := (hxk 0 (hNlt 0 (Nat.zero_le _))).2.1
    rwa [h0] at this
  · intro n hn
    have a := hxk n (hNlt n hn.le)
    have b := hxk (n + 1) (hNlt (n + 1) hn)
    constructor
    · rw [← a.2.2]; exact b.1
    · calc zoneHi (x n) (k n) = seq (n + 1) := a.2.2.symm
        _ < zoneHi (x (n + 1)) (k (n + 1)) := b.2.1
  · have a := hxk N (hNlt N le_rfl)
    rw [← a.2.2]
    have : seq (N + 1) = seq N0 := by rw [hN]
    rw [this]
    exact hN0

#print axioms pattern_of_crosser

/-! ## (3) Crossers and patterns coincide -/

/-- **The crossing cells (exact).**  For a finite set `ds` of positive disparities with least element `m`, the cascade from
`1/(8m)` has a state above `7/(8m)` (`R > 7`) iff `ds` admits a setter-lap pattern.  The crossing set is therefore the
union, over all patterns, of the cells `PatternLinear`, each an intersection of finitely many open half-spaces that are
linear in the disparities. -/
theorem crosser_iff_pattern {ds : Finset ℝ} {m : ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hm : IsLeast (ds : Set ℝ) m) :
    (∃ n, 7 / (8 * m) < cascadeSeq ds (1 / (8 * m)) n) ↔ ∃ (N : ℕ) (x : ℕ → ℝ) (k : ℕ → ℤ), PatternCell ds m N x k := by
  constructor
  · exact pattern_of_crosser hpos hm
  · rintro ⟨N, x, k, hp⟩
    exact (Gate.exceeds_seven_iff hpos hm).mpr (fun ⟨t, h1, h7, hl⟩ => pattern_no_lonely hpos hp h1 h7 hl)

#print axioms crosser_iff_pattern

/-- The same, in linear form. -/
theorem crosser_iff_linear_pattern {ds : Finset ℝ} {m : ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hm : IsLeast (ds : Set ℝ) m) :
    (∃ n, 7 / (8 * m) < cascadeSeq ds (1 / (8 * m)) n) ↔
      ∃ (N : ℕ) (x : ℕ → ℝ) (k : ℕ → ℤ), PatternLinear ds m N x k := by
  have hm0 : 0 < m := hpos m hm.1
  rw [crosser_iff_pattern hpos hm]
  constructor
  · rintro ⟨N, x, k, h⟩
    exact ⟨N, x, k, (patternCell_iff_linear hm0 hpos).mp h⟩
  · rintro ⟨N, x, k, h⟩
    exact ⟨N, x, k, (patternCell_iff_linear hm0 hpos).mpr h⟩

#print axioms crosser_iff_linear_pattern

/-! ## (4) Necessary conditions from single instants -/

/-- **Every instant of the window has a runner in the way** (a crosser has no lonely instant in `R ∈ [1, 7]`). -/
theorem crosser_blocked {ds : Finset ℝ} {m : ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hm : IsLeast (ds : Set ℝ) m)
    (hcross : ∃ n, 7 / (8 * m) < cascadeSeq ds (1 / (8 * m)) n) {s : ℝ} (h1 : 1 / (8 * m) ≤ s)
    (h7 : s ≤ 7 / (8 * m)) : ∃ d ∈ ds, InWay d s := by
  have hno := (Gate.exceeds_seven_iff hpos hm).mp hcross
  by_contra hc
  push Not at hc
  exact hno ⟨s, h1, h7, fun d hd => not_inWay_iff.mp (hc d hd)⟩

#print axioms crosser_blocked

/-- **The instant `R = r` of a crosser** (`1 ≤ r ≤ 7`, `s = r/(8m)`): some disparity `d` has `(8j-1)·m < r·d < (8j+1)·m`
for a lap `j ≥ 1`, i.e. its reading `d/m` lies in `((8j-1)/r, (8j+1)/r)`. -/
theorem crosser_zone_at {ds : Finset ℝ} {m : ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hm : IsLeast (ds : Set ℝ) m)
    (hcross : ∃ n, 7 / (8 * m) < cascadeSeq ds (1 / (8 * m)) n) {r : ℝ} (hr1 : 1 ≤ r) (hr7 : r ≤ 7) :
    ∃ d ∈ ds, ∃ j : ℤ, 1 ≤ j ∧ (8 * (j : ℝ) - 1) * m < r * d ∧ r * d < (8 * (j : ℝ) + 1) * m := by
  have hm0 : 0 < m := hpos m hm.1
  have hs1 : 1 / (8 * m) ≤ r / (8 * m) := div_le_div_of_nonneg_right hr1 (by positivity)
  have hs7 : r / (8 * m) ≤ 7 / (8 * m) := div_le_div_of_nonneg_right hr7 (by positivity)
  obtain ⟨d, hd, hw⟩ := crosser_blocked hpos hm hcross hs1 hs7
  have hd0 := hpos d hd
  have hdm : m ≤ d := hm.2 hd
  obtain ⟨a, b, -⟩ := zone_of_inWay hd0 hw
  unfold zoneLo at a
  unfold zoneHi at b
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at a b
  refine ⟨d, hd, lap d (r / (8 * m)), ?_, by nlinarith, by nlinarith⟩
  -- `j ≥ 1`: `r d ≥ m` and `r d < (8j + 1) m`
  by_contra hj
  push Not at hj
  have hj0 : (lap d (r / (8 * m)) : ℝ) ≤ 0 := by exact_mod_cast Int.lt_add_one_iff.mp hj
  nlinarith

#print axioms crosser_zone_at

/-- **First zone (`R = 1`).**  A crosser has a disparity `x` with `(8j-1)·m < x < (8j+1)·m` for a lap `j ≥ 1`; in
particular a disparity above `7·m` (a reading above `7`). -/
theorem crosser_first_zone {ds : Finset ℝ} {m : ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hm : IsLeast (ds : Set ℝ) m)
    (hcross : ∃ n, 7 / (8 * m) < cascadeSeq ds (1 / (8 * m)) n) :
    ∃ x ∈ ds, ∃ j : ℤ, 1 ≤ j ∧ (8 * (j : ℝ) - 1) * m < x ∧ x < (8 * (j : ℝ) + 1) * m ∧ 7 * m < x := by
  have hm0 : 0 < m := hpos m hm.1
  obtain ⟨d, hd, j, hj, a, b⟩ := crosser_zone_at hpos hm hcross (r := 1) le_rfl (by norm_num)
  refine ⟨d, hd, j, hj, by linarith, by linarith, ?_⟩
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  nlinarith

#print axioms crosser_first_zone

/-- **Last zone (`R = 7`).**  A crosser has a disparity `x` with `(8j-1)·m < 7·x < (8j+1)·m` for a lap `j ≥ 1`: a reading
in `((8j-1)/7, (8j+1)/7)`, for example `(15/7, 17/7)` at `j = 2`. -/
theorem crosser_last_zone {ds : Finset ℝ} {m : ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hm : IsLeast (ds : Set ℝ) m)
    (hcross : ∃ n, 7 / (8 * m) < cascadeSeq ds (1 / (8 * m)) n) :
    ∃ x ∈ ds, ∃ j : ℤ, 1 ≤ j ∧ (8 * (j : ℝ) - 1) * m < 7 * x ∧ 7 * x < (8 * (j : ℝ) + 1) * m :=
  crosser_zone_at hpos hm hcross (r := 7) (by norm_num) le_rfl

#print axioms crosser_last_zone

/-- **Integer disparities with least element `M`: a crosser has a disparity of at least `7·M + 1`.** -/
theorem int_crosser_top {ds : Finset ℝ} (hint : ∀ d ∈ ds, ∃ z : ℤ, d = z) {M : ℤ}
    (hm : IsLeast (ds : Set ℝ) (M : ℝ)) (hpos : ∀ d ∈ ds, 0 < d)
    (hcross : ∃ n, 7 / (8 * (M : ℝ)) < cascadeSeq ds (1 / (8 * (M : ℝ))) n) :
    ∃ z : ℤ, (z : ℝ) ∈ ds ∧ 7 * M + 1 ≤ z := by
  obtain ⟨x, hx, j, hj, a, b, c⟩ := crosser_first_zone hpos hm hcross
  obtain ⟨z, rfl⟩ := hint x hx
  refine ⟨z, hx, ?_⟩
  have : (7 * M : ℝ) < z := by exact_mod_cast c
  have : 7 * M < z := by exact_mod_cast this
  omega

#print axioms int_crosser_top

/-- **A crosser needs at least eight moves.**  Each move multiplies the instant by less than `9/7` (`Gate.seq_le_pow`) and
`(9/7)^7 < 7`.  (The cells found in the exact data have between 16 and 23 letters; this lower bound is much weaker.) -/
theorem crosser_index_ge_eight {ds : Finset ℝ} {m : ℝ} (hm : 0 < m) (hlow : ∀ d ∈ ds, m ≤ d) {n : ℕ}
    (hn : 7 / (8 * m) < cascadeSeq ds (1 / (8 * m)) n) : 8 ≤ n := by
  by_contra hlt
  push Not at hlt
  have h1 := Gate.seq_le_pow hm hlow n
  have h2 : ((9 : ℝ) / 7) ^ n ≤ (9 / 7) ^ 7 :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : ((9 : ℝ) / 7) ^ 7 < 7 := by norm_num
  have h4 : (9 / 7 : ℝ) ^ n * (1 / (8 * m)) < 7 / (8 * m) := by
    have : (9 / 7 : ℝ) ^ n < 7 := lt_of_le_of_lt h2 h3
    have hp : (0 : ℝ) < 1 / (8 * m) := by positivity
    calc (9 / 7 : ℝ) ^ n * (1 / (8 * m)) < 7 * (1 / (8 * m)) := by gcongr
      _ = 7 / (8 * m) := by ring
  linarith

#print axioms crosser_index_ge_eight


/-- **In a crosser the first two moves are forward, with different setters.**  Before the first state above `7/(8m)` every
state is not lonely (`Gate.exceeds_seven_iff`), so a runner is in the way and sets the move; the setter of the second move
is in the way at the opening of the first, so it differs from the first (`Dilation.consecutive_setters_ne`). -/
theorem crosser_first_two_setters {ds : Finset ℝ} {m : ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hm : IsLeast (ds : Set ℝ) m)
    (hcross : ∃ n, 7 / (8 * m) < cascadeSeq ds (1 / (8 * m)) n) :
    ∃ x y, ChainLaws.IsSetterAt ds (cascadeSeq ds (1 / (8 * m))) 0 x ∧
      ChainLaws.IsSetterAt ds (cascadeSeq ds (1 / (8 * m))) 1 y ∧ x ≠ y := by
  have hm0 : 0 < m := hpos m hm.1
  have hlow : ∀ d ∈ ds, m ≤ d := fun d hd => hm.2 hd
  have hno := (Gate.exceeds_seven_iff hpos hm).mp hcross
  have hmv := cascadeSeq_isMove ds (1 / (8 * m))
  have hge : ∀ n, 1 / (8 * m) ≤ cascadeSeq ds (1 / (8 * m)) n := fun n => by
    have := start_le_seq hpos hmv n; rwa [cascadeSeq_zero] at this
  -- a state in the window is not lonely, so its move is a setter move
  have hset : ∀ n, cascadeSeq ds (1 / (8 * m)) n ≤ 7 / (8 * m) →
      ∃ x, ChainLaws.IsSetterAt ds (cascadeSeq ds (1 / (8 * m))) n x := by
    intro n hn
    have hnl : ¬ LonelyAt ds (cascadeSeq ds (1 / (8 * m)) n) := fun hl => hno ⟨_, hge n, hn, hl⟩
    rcases hmv n with ⟨hnone, _⟩ | ⟨d, hd, hw, hsd, _⟩
    · exact absurd (fun d hd => not_inWay_iff.mp (hnone d hd)) hnl
    · exact ⟨d, hd, hw, hsd⟩
  have h0 : cascadeSeq ds (1 / (8 * m)) 0 ≤ 7 / (8 * m) := by
    rw [cascadeSeq_zero]
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  obtain ⟨x, hx⟩ := hset 0 h0
  have h1 : cascadeSeq ds (1 / (8 * m)) 1 ≤ 7 / (8 * m) := by
    have := Gate.seq_le_pow hm0 hlow 1
    have h7 : (9 / 7 : ℝ) ^ 1 * (1 / (8 * m)) ≤ 7 / (8 * m) := by
      rw [pow_one, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  obtain ⟨y, hy⟩ := hset 1 h1
  refine ⟨x, y, hx, hy, ?_⟩
  intro hxy
  -- `y` is in the way at the opening of `x`
  have hseq : cascadeSeq ds (1 / (8 * m)) 1 = nextOpening x (cascadeSeq ds (1 / (8 * m)) 0) := hx.2.2
  exact Dilation.consecutive_setters_ne hpos hx.1 hseq hy.2.1 hxy.symm

#print axioms crosser_first_two_setters

/-- **A crosser has two distinct disparities above `(49/9)·m`**: the setters of the first two moves are distinct and each
exceeds `7·m·(7/9)` (`Gate.staircase_setter`).  No counting step. -/
theorem crosser_two_large {ds : Finset ℝ} {m : ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hm : IsLeast (ds : Set ℝ) m)
    (hcross : ∃ n, 7 / (8 * m) < cascadeSeq ds (1 / (8 * m)) n) :
    ∃ x ∈ ds, ∃ y ∈ ds, x ≠ y ∧ 7 * m * (7 / 9) ^ 1 < x ∧ 7 * m * (7 / 9) ^ 1 < y := by
  have hm0 : 0 < m := hpos m hm.1
  have hlow : ∀ d ∈ ds, m ≤ d := fun d hd => hm.2 hd
  obtain ⟨x, y, hx, hy, hxy⟩ := crosser_first_two_setters hpos hm hcross
  exact ⟨x, hx.1, y, hy.1, hxy, Gate.staircase_setter hm0 hlow (i := 0) (k := 1) (by norm_num) hx,
    Gate.staircase_setter hm0 hlow (i := 1) (k := 1) le_rfl hy⟩

#print axioms crosser_two_large

/-- **Rank form.**  With seven disparities, the second largest exceeds `(49/9)·m`.
[PROVISIONAL: counting tool] two distinct elements above `c` put the sixth-ranked of seven above `c`
(`Gate.staircase_rank`); the step supports the claim "the second largest disparity exceeds `49m/9`". -/
theorem crosser_second_largest {ds : Finset ℝ} {m : ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hm : IsLeast (ds : Set ℝ) m)
    (hcross : ∃ n, 7 / (8 * m) < cascadeSeq ds (1 / (8 * m)) n) (hcard : ds.card = 7) :
    7 * m * (7 / 9) ^ 1 < ds.orderEmbOfFin hcard ⟨5, by norm_num⟩ := by
  obtain ⟨x, hx, y, hy, hxy, h1, h2⟩ := crosser_two_large hpos hm hcross
  have hsub : ({x, y} : Finset ℝ) ⊆ ds.filter (fun z => 7 * m * (7 / 9) ^ 1 < z) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Finset.mem_filter.mpr ⟨hx, h1⟩
    · rw [Finset.mem_singleton.mp hz]; exact Finset.mem_filter.mpr ⟨hy, h2⟩
  have : 2 ≤ (ds.filter (fun z => 7 * m * (7 / 9) ^ 1 < z)).card := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair hxy] at this
  exact Gate.staircase_rank (k := 1) hcard (by norm_num) this

#print axioms crosser_second_largest

/-- **Integers.**  A crosser with integer disparities and least element `M` has two distinct disparities `z, w` with
`49·M < 9·z` and `49·M < 9·w` (so `z, w ≥ ⌊49M/9⌋ + 1`).  Together with `int_crosser_top` (a disparity `≥ 7M + 1`) and the
multiples of `StrongGateStudy` this is the list of necessary conditions on the large disparities. -/
theorem int_crosser_two_large {ds : Finset ℝ} (hint : ∀ d ∈ ds, ∃ z : ℤ, d = z) {M : ℤ}
    (hm : IsLeast (ds : Set ℝ) (M : ℝ)) (hpos : ∀ d ∈ ds, 0 < d)
    (hcross : ∃ n, 7 / (8 * (M : ℝ)) < cascadeSeq ds (1 / (8 * (M : ℝ))) n) :
    ∃ z w : ℤ, (z : ℝ) ∈ ds ∧ (w : ℝ) ∈ ds ∧ z ≠ w ∧ 49 * M < 9 * z ∧ 49 * M < 9 * w := by
  obtain ⟨x, hx, y, hy, hxy, h1, h2⟩ := crosser_two_large hpos hm hcross
  obtain ⟨z, rfl⟩ := hint x hx
  obtain ⟨w, rfl⟩ := hint y hy
  refine ⟨z, w, hx, hy, fun h => hxy (by rw [h]), ?_, ?_⟩
  · have : (49 * M : ℝ) < 9 * z := by norm_num at h1; linarith
    exact_mod_cast this
  · have : (49 * M : ℝ) < 9 * w := by norm_num at h2; linarith
    exact_mod_cast this

#print axioms int_crosser_two_large

/-! ## (5) Scale: only the denominator of the reading vector matters -/

/-- A pattern cell is invariant under `ds ↦ c·ds`, `m ↦ c·m`, `xₙ ↦ c·xₙ` (`R` is scale free). -/
theorem patternLinear_scale {ds : Finset ℝ} {m c : ℝ} (hc : 0 < c) {N : ℕ} {x : ℕ → ℝ} {k : ℕ → ℤ}
    (h : PatternLinear ds m N x k) :
    PatternLinear (ds.image (fun d => c * d)) (c * m) N (fun n => c * x n) k := by
  obtain ⟨hmem, h0, h0', hstep, hend⟩ := h
  refine ⟨fun n hn => Finset.mem_image.mpr ⟨x n, hmem n hn, rfl⟩, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · intro n hn
    obtain ⟨a, b⟩ := hstep n hn
    constructor <;> nlinarith
  · nlinarith

#print axioms patternLinear_scale

/-- **Crossing is invariant under common scaling** (one direction; the other is the same statement with `c⁻¹`). -/
theorem crosser_scale {ds : Finset ℝ} {m c : ℝ} (hc : 0 < c) (hpos : ∀ d ∈ ds, 0 < d) (hm : IsLeast (ds : Set ℝ) m)
    (hcross : ∃ n, 7 / (8 * m) < cascadeSeq ds (1 / (8 * m)) n) :
    ∃ n, 7 / (8 * (c * m)) < cascadeSeq (ds.image (fun d => c * d)) (1 / (8 * (c * m))) n := by
  have hpos' : ∀ d ∈ ds.image (fun d => c * d), 0 < d := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    exact mul_pos hc (hpos e he)
  have hm' : IsLeast ((ds.image (fun d => c * d) : Finset ℝ) : Set ℝ) (c * m) := by
    refine ⟨Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨m, hm.1, rfl⟩), ?_⟩
    intro d hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hd)
    exact mul_le_mul_of_nonneg_left (hm.2 he) hc.le
  rw [crosser_iff_linear_pattern hpos' hm']
  obtain ⟨N, x, k, h⟩ := (crosser_iff_linear_pattern hpos hm).mp hcross
  exact ⟨N, _, k, patternLinear_scale hc h⟩

#print axioms crosser_scale

/-! ## (5b) The other side: lonely windows are closed cells indexed by lap vectors -/

/-- **A lonely instant in the window, as a lap vector.**  A lonely instant `t ∈ [1/(8m), 7/(8m)]` exists iff there are laps
`kd` (one per disparity) such that the clear windows `[(8kd+1)/(8d), (8kd+7)/(8d)]` pairwise meet and each meets the
window: `(8kd+1)·e ≤ (8ke+7)·d`, `d ≤ (8kd+7)·m`, `(8kd+1)·m ≤ 7·d`.  Each lap vector is a closed polyhedral cell, linear in
the disparities; the non-crossers are their union and the crossers its complement (1-dimensional Helly: intervals
that meet pairwise have a common point, namely the largest left end). -/
theorem lonely_in_window_iff {ds : Finset ℝ} {m : ℝ} (hm0 : 0 < m) (hne : ds.Nonempty) (hpos : ∀ d ∈ ds, 0 < d) :
    (∃ t, 1 / (8 * m) ≤ t ∧ t ≤ 7 / (8 * m) ∧ LonelyAt ds t) ↔
      ∃ k : ℝ → ℤ, ∀ d ∈ ds, (d ≤ (8 * (k d : ℝ) + 7) * m ∧ (8 * (k d : ℝ) + 1) * m ≤ 7 * d) ∧
        ∀ e ∈ ds, (8 * (k d : ℝ) + 1) * e ≤ (8 * (k e : ℝ) + 7) * d := by
  constructor
  · rintro ⟨t, h1, h7, hl⟩
    refine ⟨fun d => ⌊d * t⌋, fun d hd => ?_⟩
    have hd0 := hpos d hd
    have hf := (Localisation.clear_iff_fract _).mp (hl d hd)
    have ha : (8 * (⌊d * t⌋ : ℝ) + 1) ≤ 8 * (d * t) := by unfold Int.fract at hf; linarith [hf.1]
    have hb : 8 * (d * t) ≤ 8 * (⌊d * t⌋ : ℝ) + 7 := by unfold Int.fract at hf; linarith [hf.2]
    rw [div_le_iff₀ (by positivity)] at h1
    rw [le_div_iff₀ (by positivity)] at h7
    refine ⟨⟨by nlinarith, by nlinarith⟩, fun e he => ?_⟩
    have he0 := hpos e he
    have hf' := (Localisation.clear_iff_fract _).mp (hl e he)
    have hb' : 8 * (e * t) ≤ 8 * (⌊e * t⌋ : ℝ) + 7 := by unfold Int.fract at hf'; linarith [hf'.2]
    -- `(8 kd + 1) e ≤ 8 d e t ≤ (8 ke + 7) d`
    have hdt : 0 < t := by
      have : 0 < 1 / (8 * m) := by positivity
      linarith [show 1 / (8 * m) ≤ t from by
        rw [div_le_iff₀ (by positivity)]; exact h1.trans' (le_of_eq (by ring))]
    nlinarith [mul_pos hd0 he0, mul_pos hd0 hdt, mul_pos he0 hdt]
  · rintro ⟨k, hk⟩
    -- the largest left end, or the start of the window
    obtain ⟨d0, hd0, hmax⟩ := ds.exists_max_image (fun d => (8 * (k d : ℝ) + 1) / (8 * d)) hne
    set t := max (1 / (8 * m)) ((8 * (k d0 : ℝ) + 1) / (8 * d0)) with ht
    have hd00 := hpos d0 hd0
    have hlo : ∀ d ∈ ds, (8 * (k d : ℝ) + 1) / (8 * d) ≤ t := fun d hd =>
      (hmax d hd).trans (le_max_right _ _)
    have hhi : ∀ d ∈ ds, t ≤ (8 * (k d : ℝ) + 7) / (8 * d) := by
      intro d hd
      have hd0' := hpos d hd
      apply max_le
      · rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [(hk d hd).1.1]
      · rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [(hk d0 hd0).2 d hd]
    refine ⟨t, le_max_left _ _, ?_, ?_⟩
    · apply max_le
      · exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
      · rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [(hk d0 hd0).1.2]
    · intro d hd
      have hd0' := hpos d hd
      have h1 := hlo d hd
      have h2 := hhi d hd
      rw [div_le_iff₀ (by positivity)] at h1
      rw [le_div_iff₀ (by positivity)] at h2
      exact Localisation.clear_of_window (k d) (by nlinarith) (by nlinarith)

#print axioms lonely_in_window_iff

/-- **Crossers, dually.**  The cascade crosses `R = 7` iff for every lap vector some pair (or window) condition fails. -/
theorem crosser_iff_all_laps_fail {ds : Finset ℝ} {m : ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hm : IsLeast (ds : Set ℝ) m) :
    (∃ n, 7 / (8 * m) < cascadeSeq ds (1 / (8 * m)) n) ↔
      ∀ k : ℝ → ℤ, ∃ d ∈ ds, (¬ (d ≤ (8 * (k d : ℝ) + 7) * m ∧ (8 * (k d : ℝ) + 1) * m ≤ 7 * d)) ∨
        ∃ e ∈ ds, ¬ ((8 * (k d : ℝ) + 1) * e ≤ (8 * (k e : ℝ) + 7) * d) := by
  have hm0 : 0 < m := hpos m hm.1
  have hne : ds.Nonempty := ⟨m, hm.1⟩
  rw [Gate.exceeds_seven_iff hpos hm, lonely_in_window_iff hm0 hne hpos]
  constructor
  · intro h k
    by_contra hc
    push Not at hc
    exact h ⟨k, fun d hd => by
      obtain ⟨a, b⟩ := hc d hd
      exact ⟨a, b⟩⟩
  · intro h ⟨k, hk⟩
    obtain ⟨d, hd, hc⟩ := h k
    rcases hc with hc | ⟨e, he, hc⟩
    · exact hc (hk d hd).1
    · exact hc ((hk d hd).2 e he)

#print axioms crosser_iff_all_laps_fail

/-! ## (5c) Integer disparities: the cells are integer programs with slack one -/

/-- A pattern for integer disparities `a n` with least element `M`: every strict inequality of `PatternLinear` holds with
slack at least `1` (the left side plus one is at most the right side). -/
-- STANDING: DEFINITION
def IntPattern (M : ℤ) (N : ℕ) (a k : ℕ → ℤ) : Prop :=
  (8 * k 0 - 1) * M + 1 ≤ a 0 ∧ a 0 + 1 ≤ (8 * k 0 + 1) * M ∧
  (∀ n, n < N → (8 * k (n + 1) - 1) * a n + 1 ≤ (8 * k n + 1) * a (n + 1) ∧
    (8 * k n + 1) * a (n + 1) + 1 ≤ (8 * k (n + 1) + 1) * a n) ∧
  7 * a N + 1 ≤ (8 * k N + 1) * M

/-- **For integer disparities a crosser is an integer solution of a pattern.**  If `ds` consists of integers, has least
element `M` and every `a n` is one of its elements, then `PatternLinear` and `IntPattern` agree. -/
theorem patternLinear_iff_intPattern {ds : Finset ℝ} {M : ℤ} {N : ℕ} {a k : ℕ → ℤ}
    (hmem : ∀ n, n ≤ N → ((a n : ℤ) : ℝ) ∈ ds) :
    PatternLinear ds (M : ℝ) N (fun n => (a n : ℝ)) k ↔ IntPattern M N a k := by
  unfold PatternLinear IntPattern
  beta_reduce
  constructor
  · rintro ⟨-, h0, h0', hstep, hend⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : (8 * k 0 - 1) * M < a 0 := by exact_mod_cast h0
      omega
    · have : a 0 < (8 * k 0 + 1) * M := by exact_mod_cast h0'
      omega
    · intro n hn
      obtain ⟨u, v⟩ := hstep n hn
      have u' : (8 * k (n + 1) - 1) * a n < (8 * k n + 1) * a (n + 1) := by exact_mod_cast u
      have v' : (8 * k n + 1) * a (n + 1) < (8 * k (n + 1) + 1) * a n := by exact_mod_cast v
      constructor <;> omega
    · have : 7 * a N < (8 * k N + 1) * M := by exact_mod_cast hend
      omega
  · rintro ⟨h0, h0', hstep, hend⟩
    refine ⟨hmem, ?_, ?_, ?_, ?_⟩
    · have : (8 * k 0 - 1) * M < a 0 := by omega
      exact_mod_cast this
    · have : a 0 < (8 * k 0 + 1) * M := by omega
      exact_mod_cast this
    · intro n hn
      obtain ⟨u, v⟩ := hstep n hn
      have u' : (8 * k (n + 1) - 1) * a n < (8 * k n + 1) * a (n + 1) := by omega
      have v' : (8 * k n + 1) * a (n + 1) < (8 * k (n + 1) + 1) * a n := by omega
      exact ⟨by exact_mod_cast u', by exact_mod_cast v'⟩
    · have : 7 * a N < (8 * k N + 1) * M := by omega
      exact_mod_cast this

#print axioms patternLinear_iff_intPattern


/-- **Near multiples for every `q` in the window (integers).**  For a crosser with integer disparities and least element `M`,
and every `q` with `8M/7 ≤ q ≤ 8M`, some disparity `z` is within `q/8` of a multiple of `q` (`8·|z - q·w| < q`).  For `q ≤ 8`
this says `q ∣ z` (`StrongGateStudy.crosser_needs_multiple`); for `q = 9, …, 16` it says `z ≡ 0, ±1 (mod q)`, and so on. -/
theorem int_crosser_near_multiple {ds : Finset ℝ} (hint : ∀ d ∈ ds, ∃ z : ℤ, d = z) {M : ℤ}
    (hm : IsLeast (ds : Set ℝ) (M : ℝ)) (hpos : ∀ d ∈ ds, 0 < d)
    (hcross : ∃ n, 7 / (8 * (M : ℝ)) < cascadeSeq ds (1 / (8 * (M : ℝ))) n) {q : ℕ} (hq : 1 ≤ q)
    (hqlo : 8 * M ≤ 7 * (q : ℤ)) (hqhi : (q : ℤ) ≤ 8 * M) :
    ∃ z w : ℤ, (z : ℝ) ∈ ds ∧ 8 * |z - (q : ℤ) * w| < (q : ℤ) := by
  have hM0 : (0 : ℝ) < M := hpos _ hm.1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqlo' : 8 * (M : ℝ) ≤ 7 * q := by exact_mod_cast hqlo
  have hqhi' : (q : ℝ) ≤ 8 * M := by exact_mod_cast hqhi
  have h1 : 1 / (8 * (M : ℝ)) ≤ 1 / (q : ℝ) := one_div_le_one_div_of_le hq0 hqhi'
  have h7 : 1 / (q : ℝ) ≤ 7 / (8 * (M : ℝ)) := by
    rw [div_le_div_iff₀ hq0 (by positivity)]
    linarith
  obtain ⟨d, hd, hw⟩ := crosser_blocked hpos hm hcross h1 h7
  obtain ⟨z, rfl⟩ := hint d hd
  refine ⟨z, round ((z : ℝ) * (1 / (q : ℝ))), hd, ?_⟩
  have hw' : |(z : ℝ) * (1 / (q : ℝ)) - round ((z : ℝ) * (1 / (q : ℝ)))| < 1 / 8 := hw
  have e : (z : ℝ) * (1 / (q : ℝ)) - round ((z : ℝ) * (1 / (q : ℝ))) =
      ((z : ℝ) - (q : ℝ) * (round ((z : ℝ) * (1 / (q : ℝ))) : ℤ)) / q := by
    field_simp
  rw [e, abs_div, abs_of_pos hq0, div_lt_iff₀ hq0] at hw'
  have : 8 * |(z : ℝ) - (q : ℝ) * (round ((z : ℝ) * (1 / (q : ℝ))) : ℤ)| < q := by linarith
  exact_mod_cast this

#print axioms int_crosser_near_multiple

/-! ## (7) A certified crosser: `{6, 16, 21, 26, 29, 36, 45}` has a pattern of 19 letters

The pattern is the setter-lap word of the cascade (computed with exact fractions; the readings `ρ = x/6` give the zones).
`ex_pattern` checks all its linear conditions by `norm_num`; `ex_crosser` then gives, through `crosser_iff_linear_pattern`,
a state of the cascade above `R = 7`.  This is the smallest crosser of the exhaustive data (`d_min = 6`, `a₇ = 45`). -/

noncomputable def exDs : Finset ℝ := {6, 16, 21, 26, 29, 36, 45}

noncomputable def exX : ℕ → ℝ
  | 0 => 45 | 1 => 36 | 2 => 29 | 3 => 26 | 4 => 21 | 5 => 36 | 6 => 16 | 7 => 29 | 8 => 26 | 9 => 36
  | 10 => 45 | 11 => 21 | 12 => 29 | 13 => 36 | 14 => 26 | 15 => 16 | 16 => 45 | 17 => 36 | 18 => 21
  | _ => 21

def exK : ℕ → ℤ
  | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 2 | 6 => 1 | 7 => 2 | 8 => 2 | 9 => 3
  | 10 => 4 | 11 => 2 | 12 => 3 | 13 => 4 | 14 => 3 | 15 => 2 | 16 => 6 | 17 => 5 | 18 => 3
  | _ => 3

theorem ex_pattern : PatternLinear exDs 6 18 exX exK := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    interval_cases n <;> simp [exX, exDs]
  · simp [exX, exK]; norm_num
  · simp [exX, exK]; norm_num
  · intro n hn
    interval_cases n <;> simp [exX, exK] <;> norm_num
  · simp [exX, exK]; norm_num

#print axioms ex_pattern

theorem ex_crosser : ∃ n, 7 / (8 * (6 : ℝ)) < cascadeSeq exDs (1 / (8 * (6 : ℝ))) n := by
  have hpos : ∀ d ∈ exDs, 0 < d := by
    intro d hd
    simp only [exDs, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hm : IsLeast (exDs : Set ℝ) 6 := by
    refine ⟨by simp [exDs], ?_⟩
    intro d hd
    simp only [exDs, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  exact (crosser_iff_linear_pattern hpos hm).mpr ⟨18, exX, exK, ex_pattern⟩

#print axioms ex_crosser


/-! ## (8) The extremal non-crossers for `d_min = 3, 4, 5`: explicit lonely instants

The largest first-lonely instant in the exhaustive data (`a₇ ≤ 100`) is `R* = 17/3, 68/11, 125/19` for `d_min = 3, 4, 5`,
attained by the sets below (`R = 8·m·t`; `t = 17/72, 17/88, 25/152`).  The lemmas certify the *upper* bound `R* ≤ R*_data` for
these three sets (a lonely instant inside the window); that no set does better is the enumeration, [OBS]. -/

theorem lonely_m3 : LonelyAt ({3, 9, 11, 14, 15, 19, 24} : Finset ℝ) (17 / 72) := by
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Localisation.clear_of_window 0 (by norm_num) (by norm_num)
  · exact Localisation.clear_of_window 2 (by norm_num) (by norm_num)
  · exact Localisation.clear_of_window 2 (by norm_num) (by norm_num)
  · exact Localisation.clear_of_window 3 (by norm_num) (by norm_num)
  · exact Localisation.clear_of_window 3 (by norm_num) (by norm_num)
  · exact Localisation.clear_of_window 4 (by norm_num) (by norm_num)
  · exact Localisation.clear_of_window 5 (by norm_num) (by norm_num)

theorem lonely_m4 : LonelyAt ({4, 11, 14, 17, 19, 24, 30} : Finset ℝ) (17 / 88) := by
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Localisation.clear_of_window 0 (by norm_num) (by norm_num)
  · exact Localisation.clear_of_window 2 (by norm_num) (by norm_num)
  · exact Localisation.clear_of_window 2 (by norm_num) (by norm_num)
  · exact Localisation.clear_of_window 3 (by norm_num) (by norm_num)
  · exact Localisation.clear_of_window 3 (by norm_num) (by norm_num)
  · exact Localisation.clear_of_window 4 (by norm_num) (by norm_num)
  · exact Localisation.clear_of_window 5 (by norm_num) (by norm_num)

theorem lonely_m5 : LonelyAt ({5, 14, 19, 23, 26, 32, 41} : Finset ℝ) (25 / 152) := by
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Localisation.clear_of_window 0 (by norm_num) (by norm_num)
  · exact Localisation.clear_of_window 2 (by norm_num) (by norm_num)
  · exact Localisation.clear_of_window 3 (by norm_num) (by norm_num)
  · exact Localisation.clear_of_window 3 (by norm_num) (by norm_num)
  · exact Localisation.clear_of_window 4 (by norm_num) (by norm_num)
  · exact Localisation.clear_of_window 5 (by norm_num) (by norm_num)
  · exact Localisation.clear_of_window 6 (by norm_num) (by norm_num)

#print axioms lonely_m3
#print axioms lonely_m4
#print axioms lonely_m5


/-! ## (6) What is not proved here -/

/-- **The observation (OWED).**  No integer disparity set of seven elements with least element `3`, `4` or `5` has a
cascade state above `R = 7`.  Exhaustive exact enumeration for `a₇ ≤ 100` (this task, and Agents U and W) finds none; the
values `m ≤ 2` follow from `Types.no_crossing_of_small_dmin` once an isolation is known.  Not proved. -/
-- STANDING: OWED
def NoSmallIntegerCrosser : Prop :=
  ∀ (ds : Finset ℝ) (m : ℝ), ds.card = 7 → (∀ d ∈ ds, ∃ z : ℤ, d = z) → IsLeast (ds : Set ℝ) m →
    (m = 3 ∨ m = 4 ∨ m = 5) → ¬ ∃ n, 7 / (8 * m) < cascadeSeq ds (1 / (8 * m)) n

/-- **The smallest reading (OWED).**  In a crosser every disparity other than `d_min` exceeds `15/7` times `d_min`.
[OBS]: all lattice crossers found (denominators `6 … 30`, tens of thousands of points) and the polytope vertices of
the cells listed in the report; the value `15/7` is where the second zone of a reading enters the window `R ≤ 7`
(`15/ρ < 7`).  Not proved. -/
-- STANDING: OWED
def ReadingsAboveFifteenSevenths : Prop :=
  ∀ (ds : Finset ℝ) (m : ℝ), ds.card = 7 → (∀ d ∈ ds, 0 < d) → IsLeast (ds : Set ℝ) m →
    (∃ n, 7 / (8 * m) < cascadeSeq ds (1 / (8 * m)) n) → ∀ d ∈ ds, d ≠ m → 15 * m < 7 * d


end SmallDmin

end Fresh
