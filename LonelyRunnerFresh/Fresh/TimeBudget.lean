import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.DispCell
import Fresh.Ladder5
import Fresh.LawOfPosition
import Fresh.ChainLaws
import Fresh.Dilation

/-!
# The time budget of a cascade stretch (Task BG)

Written 2026-10-09.  Imports `Mathlib` and the Fresh modules named in the task.  Nothing is imported from the existing
`LonelyRunner` repo.  Exact reals only; every disparity is positive (no runner is stationary); no floats.

## What this file does

The owner's deduction (relayed 2026-10-09) is assessed and formalised for REAL positive disparities and ANY cascade
stretch from state `n` to state `m` (no periodicity, no integrality, the unit `d_min` is just one of the setters).

* (1) The telescoping sum `seq m - seq n = ∑ (seq (s+1) - seq s)`; the per-move advance is below the setter's zone width
  `1/(4 x)` (`advance_lt_zone`, which is `DispCell.displacement_nonneg_lt` read at the cascade; `advance_eq_displacement`
  is the bridge); `length_lt_sum_cnt`: `L < ∑_x c_x / (4 x)` with `c_x = cnt w n m x` the number of moves of the stretch
  whose chosen setter is `x`.  **[PROVISIONAL: covering]**: zone widths against the stretch length; it supports the
  necessary condition on an endless cascade (a stretch has no fixed step) and NO existence claim.
* (2) `cnt_le`: `c_x ≤ x L + 1` and `c_x ≤ ⌊x L⌋ + 1`: distinct landings of `x` are distinct openings of `x`, each in
  the stretch.  **[PROVISIONAL: counting tool]**, a count of openings in a stretch; supports the density bound
  `ρ_x ≤ 1 + 1/(x L)`, no existence claim.
* (3) `rho_sum_gt_four`: `∑ ρ_x > 4` with `ρ_x = c_x / (x L)`, for every stretch with `L > 0`.  **[PROVISIONAL: counting
  tool]** (density sum; same supported claim).  `two_above_margin`: at least two readings have `ρ_x > 1/2 - ε/6`, where
  `ε ≥ 1/(x L)` for every `x` (seven readings).  The margin is EXACT: `one_above_half_consistent` shows that `∑ρ > 4`,
  `ρ_x ≤ 1 + ε` do NOT force a second reading above `1/2` (the relay's "above `1/2` up to the `1/(xL)` correction" is the
  statement with `1/2 - ε/6`; it is not `> 1/2`).
* (4) The per-reading constraint: `return_budget_stretch`:
  `3 (c_x - 1) ≤ x ∑_{w ≠ x} c_w / w` (strict when `c_x ≥ 2`), and in densities `reading_constraint`:
  `∑_{w ≠ x} ρ_w ≥ 3 ρ_x - 3/(x L)`.  It is the sum of `Ladder5.budget_sum` over the consecutive settings of `x`.
  **[PROVISIONAL: counting tool]** (a sum of budgets over the returns of `x`; supports the necessary condition on an
  endless cascade, no existence claim).  `budget_all_readings`: summing over `x`, `(4 - n) S ≤ 3 H` with `S = ∑ c_x/x`,
  `H = ∑ 1/x`, `n = card E`; `length_lt_of_card_le_three`: for `n ≤ 3`, `L < (3/4) H`.
* (5) The linear system in the limit densities (`DensitySystem n`): infeasible for `n ≤ 3` (`densitySystem_three_false`),
  a single point for `n = 4` (`densitySystem_four_all_one`), feasible for every `n ≥ 5`, in particular `n = 7`
  (`densitySystem_seven`).  So the density constraints cannot exclude an endless cascade of seven disparities.

NOT proved here: any existence statement.  Nothing in this file bounds the number of moves; the statements are
conditional on a stretch whose every move has a setter.  Rule 7: every counting or covering step is tagged at the step.

Provenance (existing declarations whose argument was read and understood, nothing copied): `Ladder5.budget_sum`,
`Ladder5.incr_setter`, `LawOfPosition.lap_identity`, `LawOfPosition.lap_diff_pos`, `DispCell.displacement_nonneg_lt`.
-/

open Classical

namespace Fresh

namespace TimeBudget

open Cascade Dilation ChainLaws Ladder5 LawOfPosition

/-! ## (0) Setup: stretches, chosen setters, counts -/

/-- The number of moves `s ∈ [n, m)` whose chosen setter is `x`. -/
noncomputable def cnt (w : ℕ → ℝ) (n m : ℕ) (x : ℝ) : ℕ := ((Finset.Ico n m).filter (fun s => w s = x)).card

/-- An endless cascade (no fixed step) has a setter at every step. -/
theorem endless_setter {E : Finset ℝ} {seq : ℕ → ℝ} (hmv : ∀ n, IsMove E (seq n) (seq (n + 1)))
    (hend : ∀ N, seq (N + 1) ≠ seq N) (s : ℕ) : ∃ y, IsSetterAt E seq s y := by
  rcases hmv s with ⟨_, hfix⟩ | ⟨d, hd, hwd, hdt, _⟩
  · exact absurd hfix (hend s)
  · exact ⟨d, hd, hwd, hdt⟩

#print axioms endless_setter

/-! ## (1) The telescoping sum and the zone width -/

/-- **Telescoping** [L]: the stretch length is the sum of the advances. -/
theorem telescope (seq : ℕ → ℝ) (n : ℕ) : ∀ i : ℕ,
    seq (n + i) - seq n = ∑ s ∈ Finset.Ico n (n + i), (seq (s + 1) - seq s) := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    rw [show n + (i + 1) = n + i + 1 by ring, Finset.sum_Ico_succ_top (by omega)]
    linarith

#print axioms telescope

/-- Bridge to `DispCell`: the advance of a move with setter `x` is the displacement `disp x (seq s) - seq s`. -/
theorem advance_eq_displacement {E : Finset ℝ} {seq : ℕ → ℝ} {s : ℕ} {x : ℝ} (hx : IsSetterAt E seq s x) :
    seq (s + 1) - seq s = DispCell.displacement x (seq s) := by
  unfold DispCell.displacement DispCell.disp
  rw [if_pos hx.2.1, hx.2.2]

#print axioms advance_eq_displacement

/-- **The advance of each move is below the setter's zone width** [L] (the relay's `DispCell.displacement_nonneg_lt`,
read at the cascade through the bridge): `0 ≤ seq (s+1) - seq s < 1/(4 x)`. -/
theorem advance_lt_zone {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) {s : ℕ} {x : ℝ}
    (hx : IsSetterAt E seq s x) : 0 ≤ seq (s + 1) - seq s ∧ seq (s + 1) - seq s < 1 / (4 * x) := by
  rw [advance_eq_displacement hx]
  exact DispCell.displacement_nonneg_lt (hpos x hx.1) (seq s)

#print axioms advance_lt_zone

/-- Sum of a function of the chosen setter over the stretch, grouped by setter. -/
theorem sum_by_setter {E : Finset ℝ} {w : ℕ → ℝ} {n m : ℕ} (hwE : ∀ s, n ≤ s → s < m → w s ∈ E) (f : ℝ → ℝ) :
    ∑ s ∈ Finset.Ico n m, f (w s) = ∑ x ∈ E, (cnt w n m x : ℝ) * f x := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := w) (t := E) (fun s hs => by
    have := Finset.mem_Ico.mp hs
    exact hwE s this.1 this.2)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_congr rfl (fun s hs => by rw [(Finset.mem_filter.mp hs).2] : ∀ s ∈ (Finset.Ico n m).filter (fun s => w s = x), f (w s) = f x)]
  rw [Finset.sum_const, nsmul_eq_mul]
  rfl

#print axioms sum_by_setter

/-- **The stretch length is below the sum of the zone widths of its setters** [L], **[PROVISIONAL: covering]**
(zone widths against the stretch length; supports the necessary condition on an endless cascade: a stretch of `m - n`
moves each with a setter has `L < (1/4) ∑_x c_x / x`; NO existence claim).
`L = seq m - seq n`, `c_x = cnt w n m x`, `w s` the chosen setter of the move at `s`.  Hypotheses: `hpos`, `n < m`, a
setter at every step of the stretch (REQUIRED: a fixed step has none; the stretch of a cascade that fixes ends there). -/
theorem length_lt_sum_cnt {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) {w : ℕ → ℝ} {n m : ℕ} (hnm : n < m)
    (hws : ∀ s, n ≤ s → s < m → IsSetterAt E seq s (w s)) :
    seq m - seq n < ∑ x ∈ E, (cnt w n m x : ℝ) * (1 / (4 * x)) := by
  have hwE : ∀ s, n ≤ s → s < m → w s ∈ E := fun s h1 h2 => (hws s h1 h2).1
  rw [← sum_by_setter hwE (fun y => 1 / (4 * y))]
  have htel := telescope seq n (m - n)
  rw [show n + (m - n) = m by omega] at htel
  rw [htel]
  refine Finset.sum_lt_sum_of_nonempty ⟨n, Finset.mem_Ico.mpr ⟨le_refl _, hnm⟩⟩ (fun s hs => ?_)
  have := Finset.mem_Ico.mp hs
  exact (advance_lt_zone hpos (hws s this.1 this.2)).2

#print axioms length_lt_sum_cnt

/-! ## (1b) Monotonicity, the lap order and the budget on a stretch, from the forward moves alone

The maximality clause of `IsMove` (the move goes to the LARGEST next opening) is not used anywhere below: a forward move
`seq (s+1) = nextOpening x (seq s)` already advances (`incr_setter`), so a stretch with a setter at every step is
monotone, and the lap order and the budget law follow.  These are re-derivations of `ChainLaws.seq_mono`,
`LawOfPosition.lap_diff_pos` and `Ladder5.budget_sum` on a stretch, with the hypothesis `hmv` dropped. -/

/-- A stretch with a setter at every step is monotone [L]. -/
theorem seq_mono_stretch {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) {w : ℕ → ℝ} {n m : ℕ}
    (hws : ∀ s, n ≤ s → s < m → IsSetterAt E seq s (w s)) :
    ∀ a b, n ≤ a → a ≤ b → b ≤ m → seq a ≤ seq b := by
  intro a b hna hab
  induction b, hab using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ b hab ih =>
    intro hb
    have h1 := ih (by omega)
    have h2 := (incr_setter hpos (hws b (by omega) (by omega))).1
    linarith

#print axioms seq_mono_stretch

/-- Two settings of one reading inside a stretch are on strictly increasing laps [L] (`LawOfPosition.lap_diff_pos` without
`hmv`). -/
theorem lap_diff_pos_stretch {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) {w : ℕ → ℝ} {n m : ℕ}
    (hws : ∀ s, n ≤ s → s < m → IsSetterAt E seq s (w s)) {a k : ℕ} (hna : n ≤ a) (hak : a < k) (hkm : k < m) {x : ℝ}
    (ha : IsSetterAt E seq a x) (hk : IsSetterAt E seq k x) : lap x (seq a) < lap x (seq k) := by
  have hx0 := hpos x ha.1
  have h1 : seq (a + 1) ≤ seq k := seq_mono_stretch hpos hws (a + 1) k (by omega) (by omega) hkm.le
  have h2 : seq k < seq (k + 1) := by
    have := (incr_setter hpos hk).1
    linarith
  have hid := lap_identity hx0 ha hk
  have hpos' : 0 < x * (seq (k + 1) - seq (a + 1)) := mul_pos hx0 (by linarith)
  have : (lap x (seq a) : ℝ) < (lap x (seq k) : ℝ) := by linarith
  exact_mod_cast this

#print axioms lap_diff_pos_stretch

/-- **The budget law of a return on a stretch** [L] (`Ladder5.budget_sum` with `hmv` dropped): `x` sets at `a`, is in the
way at `seq k`, `a < k ≤ m`, a setter at every step: `3 < ∑_{s=a+1}^{k-1} x / w s`. -/
theorem budget_stretch {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) {w : ℕ → ℝ} {n m : ℕ}
    (hws : ∀ s, n ≤ s → s < m → IsSetterAt E seq s (w s)) {a k : ℕ} (hna : n ≤ a) (hak : a < k) (hkm : k ≤ m) {x : ℝ}
    (hx : IsSetterAt E seq a x) (hw : InWay x (seq k)) :
    3 < ∑ s ∈ Finset.Ico (a + 1) k, x / w s := by
  have hx0 := hpos x hx.1
  have hland : x * seq (a + 1) = (lap x (seq a) : ℝ) + 1 / 8 := by
    rw [hx.2.2]; exact setter_reading hx0 hx.2.1
  have hle : seq (a + 1) ≤ seq k := seq_mono_stretch hpos hws (a + 1) k (by omega) (by omega) hkm
  have h1 : x * seq (a + 1) ≤ x * seq k := mul_le_mul_of_nonneg_left hle hx0.le
  have hb := abs_lt.mp (abs_sub_lap_lt hw)
  have hlap0 : (lap x (seq a) : ℝ) < (lap x (seq k) : ℝ) := by linarith
  have hlap1 : lap x (seq a) < lap x (seq k) := by exact_mod_cast hlap0
  have hlap' : (lap x (seq a) : ℝ) + 1 ≤ (lap x (seq k) : ℝ) := by
    have : lap x (seq a) + 1 ≤ lap x (seq k) := by omega
    exact_mod_cast this
  have h34 : 3 / 4 < x * (seq k - seq (a + 1)) := by nlinarith [hb.1]
  have hsum := sum_incr hpos (a + 1) w (k - (a + 1)) (by
    intro s h1 h2
    exact hws s (by omega) (by omega))
  rw [show a + 1 + (k - (a + 1)) = k by omega] at hsum
  have hmul : x * (seq k - seq (a + 1)) ≤ x * ∑ s ∈ Finset.Ico (a + 1) k, 1 / (4 * w s) :=
    mul_le_mul_of_nonneg_left hsum hx0.le
  have hcongr : x * ∑ s ∈ Finset.Ico (a + 1) k, 1 / (4 * w s) = (∑ s ∈ Finset.Ico (a + 1) k, x / w s) / 4 := by
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hs' := Finset.mem_Ico.mp hs
    have hw0 := hpos _ (hws s (by omega) (by omega)).1
    field_simp
  rw [hcongr] at hmul
  linarith

#print axioms budget_stretch

/-! ## (2) Distinct landings of `x` are distinct openings of `x` -/

/-- **`c_x ≤ x L + 1`** [L], **[PROVISIONAL: counting tool]** (a count of the openings of `x` in the stretch; supports the
density bound `ρ_x ≤ 1 + 1/(x L)`; NO existence claim).  The landings of `x` have `x · landing = lap + 1/8` with
the laps strictly increasing (`LawOfPosition.lap_diff_pos`), all between `x · seq (n+1)` and `x · seq m`, so the number of
distinct laps is at most the length of that interval plus one.  Hypotheses: `hpos`, `n ≤ m`, a setter at every
step of the stretch.  NOT REQUIRED: the maximality clause of `IsMove` (the cascade moves `hmv`), `0 < seq 0`, any
ordering or lower bound of the disparities, integrality, periodicity, a base `m`; the unit `d_min` is an ordinary member. -/
theorem cnt_le {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d)
    {w : ℕ → ℝ} {n m : ℕ} (hnm : n ≤ m)
    (hws : ∀ s, n ≤ s → s < m → IsSetterAt E seq s (w s)) (x : ℝ) (hx : x ∈ E) :
    (cnt w n m x : ℝ) ≤ x * (seq m - seq n) + 1 := by
  have hx0 := hpos x hx
  have hL : 0 ≤ seq m - seq n := by have := seq_mono_stretch hpos hws n m le_rfl hnm le_rfl; linarith
  have hxL : 0 ≤ x * (seq m - seq n) := mul_nonneg hx0.le hL
  by_cases hS : ((Finset.Ico n m).filter (fun s => w s = x)).Nonempty
  · set S := (Finset.Ico n m).filter (fun s => w s = x) with hSdef
    have hmem : ∀ s ∈ S, n ≤ s ∧ s < m ∧ IsSetterAt E seq s x := by
      intro s hs
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hs
      obtain ⟨a, b⟩ := Finset.mem_Ico.mp h1
      refine ⟨a, b, ?_⟩
      have := hws s a b
      rwa [h2] at this
    set s0 := S.min' hS with hs0
    set s1 := S.max' hS with hs1
    have h0m := hmem s0 (Finset.min'_mem S hS)
    have h1m := hmem s1 (Finset.max'_mem S hS)
    have hlt : ∀ s ∈ S, ∀ s' ∈ S, s < s' → lap x (seq s) < lap x (seq s') := fun s hs s' hs' h =>
      lap_diff_pos_stretch hpos hws (hmem s hs).1 h (hmem s' hs').2.1 (hmem s hs).2.2 (hmem s' hs').2.2
    have hlo : ∀ s ∈ S, lap x (seq s0) ≤ lap x (seq s) := by
      intro s hs
      rcases eq_or_lt_of_le (show s0 ≤ s from Finset.min'_le S s hs) with h | h
      · rw [h]
      · exact (hlt _ (Finset.min'_mem S hS) s hs h).le
    have hhi : ∀ s ∈ S, lap x (seq s) ≤ lap x (seq s1) := by
      intro s hs
      rcases eq_or_lt_of_le (show s ≤ s1 from Finset.le_max' S s hs) with h | h
      · rw [h]
      · exact (hlt s hs _ (Finset.max'_mem S hS) h).le
    have hinj : Set.InjOn (fun s => lap x (seq s)) (S : Set ℕ) := by
      intro a ha b hb hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact (hlt a ha b hb h).ne hab
      · exact (hlt b hb a ha h).ne hab.symm
    have hcard : S.card ≤ (Finset.Icc (lap x (seq s0)) (lap x (seq s1))).card :=
      Finset.card_le_card_of_injOn (fun s => lap x (seq s)) (fun s hs =>
        Finset.mem_Icc.mpr ⟨hlo s hs, hhi s hs⟩) hinj
    rw [Int.card_Icc] at hcard
    have hord : lap x (seq s0) ≤ lap x (seq s1) := hlo s1 (Finset.max'_mem S hS)
    have hid := lap_identity hx0 h0m.2.2 h1m.2.2
    have hs1m : seq (s1 + 1) ≤ seq m := seq_mono_stretch hpos hws (s1 + 1) m (by omega) (by omega) le_rfl
    have hs0n : seq n ≤ seq (s0 + 1) := seq_mono_stretch hpos hws n (s0 + 1) le_rfl (by omega) (by omega)
    have hdiff : ((lap x (seq s1) : ℝ) - (lap x (seq s0) : ℝ)) ≤ x * (seq m - seq n) := by
      rw [← hid]
      have : seq (s1 + 1) - seq (s0 + 1) ≤ seq m - seq n := by linarith
      exact mul_le_mul_of_nonneg_left this hx0.le
    have hnat : ((lap x (seq s1) + 1 - lap x (seq s0)).toNat : ℝ) = (lap x (seq s1) : ℝ) + 1 - (lap x (seq s0) : ℝ) := by
      have h0 : 0 ≤ lap x (seq s1) + 1 - lap x (seq s0) := by omega
      have := Int.toNat_of_nonneg h0
      have h2 : (((lap x (seq s1) + 1 - lap x (seq s0)).toNat : ℤ) : ℝ) = ((lap x (seq s1) + 1 - lap x (seq s0) : ℤ) : ℝ) := by
        rw [this]
      push_cast at h2
      exact_mod_cast h2
    have hc : (S.card : ℝ) ≤ ((lap x (seq s1) + 1 - lap x (seq s0)).toNat : ℝ) := by exact_mod_cast hcard
    unfold cnt
    rw [← hSdef]
    linarith
  · have : cnt w n m x = 0 := by
      unfold cnt
      rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      rfl
    rw [this]
    simpa using hxL.trans (le_add_of_nonneg_right zero_le_one)

#print axioms cnt_le

/-- The same in natural numbers: `c_x ≤ ⌊x L⌋ + 1` [L], **[PROVISIONAL: counting tool]**, same supported claim. -/
theorem cnt_le_floor {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d)
    {w : ℕ → ℝ} {n m : ℕ} (hnm : n ≤ m)
    (hws : ∀ s, n ≤ s → s < m → IsSetterAt E seq s (w s)) (x : ℝ) (hx : x ∈ E) :
    cnt w n m x ≤ ⌊x * (seq m - seq n)⌋₊ + 1 := by
  have h := cnt_le hpos hnm hws x hx
  rcases Nat.eq_zero_or_pos (cnt w n m x) with h0 | h0
  · omega
  · have : ((cnt w n m x - 1 : ℕ) : ℝ) ≤ x * (seq m - seq n) := by
      rw [Nat.cast_sub h0]; push_cast; linarith
    have := Nat.le_floor this
    omega

#print axioms cnt_le_floor

/-! ## (3) The densities: the sum exceeds four; the pigeonhole with its exact margin -/

/-- The stretch has positive length once it has a move (each advance is positive: `Ladder5.incr_setter`). -/
theorem length_pos {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) {w : ℕ → ℝ} {n m : ℕ} (hnm : n < m)
    (hws : ∀ s, n ≤ s → s < m → IsSetterAt E seq s (w s)) : 0 < seq m - seq n := by
  have htel := telescope seq n (m - n)
  rw [show n + (m - n) = m by omega] at htel
  rw [htel]
  exact Finset.sum_pos (fun s hs => by
    have := Finset.mem_Ico.mp hs
    have := (incr_setter hpos (hws s this.1 this.2)).1
    linarith) ⟨n, Finset.mem_Ico.mpr ⟨le_refl _, hnm⟩⟩

#print axioms length_pos

/-- The density of the reading `x` over a stretch of length `L`: `ρ_x = c_x / (x L)`. -/
noncomputable def rho (w : ℕ → ℝ) (n m : ℕ) (L x : ℝ) : ℝ := (cnt w n m x : ℝ) / (x * L)

/-- **The density bound** [L], **[PROVISIONAL: counting tool]** (from `cnt_le`; supports `ρ_x ≤ 1 + 1/(xL)`; no existence
claim): `ρ_x ≤ 1 + 1/(x L)`. -/
theorem rho_le {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d)
    {w : ℕ → ℝ} {n m : ℕ} (hnm : n < m)
    (hws : ∀ s, n ≤ s → s < m → IsSetterAt E seq s (w s)) (x : ℝ) (hx : x ∈ E) :
    rho w n m (seq m - seq n) x ≤ 1 + 1 / (x * (seq m - seq n)) := by
  have hL := length_pos hpos hnm hws
  have hx0 := hpos x hx
  have hxL : 0 < x * (seq m - seq n) := mul_pos hx0 hL
  have h := cnt_le hpos hnm.le hws x hx
  unfold rho
  rw [div_le_iff₀ hxL, add_mul, one_div, inv_mul_cancel₀ hxL.ne']
  linarith

#print axioms rho_le

/-- **The density sum exceeds four** [L], **[PROVISIONAL: counting tool]** (density sum, from `length_lt_sum_cnt`; supports the
necessary condition on an endless cascade; no existence claim): `4 < ∑_x ρ_x` for every stretch with a setter at each step. -/
theorem rho_sum_gt_four {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d) {w : ℕ → ℝ} {n m : ℕ} (hnm : n < m)
    (hws : ∀ s, n ≤ s → s < m → IsSetterAt E seq s (w s)) :
    4 < ∑ x ∈ E, rho w n m (seq m - seq n) x := by
  have hL := length_pos hpos hnm hws
  have h := length_lt_sum_cnt hpos hnm hws
  have e : ∑ x ∈ E, rho w n m (seq m - seq n) x = (∑ x ∈ E, (cnt w n m x : ℝ) * (1 / (4 * x))) * 4 / (seq m - seq n) := by
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have := hpos x hx
    unfold rho
    field_simp
  rw [e, lt_div_iff₀ hL]
  linarith

#print axioms rho_sum_gt_four

/-- Abstract pigeonhole [L], **[PROVISIONAL: counting tool]** (pigeonhole over seven readings; supports the necessary
condition on an endless cascade; no existence claim).  Seven values, each at most `1 + ε`, with sum above `4`: at least two
exceed `1/2 - ε/6`.  The margin is exact (`one_above_half_consistent`). -/
theorem two_above_abstract (E : Finset ℝ) (hcard : E.card = 7) (ρ : ℝ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hle : ∀ x ∈ E, ρ x ≤ 1 + ε) (hsum : 4 < ∑ x ∈ E, ρ x) :
    ∃ x ∈ E, ∃ y ∈ E, x ≠ y ∧ (3 - ε) / 6 < ρ x ∧ (3 - ε) / 6 < ρ y := by
  by_contra hcon
  push Not at hcon
  by_cases hz : ∃ z ∈ E, (3 - ε) / 6 < ρ z
  · obtain ⟨z, hzE, hz⟩ := hz
    have hothers : ∀ y ∈ E.erase z, ρ y ≤ (3 - ε) / 6 := by
      intro y hy
      have hyz := Finset.ne_of_mem_erase hy
      exact hcon z hzE y (Finset.mem_of_mem_erase hy) hyz.symm hz
    have h6 : ∑ y ∈ E.erase z, ρ y ≤ (E.erase z).card • ((3 - ε) / 6) := Finset.sum_le_card_nsmul _ _ _ hothers
    rw [Finset.card_erase_of_mem hzE, hcard] at h6
    rw [← Finset.add_sum_erase E ρ hzE] at hsum
    have := hle z hzE
    simp only [nsmul_eq_mul] at h6
    norm_num at h6
    linarith
  · push Not at hz
    have h7 : ∑ y ∈ E, ρ y ≤ E.card • ((3 - ε) / 6) := Finset.sum_le_card_nsmul _ _ _ hz
    rw [hcard] at h7
    simp only [nsmul_eq_mul] at h7
    norm_num at h7
    linarith

#print axioms two_above_abstract

/-- **At least two readings exceed `1/2 - ε/6`** [L], **[PROVISIONAL: counting tool]** (pigeonhole over the densities; same
supported claim): seven disparities, `ε ≥ 1/(x L)` for every `x ∈ E`. -/
theorem two_above_margin {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d)
    {w : ℕ → ℝ} {n m : ℕ} (hnm : n < m)
    (hws : ∀ s, n ≤ s → s < m → IsSetterAt E seq s (w s)) (hcard : E.card = 7) {ε : ℝ}
    (hε : ∀ x ∈ E, 1 / (x * (seq m - seq n)) ≤ ε) :
    ∃ x ∈ E, ∃ y ∈ E, x ≠ y ∧ (3 - ε) / 6 < rho w n m (seq m - seq n) x ∧
      (3 - ε) / 6 < rho w n m (seq m - seq n) y := by
  have hE : E.Nonempty := by
    rw [← Finset.card_pos, hcard]; norm_num
  obtain ⟨x0, hx0⟩ := hE
  have hL := length_pos hpos hnm hws
  have hε0 : 0 ≤ ε := le_trans (by have := hpos x0 hx0; positivity) (hε x0 hx0)
  exact two_above_abstract E hcard _ hε0 (fun x hx => (rho_le hpos hnm hws x hx).trans (by linarith [hε x hx]))
    (rho_sum_gt_four hpos hnm hws)

#print axioms two_above_margin

/-- **The margin is exact** [L]: for every `ε > 0` there are seven values, each at most `1 + ε`, with sum above `4`, of which
only one exceeds `1/2`.  So `∑ρ > 4` and `ρ_x ≤ 1 + ε` do NOT yield a second reading above `1/2`; they yield two above
`1/2 - ε/6` (`two_above_abstract`). -/
theorem one_above_half_consistent {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : Fin 7 → ℝ, 4 < ∑ i, ρ i ∧ (∀ i, ρ i ≤ 1 + ε) ∧ ∀ i j, i ≠ j → ρ i ≤ 1 / 2 ∨ ρ j ≤ 1 / 2 := by
  refine ⟨fun i => if i = 0 then 1 + ε else 1 / 2, ?_, ?_, ?_⟩
  · simp [Fin.sum_univ_succ]
    linarith
  · intro i
    by_cases h : i = 0
    · simp [h]
    · simp [h]; linarith
  · intro i j hij
    by_cases hi : i = 0
    · right
      have : j ≠ 0 := fun h => hij (hi.trans h.symm)
      simp [this]
    · left
      simp [hi]

#print axioms one_above_half_consistent

/-! ## (4) The per-reading constraint: the budgets of the returns of `x`, summed -/

/-- The number of moves in `[p, q)` whose chosen setter is `x`. -/
noncomputable def setCount (w : ℕ → ℝ) (x : ℝ) (p q : ℕ) : ℕ := ((Finset.Ico p q).filter (fun s => w s = x)).card

/-- The sum of `x / w s` over the moves of `[p, q)` whose chosen setter is NOT `x`. -/
noncomputable def offSum (w : ℕ → ℝ) (x : ℝ) (p q : ℕ) : ℝ := ∑ s ∈ Finset.Ico p q, if w s = x then 0 else x / w s

theorem setCount_add (w : ℕ → ℝ) (x : ℝ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    setCount w x a c = setCount w x a b + setCount w x b c := by
  unfold setCount
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.sum_Ico_consecutive _ hab hbc]

theorem offSum_add (w : ℕ → ℝ) (x : ℝ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    offSum w x a c = offSum w x a b + offSum w x b c := by
  unfold offSum
  rw [Finset.sum_Ico_consecutive _ hab hbc]

#print axioms setCount_add
#print axioms offSum_add

/-- If `q'` is a setting of `x` and there is none in `(q', q)`, then `[q', q)` holds exactly one setting. -/
theorem setCount_last (w : ℕ → ℝ) (x : ℝ) {q' q : ℕ} (h : q' < q) (hx : w q' = x)
    (hnone : ∀ s, q' < s → s < q → w s ≠ x) : setCount w x q' q = 1 := by
  unfold setCount
  rw [Finset.card_eq_one]
  refine ⟨q', ?_⟩
  ext s
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rcases eq_or_lt_of_le h1 with h4 | h4
    · exact h4.symm
    · exact absurd h3 (hnone s h4 h2)
  · rintro rfl
    exact ⟨⟨le_refl _, h⟩, hx⟩

#print axioms setCount_last

/-- Over `[q', q)` with `q'` a setting of `x` and none in between, the off-`x` sum is the sum over `(q', q)`. -/
theorem offSum_last (w : ℕ → ℝ) (x : ℝ) {q' q : ℕ} (h : q' < q) (hx : w q' = x)
    (hnone : ∀ s, q' < s → s < q → w s ≠ x) :
    offSum w x q' q = ∑ s ∈ Finset.Ico (q' + 1) q, x / w s := by
  unfold offSum
  rw [Finset.sum_eq_sum_Ico_succ_bot h, if_pos hx, zero_add]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  have := Finset.mem_Ico.mp hs
  rw [if_neg (hnone s (by omega) this.2)]

#print axioms offSum_last

/-- **The chain of returns** [L], **[PROVISIONAL: counting tool]** (a sum of budgets over the returns of `x`; supports the
necessary condition on an endless cascade; no existence claim).  Between two settings `p ≤ q` of `x` inside the stretch,
`3 · #{settings of x in [p, q)} ≤` the off-`x` sum `∑ x / w s` over `[p, q)`, strictly when `p < q`.  Each consecutive pair of
settings contributes `Ladder5.budget_sum`.  Hypotheses: `hpos`, a setter at every step of the stretch (REQUIRED:
`budget_stretch` uses the setters of the intermediate moves).  NOT REQUIRED: any ordering of the readings, `0 < seq 0`,
integrality, periodicity. -/
theorem chain_of_returns {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d)
    {w : ℕ → ℝ} {n m : ℕ}
    (hws : ∀ s, n ≤ s → s < m → IsSetterAt E seq s (w s)) {x : ℝ} :
    ∀ q p, n ≤ p → p ≤ q → q < m → w p = x → w q = x →
      3 * (setCount w x p q : ℝ) ≤ offSum w x p q ∧ (p < q → 3 * (setCount w x p q : ℝ) < offSum w x p q) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro p hnp hpq hqm hpx hqx
    rcases eq_or_lt_of_le hpq with hpq' | hpq'
    · subst hpq'
      have h1 : setCount w x p p = 0 := by simp [setCount]
      have h2 : offSum w x p p = 0 := by simp [offSum]
      rw [h1, h2]
      exact ⟨by simp, fun h => absurd h (lt_irrefl _)⟩
    · set F := (Finset.Ico p q).filter (fun s => w s = x) with hF
      have hFne : F.Nonempty := ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨le_refl _, hpq'⟩, hpx⟩⟩
      set q' := F.max' hFne with hq'
      have hq'F := Finset.max'_mem F hFne
      obtain ⟨hq'I, hq'x⟩ := Finset.mem_filter.mp hq'F
      obtain ⟨hq'1, hq'2⟩ := Finset.mem_Ico.mp hq'I
      have hnone : ∀ s, q' < s → s < q → w s ≠ x := by
        intro s h1 h2 h3
        have : s ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, h2⟩, h3⟩
        have := Finset.le_max' F s this
        omega
      obtain ⟨ih1, _⟩ := ih q' hq'2 p hnp hq'1 (by omega) hpx hq'x
      have hsc : setCount w x p q = setCount w x p q' + 1 := by
        rw [setCount_add w x hq'1 hq'2.le, setCount_last w x hq'2 hq'x hnone]
      have hos : offSum w x p q = offSum w x p q' + ∑ s ∈ Finset.Ico (q' + 1) q, x / w s := by
        rw [offSum_add w x hq'1 hq'2.le, offSum_last w x hq'2 hq'x hnone]
      have hbud := budget_stretch hpos hws (a := q') (k := q) (by omega) hq'2 hqm.le (x := x) (by
          have := hws q' (by omega) (by omega)
          rwa [hq'x] at this)
        (by
          have := hws q (by omega) hqm
          rw [hqx] at this
          exact this.2.1)
      have hcast : (setCount w x p q : ℝ) = (setCount w x p q' : ℝ) + 1 := by exact_mod_cast hsc
      rw [hcast, hos]
      constructor <;> [skip; intro _] <;> linarith

#print axioms chain_of_returns

/-- The off-`x` sum over the whole stretch is `x ∑_{y ≠ x} c_y / y`. -/
theorem offSum_eq {E : Finset ℝ} {w : ℕ → ℝ} {n m : ℕ} (hwE : ∀ s, n ≤ s → s < m → w s ∈ E) {x : ℝ} (hx : x ∈ E) :
    offSum w x n m = x * ∑ y ∈ E.erase x, (cnt w n m y : ℝ) / y := by
  unfold offSum
  rw [sum_by_setter hwE (fun y => if y = x then 0 else x / y)]
  rw [← Finset.add_sum_erase E _ hx]
  simp only [if_true, mul_zero, zero_add]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  rw [if_neg (Finset.ne_of_mem_erase hy)]
  ring

#print axioms offSum_eq

/-- **The per-reading constraint on a stretch** [L], **[PROVISIONAL: counting tool]** (a sum of budgets over the returns of
`x`; supports the necessary condition on an endless cascade; no existence claim):
`3 (c_x - 1) ≤ x ∑_{y ≠ x} c_y / y`, strictly when `c_x ≥ 2`.  The `-1` is the boundary term: a reading set `c_x` times has
`c_x - 1` returns inside the stretch.  Hypotheses: `hpos`, a setter at every step of the stretch (NOT REQUIRED: `hmv`). -/
theorem return_budget_stretch {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d)
    {w : ℕ → ℝ} {n m : ℕ}
    (hws : ∀ s, n ≤ s → s < m → IsSetterAt E seq s (w s)) {x : ℝ} (hx : x ∈ E) :
    3 * ((cnt w n m x : ℝ) - 1) ≤ x * ∑ y ∈ E.erase x, (cnt w n m y : ℝ) / y ∧
      (2 ≤ cnt w n m x → 3 * ((cnt w n m x : ℝ) - 1) < x * ∑ y ∈ E.erase x, (cnt w n m y : ℝ) / y) := by
  have hwE : ∀ s, n ≤ s → s < m → w s ∈ E := fun s h1 h2 => (hws s h1 h2).1
  have hx0 := hpos x hx
  have hRnn : 0 ≤ x * ∑ y ∈ E.erase x, (cnt w n m y : ℝ) / y :=
    mul_nonneg hx0.le (Finset.sum_nonneg (fun y hy => div_nonneg (Nat.cast_nonneg _)
      (hpos y (Finset.mem_of_mem_erase hy)).le))
  by_cases hc : cnt w n m x = 0
  · rw [hc]
    refine ⟨by simp; linarith, fun h => by omega⟩
  · set F := (Finset.Ico n m).filter (fun s => w s = x) with hF
    have hFne : F.Nonempty := by
      rw [← Finset.card_pos]; exact Nat.pos_of_ne_zero hc
    set p := F.min' hFne with hp
    set q := F.max' hFne with hq
    obtain ⟨hpI, hpx⟩ := Finset.mem_filter.mp (Finset.min'_mem F hFne)
    obtain ⟨hqI, hqx⟩ := Finset.mem_filter.mp (Finset.max'_mem F hFne)
    obtain ⟨hp1, hp2⟩ := Finset.mem_Ico.mp hpI
    obtain ⟨hq1, hq2⟩ := Finset.mem_Ico.mp hqI
    have hpq : p ≤ q := Finset.min'_le_max' F hFne
    -- no setting before `p`, none after `q`
    have hbefore : setCount w x n p = 0 := by
      unfold setCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro s hs hsx
      have hs' := Finset.mem_Ico.mp hs
      have : s ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hs'.1, by omega⟩, hsx⟩
      have := Finset.min'_le F s this
      omega
    have hafter : ∀ s, q < s → s < m → w s ≠ x := by
      intro s h1 h2 h3
      have : s ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, h2⟩, h3⟩
      have := Finset.le_max' F s this
      omega
    have hcnt : cnt w n m x = setCount w x p q + 1 := by
      have e0 : cnt w n m x = setCount w x n m := rfl
      rw [e0, setCount_add w x (show n ≤ q by omega) hq2.le, setCount_last w x hq2 hqx hafter,
        setCount_add w x hp1 hpq, hbefore, zero_add]
    obtain ⟨hch1, hch2⟩ := chain_of_returns hpos hws q p hp1 hpq hq2 hpx hqx
    -- the off-sum over `[p, q)` is at most the off-sum over the whole stretch
    have hnn : ∀ s, n ≤ s → s < m → 0 ≤ (if w s = x then 0 else x / w s) := by
      intro s h1 h2
      split_ifs
      · exact le_refl _
      · exact div_nonneg hx0.le (hpos _ (hwE s h1 h2)).le
    have hle : offSum w x p q ≤ offSum w x n m := by
      unfold offSum
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun s hs => ?_) (fun s hs _ => ?_)
      · have := Finset.mem_Ico.mp hs
        exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      · have := Finset.mem_Ico.mp hs
        exact hnn s this.1 this.2
    rw [← offSum_eq hwE hx]
    have hcastc : (cnt w n m x : ℝ) = (setCount w x p q : ℝ) + 1 := by exact_mod_cast hcnt
    refine ⟨by rw [hcastc]; linarith, fun h2 => ?_⟩
    have hpq' : p < q := by
      rcases eq_or_lt_of_le hpq with h | h
      · exfalso
        have : setCount w x p q = 0 := by rw [h]; simp [setCount]
        omega
      · exact h
    have := hch2 hpq'
    rw [hcastc]
    linarith

#print axioms return_budget_stretch

/-- **The per-reading constraint in densities** [L], **[PROVISIONAL: counting tool]** (same supported claim as
`return_budget_stretch`; no existence claim): `∑_{y ≠ x} ρ_y ≥ 3 ρ_x - 3/(x L)`.  The correction `3/(x L)` is the boundary term. -/
theorem reading_constraint {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d)
    {w : ℕ → ℝ} {n m : ℕ} (hnm : n < m)
    (hws : ∀ s, n ≤ s → s < m → IsSetterAt E seq s (w s)) {x : ℝ} (hx : x ∈ E) :
    3 * rho w n m (seq m - seq n) x - 3 / (x * (seq m - seq n)) ≤ ∑ y ∈ E.erase x, rho w n m (seq m - seq n) y := by
  have hL := length_pos hpos hnm hws
  have hx0 := hpos x hx
  have hxL : 0 < x * (seq m - seq n) := mul_pos hx0 hL
  have h := (return_budget_stretch hpos hws hx).1
  have e : ∑ y ∈ E.erase x, rho w n m (seq m - seq n) y =
      (x * ∑ y ∈ E.erase x, (cnt w n m y : ℝ) / y) / (x * (seq m - seq n)) := by
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    have := hpos y (Finset.mem_of_mem_erase hy)
    unfold rho
    field_simp
  rw [e]
  have e2 : 3 * rho w n m (seq m - seq n) x - 3 / (x * (seq m - seq n)) =
      3 * ((cnt w n m x : ℝ) - 1) / (x * (seq m - seq n)) := by
    unfold rho
    field_simp
  rw [e2]
  exact div_le_div_of_nonneg_right h hxL.le

#print axioms reading_constraint

/-- The same constraint with the total: `4 c_x ≤ x S + 3` where `S = ∑_{y ∈ E} c_y / y` [L], **[PROVISIONAL: counting tool]**
(same supported claim).  Equivalently `ρ_x ≤ (∑ρ)/4 + 3/(4 x L)`: no reading has more than a quarter of the total density
(up to the boundary term). -/
theorem budget_cnt_form {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d)
    {w : ℕ → ℝ} {n m : ℕ}
    (hws : ∀ s, n ≤ s → s < m → IsSetterAt E seq s (w s)) {x : ℝ} (hx : x ∈ E) :
    4 * (cnt w n m x : ℝ) ≤ x * ∑ y ∈ E, (cnt w n m y : ℝ) / y + 3 := by
  have hx0 := hpos x hx
  have h := (return_budget_stretch hpos hws hx).1
  rw [Finset.sum_erase_eq_sub hx] at h
  have e : x * (∑ y ∈ E, (cnt w n m y : ℝ) / y - (cnt w n m x : ℝ) / x) =
      x * ∑ y ∈ E, (cnt w n m y : ℝ) / y - cnt w n m x := by
    rw [mul_sub]; congr 1; field_simp
  rw [e] at h
  linarith

#print axioms budget_cnt_form

/-- **Summing the constraint over all readings** [L], **[PROVISIONAL: counting tool]** (same supported claim):
`(4 - n) S ≤ 3 H`, `S = ∑ c_x / x`, `H = ∑ 1/x`, `n = card E`. -/
theorem budget_all_readings {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d)
    {w : ℕ → ℝ} {n m : ℕ}
    (hws : ∀ s, n ≤ s → s < m → IsSetterAt E seq s (w s)) :
    (4 - (E.card : ℝ)) * ∑ y ∈ E, (cnt w n m y : ℝ) / y ≤ 3 * ∑ y ∈ E, 1 / y := by
  set S := ∑ y ∈ E, (cnt w n m y : ℝ) / y with hS
  have hterm : ∀ x ∈ E, 4 * ((cnt w n m x : ℝ) / x) ≤ S + 3 * (1 / x) := by
    intro x hx
    have hx0 := hpos x hx
    have h := budget_cnt_form hpos hws hx
    rw [← hS] at h
    have : 4 * ((cnt w n m x : ℝ) / x) = 4 * (cnt w n m x : ℝ) / x := by ring
    rw [this, div_le_iff₀ hx0]
    have e : (S + 3 * (1 / x)) * x = S * x + 3 := by field_simp
    rw [e]
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, nsmul_eq_mul] at hsum
  rw [← hS] at hsum
  linarith

#print axioms budget_all_readings

/-- **Three or fewer disparities: the stretch is short** [L], **[PROVISIONAL: counting tool]** and **[PROVISIONAL: covering]**
(the sum of budgets and the zone widths against the length; a necessary-condition statement about a stretch with a setter at
every step, NOT an existence claim and NOT a bound on a number of moves): `card E ≤ 3` gives `L < (3/4) ∑ 1/x`.
This is the `n ≤ 3` infeasibility of the density system in its finite form (`densitySystem_le_three` is the limit form). -/
theorem length_lt_of_card_le_three {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d)
    {w : ℕ → ℝ} {n m : ℕ} (hnm : n < m)
    (hws : ∀ s, n ≤ s → s < m → IsSetterAt E seq s (w s)) (hcard : E.card ≤ 3) :
    seq m - seq n < 3 / 4 * ∑ y ∈ E, 1 / y := by
  have h1 := length_lt_sum_cnt hpos hnm hws
  have h2 := budget_all_readings hpos hws
  have hS0 : 0 ≤ ∑ y ∈ E, (cnt w n m y : ℝ) / y :=
    Finset.sum_nonneg (fun y hy => div_nonneg (Nat.cast_nonneg _) (hpos y hy).le)
  have hc : (E.card : ℝ) ≤ 3 := by exact_mod_cast hcard
  have e : ∑ x ∈ E, (cnt w n m x : ℝ) * (1 / (4 * x)) = (∑ y ∈ E, (cnt w n m y : ℝ) / y) / 4 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have := hpos x hx
    field_simp
  rw [e] at h1
  nlinarith

#print axioms length_lt_of_card_le_three

/-! ## (5) The linear system in the limit densities -/

/-- The density system in its limit form (the shadow of `rho_le`, `rho_sum_gt_four`, `reading_constraint` when the
corrections `1/(x L)` vanish): every density in `[0, 1]`, total at least `4`, and each density at most a third of the others'. -/
-- STANDING: DEFINITION
def DensitySystem (n : ℕ) (ρ : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ ρ i ∧ ρ i ≤ 1) ∧ 4 ≤ ∑ i, ρ i ∧ ∀ i, 3 * ρ i ≤ ∑ j, ρ j - ρ i

/-- **Infeasible for three or fewer readings** [L]: summing the per-reading constraints gives `(4 - n) ∑ρ ≤ 0`. -/
theorem densitySystem_le_three {n : ℕ} (hn : n ≤ 3) (ρ : Fin n → ℝ) : ¬ DensitySystem n ρ := by
  rintro ⟨hb, hs, hr⟩
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hr i)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hn' : (n : ℝ) ≤ 3 := by exact_mod_cast hn
  nlinarith

#print axioms densitySystem_le_three

/-- **Four readings: a single point** [L]: the system forces every density to be `1`. -/
theorem densitySystem_four_all_one (ρ : Fin 4 → ℝ) (h : DensitySystem 4 ρ) : ∀ i, ρ i = 1 := by
  obtain ⟨hb, hs, _⟩ := h
  rw [Fin.sum_univ_four] at hs
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  intro i
  fin_cases i <;> simp <;> linarith

#print axioms densitySystem_four_all_one

/-- The single point of the four-reading system satisfies it [L]. -/
theorem densitySystem_four_point : DensitySystem 4 (fun _ => 1) := by
  refine ⟨fun i => ⟨by norm_num, le_refl _⟩, ?_, fun i => ?_⟩ <;> simp <;> norm_num

#print axioms densitySystem_four_point

/-- **Feasible for every `n ≥ 5`** [L]: all densities `1`. -/
theorem densitySystem_ge_five {n : ℕ} (hn : 5 ≤ n) : DensitySystem n (fun _ => 1) := by
  have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨fun i => ⟨by norm_num, le_refl _⟩, ?_, fun i => ?_⟩
  · simp
    linarith
  · simp
    linarith

#print axioms densitySystem_ge_five

/-- **Seven readings: feasible, with every density strictly inside `(0, 1)`** [L]: all densities `9/10`.  The density
constraints alone do not exclude an endless cascade of seven disparities. -/
theorem densitySystem_seven : ∃ ρ : Fin 7 → ℝ, DensitySystem 7 ρ ∧ ∀ i, 0 < ρ i ∧ ρ i < 1 := by
  refine ⟨fun _ => 9 / 10, ⟨fun i => ⟨by norm_num, by norm_num⟩, ?_, fun i => ?_⟩, fun i => ⟨by norm_num, by norm_num⟩⟩
  · simp; norm_num
  · simp; norm_num

#print axioms densitySystem_seven

/-! ## (6) The statements on any stretch of an endless cascade -/

/-- **Any stretch of an endless cascade carries the necessary conditions** [L], **[PROVISIONAL: covering]** and
**[PROVISIONAL: counting tool]** (zone widths against the stretch length; a count of openings; a sum of budgets; they
support the necessary conditions on an endless cascade (no fixed step) and NO existence claim).  For an endless cascade on
positive disparities `E` and any `n < m` there is a choice `w` of setters with: the density sum above `4`, `c_x ≤ ⌊x L⌋ + 1`
for every `x`, and the per-reading constraint for every `x`.  The unit `d_min` is an ordinary member of `E`; nothing is
assumed about integrality or periodicity. -/
theorem endless_necessary {E : Finset ℝ} {seq : ℕ → ℝ} (hpos : ∀ d ∈ E, 0 < d)
    (hmv : ∀ n, IsMove E (seq n) (seq (n + 1))) (hend : ∀ N, seq (N + 1) ≠ seq N) {n m : ℕ} (hnm : n < m) :
    ∃ w : ℕ → ℝ, (∀ s, n ≤ s → s < m → IsSetterAt E seq s (w s)) ∧
      4 < ∑ x ∈ E, rho w n m (seq m - seq n) x ∧
      (∀ x ∈ E, cnt w n m x ≤ ⌊x * (seq m - seq n)⌋₊ + 1) ∧
      (∀ x ∈ E, 3 * rho w n m (seq m - seq n) x - 3 / (x * (seq m - seq n)) ≤
        ∑ y ∈ E.erase x, rho w n m (seq m - seq n) y) := by
  have hex : ∀ s, ∃ y, IsSetterAt E seq s y := endless_setter hmv hend
  choose w hw using hex
  exact ⟨w, fun s _ _ => hw s, rho_sum_gt_four hpos hnm (fun s _ _ => hw s),
    fun x hx => cnt_le_floor hpos hnm.le (fun s _ _ => hw s) x hx,
    fun x hx => reading_constraint hpos hnm (fun s _ _ => hw s) hx⟩

#print axioms endless_necessary

end TimeBudget

end Fresh
