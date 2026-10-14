import Mathlib
import Fresh.Framework
import Fresh.Gate
import Fresh.RealCase
import Fresh.DispCell
import Fresh.TwoScale
import Fresh.Boundaries

/-!
# The grid-plus-deviation normal form for real disparities (Task AX)

Written 2026-10-09.  Imports `Mathlib` and the Fresh modules `Framework`, `Gate`, `RealCase`, `DispCell`, `TwoScale`,
`Boundaries` (and, through them, `Cascade`); nothing from the existing `LonelyRunner` repo.  Exact reals only; no
floats; no runner is stationary; no density, coverage, cap or move budget is the shape of any statement.  No counting
or covering step is used in any proof in this file.

Setting.  `m > 0` is the base scale (in the application `m = d_min`), `ρ_d = d/m`, `idx_d = round ρ_d` (Lean's
`round`: the tie `ρ = k + 1/2` goes UP, so `e_d = ρ_d - idx_d ∈ [-1/2, 1/2)`; `idx_tie` records it), and
`R = 8 m t` is the gate coordinate, so the reading of `d` at `R` is `ρ_d R / 8` laps.  A runner is clear at `R` iff
`m8 (ρ_d R) ∈ [1,7]`, written `Win (ρ_d R)`.

Contents.
* (1) `reading_identity`: `ρ R = idx R + e R`.  `clear_at`: if `ρ R0 = N + x` (`N` an integer) then runner `ρ` is clear
  at `R0` iff `Win (N mod 8 + x)` (a corollary of `RealCase.clear_shift_iff`).  `clear_at_one`: at `R = 1` runner `d` is
  clear iff `Win (idx_d mod 8 + e_d)`, also iff `Win (d/m)` (`clear_at_one_rho`).
* (2) `win_class` (residue classes): for an integer `r ∈ [0,8)` and a real `x` with `|x| ≤ 1`,
  `Win (r + x)  ↔  (r = 0 → 1 ≤ |x|) ∧ (r = 1 → 0 ≤ x) ∧ (r = 7 → x ≤ 0)`.  So residues `2..6` are slack, residue `7`
  is clear iff `x ≤ 0`, residue `1` iff `x ≥ 0`, residue `0` is blocked iff `|x| < 1`.  The window `|x| ≤ 1` is
  tight: `win_mid_fails_below`, `win_mid_fails_above`, `win_seven_clear_at_two`, `win_one_clear_at_neg_two`.
* (3) `lonely_one_iff_n` (any integer assignment `n d` with `|ρ_d - n d| ≤ 1`), `lonely_one_iff` (nearest integer),
  `lonely_one_complete` (all non-unit residues in `2..7`), `lonely_one_complete_literal` (the six readings other than
  the unit have residues exactly `{2,..,7}` once each).
* (4) `dev_one_r0`, `dev_one_r1`, `dev_one_r7`: the signed residue `dev m 1 d` of a blocked runner; the opening offsets
  `(1 - e)/ρ`, `-e/ρ`, `(2 - e)/ρ`.  `first_move_r7`: the first cascade move when the residue-7 reading is the only
  blocked runner is `R = 1 + (2 - e)/ρ_7`.  (The brief's `(1 - e)/ρ` is the move for a blocked residue-0 runner; the
  signed residue of a residue-7 runner with `e > 0` is `e - 1`, hence `2 - e`.)
  `first_move_AP_perturbed`: `(1,…,6,7+e)` moves to `8 t' = 9/(7+e)`.  `blocked_one_class`, `isMove_one_classes`: the
  three blocked classes and their offsets.
* (5) `blocked_one_iff`: `R = 1` is blocked iff some reading has residue `0`, or residue `1` with `e < 0`, or residue
  `7` with `e > 0`.  `slack_erase`, `repeated_residue_not_blocking`, `repeated_residue_instance`: a reading with
  residue in `2..6` never matters, so two readings sharing such a residue do not block.
* (6) `clear_at_unit`: at `R = a` (an integer) runner `d` is clear iff `Win ((idx_d a) mod 8 + e_d a)`.
  `lonely_at_iff`, `emod_mul_odd`, `lonely_at_odd_iff`, `completeResidues_mul_odd`, `lonely_one_or_seven`
  (`R = 1` lonely iff `e_7 ≤ 0`, `R = 7` lonely iff `0 ≤ e_7`, under `|e| ≤ 1/7`), `dichotomy_example`.

Provenance (existing declarations whose argument was read and understood; no proof was copied).
* (1), (3): `RealCase.clear_shift_iff`, `RealCase.lonelyAt_gate_iff`; existing-repo counterpart: the `d_min` residue
  chain of `LRC/Cascade/*` was read for the idea only.
* (4): `RealCase.nextOpening_gate`, `RealCase.isMove_gate`, `RealCase.isMove_of_gate`.
* (6): `TwoScale.m8_residue`, `TwoScale.residue_window` (integer disparities, residue `res d a = (d a) mod 8`), of which
  `clear_at_unit` is the real-disparity form.
-/

open Classical

namespace Fresh.NormalForm

open Fresh

/-! ## The residue window and the shift lemma -/

/-- `y` is in the clear window: `y mod 8 ∈ [1, 7]`. -/
-- STANDING: DEFINITION
def Win (y : ℝ) : Prop := 1 ≤ TwoScale.m8 y ∧ TwoScale.m8 y ≤ 7

theorem win_iff_distInt (y : ℝ) : Win y ↔ (1 / 8 : ℝ) ≤ distInt (y / 8) :=
  (TwoScale.eighth_le_distInt_iff_m8 y).symm

theorem m8_of_Ico {y : ℝ} (h0 : 0 ≤ y) (h8 : y < 8) : TwoScale.m8 y = y := by
  unfold TwoScale.m8
  have : ⌊y / 8⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    constructor <;> linarith [div_nonneg h0 (by norm_num : (0 : ℝ) ≤ 8), (div_lt_one (by norm_num : (0 : ℝ) < 8)).mpr h8]
  rw [this]; simp

theorem win_of_Ico {y : ℝ} (h0 : 0 ≤ y) (h8 : y < 8) : Win y ↔ (1 ≤ y ∧ y ≤ 7) := by
  unfold Win; rw [m8_of_Ico h0 h8]

theorem win_shift (y : ℝ) (z : ℤ) : Win (y + 8 * (z : ℝ)) ↔ Win y := by
  unfold Win; rw [TwoScale.m8_add_int]

#print axioms win_iff_distInt
#print axioms m8_of_Ico
#print axioms win_of_Ico
#print axioms win_shift

/-- **Residue classes of the clear window** [L].  For an integer `r ∈ [0,8)` and `|x| ≤ 1`:
`Win (r + x)` iff `(r = 0 → 1 ≤ |x|) ∧ (r = 1 → 0 ≤ x) ∧ (r = 7 → x ≤ 0)`.  Residues `2..6` impose nothing. -/
theorem win_class (r : ℤ) (hr0 : 0 ≤ r) (hr8 : r < 8) (x : ℝ) (hx : |x| ≤ 1) :
    Win ((r : ℝ) + x) ↔ ((r = 0 → 1 ≤ |x|) ∧ (r = 1 → 0 ≤ x) ∧ (r = 7 → x ≤ 0)) := by
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  interval_cases r
  · -- r = 0
    simp only [Int.cast_zero, zero_add]
    constructor
    · intro h
      refine ⟨fun _ => ?_, fun h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩
      by_cases hx0 : 0 ≤ x
      · rw [win_of_Ico hx0 (by linarith)] at h
        rw [abs_of_nonneg hx0]; exact h.1
      · push Not at hx0
        have hh : Win (x + 8 * ((1 : ℤ) : ℝ)) := by
          rw [win_shift]; exact h
        rw [win_of_Ico (by push_cast; linarith) (by push_cast; linarith)] at hh
        push_cast at hh
        rw [abs_of_neg hx0]; linarith [hh.2]
    · rintro ⟨h0, -, -⟩
      have h1 := h0 trivial
      by_cases hx0 : 0 ≤ x
      · rw [abs_of_nonneg hx0] at h1
        rw [win_of_Ico hx0 (by linarith)]; constructor <;> linarith
      · push Not at hx0
        rw [abs_of_neg hx0] at h1
        have hh : Win (x + 8 * ((1 : ℤ) : ℝ)) := by
          rw [win_of_Ico (by push_cast; linarith) (by push_cast; linarith)]
          push_cast; constructor <;> linarith
        rwa [win_shift] at hh
  · -- r = 1
    simp only [Int.cast_one]
    constructor
    · intro h
      refine ⟨fun h => absurd h (by norm_num), fun _ => ?_, fun h => absurd h (by norm_num)⟩
      by_contra hneg
      push Not at hneg
      by_cases hb : 0 ≤ 1 + x
      · rw [win_of_Ico hb (by linarith)] at h
        linarith [h.1]
      · push Not at hb
        have hh : Win (1 + x + 8 * ((1 : ℤ) : ℝ)) := by rw [win_shift]; exact h
        rw [win_of_Ico (by push_cast; linarith) (by push_cast; linarith)] at hh
        push_cast at hh
        linarith [hh.2]
    · rintro ⟨-, h1, -⟩
      have h1' := h1 trivial
      rw [win_of_Ico (by linarith) (by linarith)]; constructor <;> linarith
  · simp only [Int.cast_ofNat]
    constructor
    · intro h; refine ⟨fun h => absurd h (by norm_num), fun h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩
    · intro _; rw [win_of_Ico (by linarith) (by linarith)]; constructor <;> linarith
  · simp only [Int.cast_ofNat]
    constructor
    · intro h; refine ⟨fun h => absurd h (by norm_num), fun h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩
    · intro _; rw [win_of_Ico (by linarith) (by linarith)]; constructor <;> linarith
  · simp only [Int.cast_ofNat]
    constructor
    · intro h; refine ⟨fun h => absurd h (by norm_num), fun h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩
    · intro _; rw [win_of_Ico (by linarith) (by linarith)]; constructor <;> linarith
  · simp only [Int.cast_ofNat]
    constructor
    · intro h; refine ⟨fun h => absurd h (by norm_num), fun h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩
    · intro _; rw [win_of_Ico (by linarith) (by linarith)]; constructor <;> linarith
  · simp only [Int.cast_ofNat]
    constructor
    · intro h; refine ⟨fun h => absurd h (by norm_num), fun h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩
    · intro _; rw [win_of_Ico (by linarith) (by linarith)]; constructor <;> linarith
  · -- r = 7
    simp only [Int.cast_ofNat]
    constructor
    · intro h
      refine ⟨fun h => absurd h (by norm_num), fun h => absurd h (by norm_num), fun _ => ?_⟩
      by_contra hpos
      push Not at hpos
      by_cases hb : 7 + x < 8
      · rw [win_of_Ico (by linarith) hb] at h
        linarith [h.2]
      · push Not at hb
        have hh : Win (7 + x + 8 * (((-1 : ℤ)) : ℝ)) := by rw [win_shift]; exact h
        rw [win_of_Ico (by push_cast; linarith) (by push_cast; linarith)] at hh
        push_cast at hh
        linarith [hh.1]
    · rintro ⟨-, -, h7⟩
      have h7' := h7 trivial
      rw [win_of_Ico (by linarith) (by linarith)]; constructor <;> linarith

#print axioms win_class

/-! ### Tightness of the window `|x| ≤ 1` (exact counterexamples) -/

/-- The slack class (residues `2..6`) fails below the window: `r = 2`, `x = -3/2` gives `1/2` [L]. -/
theorem win_mid_fails_below : ¬ Win ((2 : ℝ) + (-3 / 2)) := by
  rw [show (2 : ℝ) + (-3 / 2) = 1 / 2 by norm_num, win_of_Ico (by norm_num) (by norm_num)]
  norm_num

/-- ... and above it: `r = 6`, `x = 3/2` gives `7.5` [L]. -/
theorem win_mid_fails_above : ¬ Win ((6 : ℝ) + 3 / 2) := by
  rw [show (6 : ℝ) + 3 / 2 = 15 / 2 by norm_num, win_of_Ico (by norm_num) (by norm_num)]
  norm_num

/-- Residue `7` with `x = 2 > 0` is nevertheless clear (`9 ≡ 1`): "clear iff `x ≤ 0`" needs `x < 2` [L]. -/
theorem win_seven_clear_at_two : Win ((7 : ℝ) + 2) := by
  have := (win_shift 1 1).mp
  have h : Win ((1 : ℝ)) := by
    rw [win_of_Ico (by norm_num) (by norm_num)]; norm_num
  have e : (7 : ℝ) + 2 = 1 + 8 * ((1 : ℤ) : ℝ) := by norm_num
  rw [e, win_shift]; exact h

/-- Residue `1` with `x = -2 < 0` is nevertheless clear (`-1 ≡ 7`): "clear iff `0 ≤ x`" needs `-2 < x` [L]. -/
theorem win_one_clear_at_neg_two : Win ((1 : ℝ) + (-2)) := by
  have h : Win ((7 : ℝ)) := by
    rw [win_of_Ico (by norm_num) (by norm_num)]; norm_num
  have e : (1 : ℝ) + (-2) = 7 + 8 * ((-1 : ℤ) : ℝ) := by norm_num
  rw [e, win_shift]; exact h

/-- Residue `0` at `|x| = 1` is clear: "blocked iff `|x| < 1`" is exact at the edge [L]. -/
theorem win_zero_clear_at_one : Win ((0 : ℝ) + 1) := by
  rw [show (0 : ℝ) + 1 = 1 by norm_num, win_of_Ico (by norm_num) (by norm_num)]; norm_num

#print axioms win_mid_fails_below
#print axioms win_mid_fails_above
#print axioms win_seven_clear_at_two
#print axioms win_one_clear_at_neg_two
#print axioms win_zero_clear_at_one

/-! ## (1) Grid index and deviation -/

/-- The grid index of `d` at base `m`: the nearest integer to `ρ = d/m`.  Lean's `round` sends the tie
`ρ = k + 1/2` to `k + 1` (`idx_tie`). -/
noncomputable def idx (m d : ℝ) : ℤ := round (d / m)

/-- The deviation `e = ρ - idx ∈ [-1/2, 1/2)`. -/
noncomputable def edev (m d : ℝ) : ℝ := d / m - (idx m d : ℝ)

/-- **The reading identity** [L]: `ρ R = idx R + e R`, for every `R`. -/
theorem reading_identity (m d R : ℝ) : d / m * R = (idx m d : ℝ) * R + edev m d * R := by
  unfold edev; ring

theorem edev_ge (m d : ℝ) : -1 / 2 ≤ edev m d := by
  unfold edev idx
  rw [round_eq]
  have := Int.floor_le (d / m + 1 / 2)
  linarith

theorem edev_lt (m d : ℝ) : edev m d < 1 / 2 := by
  unfold edev idx
  rw [round_eq]
  have := Int.lt_floor_add_one (d / m + 1 / 2)
  linarith

theorem abs_edev_le (m d : ℝ) : |edev m d| ≤ 1 / 2 := by
  rw [abs_le]; exact ⟨by linarith [edev_ge m d], (edev_lt m d).le⟩

/-- **The tie rule** [L]: `ρ = k + 1/2` has `idx = k + 1` (so `e = -1/2`). -/
theorem idx_tie (m d : ℝ) (k : ℤ) (h : d / m = (k : ℝ) + 1 / 2) : idx m d = k + 1 := by
  unfold idx
  rw [round_eq, h]
  have : (k : ℝ) + 1 / 2 + 1 / 2 = ((k + 1 : ℤ) : ℝ) := by push_cast; ring
  rw [this, Int.floor_intCast]

/-- The unit reading `d = m`: `idx = 1`, `e = 0` [L]. -/
theorem idx_self {m : ℝ} (hm : 0 < m) : idx m m = 1 := by
  unfold idx; rw [div_self hm.ne']; simp

theorem edev_self {m : ℝ} (hm : 0 < m) : edev m m = 0 := by
  unfold edev; rw [idx_self hm, div_self hm.ne']; simp

#print axioms reading_identity
#print axioms edev_ge
#print axioms edev_lt
#print axioms abs_edev_le
#print axioms idx_tie
#print axioms idx_self
#print axioms edev_self

/-- **Clearness at a base point with an integer part** [L].  If `ρ R0 = N + x` with `N` an integer, runner `ρ` is
clear at `R0` (reading `ρ R0 / 8` laps) iff `Win ((N mod 8) + x)`.  Corollary of `RealCase.clear_shift_iff` at `ε = 0`,
with `δ = (N mod 8) + x`, `z = N / 8`.  No hypothesis on `ρ`, `R0`, `x`. -/
theorem clear_at (ρ R0 x : ℝ) (N : ℤ) (h : ρ * R0 = (N : ℝ) + x) :
    (1 / 8 : ℝ) ≤ distInt (ρ * R0 / 8) ↔ Win (((N % 8 : ℤ) : ℝ) + x) := by
  have hδ : ρ * R0 = 8 * ((N / 8 : ℤ) : ℝ) + (((N % 8 : ℤ) : ℝ) + x) := by
    have h1 := Int.emod_add_mul_ediv N 8
    have h2 : ((N % 8 : ℤ) : ℝ) + 8 * ((N / 8 : ℤ) : ℝ) = N := by exact_mod_cast h1
    rw [h]; linarith
  have := RealCase.clear_shift_iff ρ R0 0 _ (N / 8) hδ
  simpa [Win] using this

#print axioms clear_at

/-- **(1) At `R = 1` runner `d` is clear iff `Win (idx_d mod 8 + e_d)`** [L]. -/
theorem clear_at_one {m : ℝ} (hm : 0 < m) (d : ℝ) :
    (1 / 8 : ℝ) ≤ distInt (d * (1 / (8 * m))) ↔ Win (((idx m d % 8 : ℤ) : ℝ) + edev m d) := by
  have e : d * (1 / (8 * m)) = d / m * 1 / 8 := by
    have := RealCase.gate_reading (d := d) (m := m) (R := 1) hm
    simpa using this
  rw [e]
  exact clear_at (d / m) 1 (edev m d) (idx m d) (by unfold edev; ring)

/-- The same, as the residue of `ρ` itself: runner `d` is clear at `R = 1` iff `m8 (idx_d + e_d) ∈ [1,7]` [L]. -/
theorem clear_at_one_rho {m : ℝ} (hm : 0 < m) (d : ℝ) :
    (1 / 8 : ℝ) ≤ distInt (d * (1 / (8 * m))) ↔ Win ((idx m d : ℝ) + edev m d) := by
  have e : d * (1 / (8 * m)) = d / m * 1 / 8 := by
    have := RealCase.gate_reading (d := d) (m := m) (R := 1) hm
    simpa using this
  rw [e, mul_one, ← win_iff_distInt]
  unfold edev; ring_nf

#print axioms clear_at_one
#print axioms clear_at_one_rho

/-! ## (2), (3) Residue classes at `R = 1` and the complete residue case -/

/-- **A single runner at `R = 1`, for any integer `n` with `|ρ - n| ≤ 1`** [L]: clear iff
`(n mod 8 = 0 → 1 ≤ |ρ - n|) ∧ (n mod 8 = 1 → 0 ≤ ρ - n) ∧ (n mod 8 = 7 → ρ - n ≤ 0)`.  `n` need not be the nearest
integer: floor, ceiling, either tie rule all satisfy the hypothesis when `|ρ - n| ≤ 1`. -/
theorem clear_one_iff_n {m : ℝ} (hm : 0 < m) (d : ℝ) (n : ℤ) (hn : |d / m - n| ≤ 1) :
    (1 / 8 : ℝ) ≤ distInt (d * (1 / (8 * m))) ↔
      ((n % 8 = 0 → 1 ≤ |d / m - n|) ∧ (n % 8 = 1 → 0 ≤ d / m - n) ∧ (n % 8 = 7 → d / m - n ≤ 0)) := by
  have e : d * (1 / (8 * m)) = d / m * 1 / 8 := by
    have := RealCase.gate_reading (d := d) (m := m) (R := 1) hm
    simpa using this
  rw [e, clear_at (d / m) 1 (d / m - n) n (by ring)]
  exact win_class (n % 8) (Int.emod_nonneg _ (by norm_num)) (Int.emod_lt_of_pos _ (by norm_num)) _ hn

#print axioms clear_one_iff_n

/-- **(2) Residue classes at `R = 1` for the nearest integer** [L]: runner `d` is clear iff
`idx mod 8 ≠ 0`, and (`idx mod 8 = 1 → 0 ≤ e`), and (`idx mod 8 = 7 → e ≤ 0`).  So residues `2..6` are slack
(clear whatever `e` is), residue `7` is clear iff `e ≤ 0`, residue `1` iff `e ≥ 0`, residue `0` is blocked (always,
since `|e| ≤ 1/2 < 1`). -/
theorem clear_one_iff {m : ℝ} (hm : 0 < m) (d : ℝ) :
    (1 / 8 : ℝ) ≤ distInt (d * (1 / (8 * m))) ↔
      (idx m d % 8 ≠ 0 ∧ (idx m d % 8 = 1 → 0 ≤ edev m d) ∧ (idx m d % 8 = 7 → edev m d ≤ 0)) := by
  have hb : |d / m - (idx m d : ℝ)| ≤ 1 / 2 := abs_edev_le m d
  rw [clear_one_iff_n hm d (idx m d) (by linarith)]
  have e0 : (idx m d % 8 = 0 → 1 ≤ |d / m - (idx m d : ℝ)|) ↔ idx m d % 8 ≠ 0 :=
    ⟨fun h h0 => by have := h h0; linarith, fun h h0 => absurd h0 h⟩
  rw [e0]
  rfl

/-- Slack: residue in `2..6` is clear whatever the deviation [L]. -/
theorem clear_one_of_slack {m : ℝ} (hm : 0 < m) (d : ℝ) (h2 : 2 ≤ idx m d % 8) (h6 : idx m d % 8 ≤ 6) :
    (1 / 8 : ℝ) ≤ distInt (d * (1 / (8 * m))) :=
  (clear_one_iff hm d).mpr ⟨by omega, fun h => by omega, fun h => by omega⟩

/-- Residue `7`: clear iff `e ≤ 0` [L]. -/
theorem clear_one_r7 {m : ℝ} (hm : 0 < m) (d : ℝ) (h : idx m d % 8 = 7) :
    (1 / 8 : ℝ) ≤ distInt (d * (1 / (8 * m))) ↔ edev m d ≤ 0 := by
  rw [clear_one_iff hm d]
  exact ⟨fun h' => h'.2.2 h, fun h' => ⟨by omega, fun h1 => by omega, fun _ => h'⟩⟩

/-- Residue `1`: clear iff `0 ≤ e` [L]. -/
theorem clear_one_r1 {m : ℝ} (hm : 0 < m) (d : ℝ) (h : idx m d % 8 = 1) :
    (1 / 8 : ℝ) ≤ distInt (d * (1 / (8 * m))) ↔ 0 ≤ edev m d := by
  rw [clear_one_iff hm d]
  exact ⟨fun h' => h'.2.1 h, fun h' => ⟨by omega, fun _ => h', fun h7 => by omega⟩⟩

/-- Residue `0`: blocked, because `|e| ≤ 1/2 < 1` [L]. -/
theorem blocked_one_r0 {m : ℝ} (hm : 0 < m) (d : ℝ) (h : idx m d % 8 = 0) :
    ¬ (1 / 8 : ℝ) ≤ distInt (d * (1 / (8 * m))) := by
  rw [clear_one_iff hm d]; exact fun h' => h'.1 h

#print axioms clear_one_iff
#print axioms clear_one_of_slack
#print axioms clear_one_r7
#print axioms clear_one_r1
#print axioms blocked_one_r0

/-- **The lonely instant `R = 1`, general integer assignment** [L].  For any finite set `S` of reals (positivity NOT
used), `m > 0`, and any `n : ℝ → ℤ` with `|ρ_d - n d| ≤ 1` on `S`: `R = 1` (that is `t = 1/(8m)`) is lonely iff every
reading satisfies the residue conditions of `clear_one_iff_n`. -/
theorem lonely_one_iff_n {m : ℝ} (hm : 0 < m) (S : Finset ℝ) (n : ℝ → ℤ) (hn : ∀ d ∈ S, |d / m - n d| ≤ 1) :
    Cascade.LonelyAt S (1 / (8 * m)) ↔
      ∀ d ∈ S, ((n d % 8 = 0 → 1 ≤ |d / m - n d|) ∧ (n d % 8 = 1 → 0 ≤ d / m - n d) ∧
        (n d % 8 = 7 → d / m - n d ≤ 0)) := by
  unfold Cascade.LonelyAt
  exact forall₂_congr (fun d hd => clear_one_iff_n hm d (n d) (hn d hd))

/-- **The lonely instant `R = 1`, nearest-integer normal form** [L].  Hypotheses: `m > 0` only.  Positivity of the
disparities, `m ∈ S`, `m` least, distinctness of residues, `|e| ≤ 1/2` beyond what rounding gives: NOT REQUIRED. -/
theorem lonely_one_iff {m : ℝ} (hm : 0 < m) (S : Finset ℝ) :
    Cascade.LonelyAt S (1 / (8 * m)) ↔
      ∀ d ∈ S, (idx m d % 8 ≠ 0 ∧ (idx m d % 8 = 1 → 0 ≤ edev m d) ∧ (idx m d % 8 = 7 → edev m d ≤ 0)) := by
  unfold Cascade.LonelyAt
  exact forall₂_congr (fun d _ => clear_one_iff hm d)

#print axioms lonely_one_iff_n
#print axioms lonely_one_iff

/-- **(3) THEOREM, the complete residue case, strongest form** [L].  Let `m > 0` and `S` be any finite set of reals in
which every reading other than the unit has `idx mod 8 ∈ {2,…,7}` (that is, `2 ≤ idx mod 8`; distinctness of the
residues, the number of readings, positivity, and `m ∈ S` are NOT used).  Then `R = 1` is lonely iff every reading with
residue `7` has `e ≤ 0`. -/
theorem lonely_one_complete {m : ℝ} (hm : 0 < m) (S : Finset ℝ) (hres : ∀ d ∈ S, d = m ∨ 2 ≤ idx m d % 8) :
    Cascade.LonelyAt S (1 / (8 * m)) ↔ ∀ d ∈ S, idx m d % 8 = 7 → edev m d ≤ 0 := by
  rw [lonely_one_iff hm]
  refine forall₂_congr (fun d hd => ?_)
  rcases hres d hd with rfl | h2
  · rw [idx_self hm, edev_self hm]
    simp
  · have h8 : idx m d % 8 < 8 := Int.emod_lt_of_pos _ (by norm_num)
    exact ⟨fun h => h.2.2, fun h => ⟨by omega, fun h1 => by omega, h⟩⟩

#print axioms lonely_one_complete

/-- The unit's residue is `1`, so no unit is ever `7` [L] (used below). -/
theorem idx_self_mod {m : ℝ} (hm : 0 < m) : idx m m % 8 = 1 := by rw [idx_self hm]; norm_num

/-- The facts a complete residue pattern gives [L]: if the six readings other than the unit have `idx mod 8` taking
exactly the values `{2,…,7}` (so each once), there is a unique residue-`7` reading `d7`, every reading is the unit or has
residue `≥ 2`, and the only reading with residue `1` is the unit. -/
theorem complete_facts {m : ℝ} (hm : 0 < m) (S : Finset ℝ)
    (himg : (S.erase m).image (fun d => idx m d % 8) = ({2, 3, 4, 5, 6, 7} : Finset ℤ))
    (hcard : (S.erase m).card = 6) :
    ∃ d7 ∈ S.erase m, idx m d7 % 8 = 7 ∧ (∀ d ∈ S, idx m d % 8 = 7 → d = d7) ∧
      (∀ d ∈ S, d = m ∨ 2 ≤ idx m d % 8) ∧ (∀ d ∈ S, idx m d % 8 = 1 → d = m) := by
  have hseven : (7 : ℤ) ∈ (S.erase m).image (fun d => idx m d % 8) := by rw [himg]; decide
  obtain ⟨d7, hd7, h7⟩ := Finset.mem_image.mp hseven
  have hcardimg : ((S.erase m).image (fun d => idx m d % 8)).card = (S.erase m).card := by
    rw [himg, hcard]; decide
  have hinj : Set.InjOn (fun d => idx m d % 8) (S.erase m : Set ℝ) := Finset.card_image_iff.mp hcardimg
  have hres : ∀ d ∈ S, d = m ∨ 2 ≤ idx m d % 8 := by
    intro d hd
    by_cases hdm : d = m
    · exact Or.inl hdm
    · right
      have : idx m d % 8 ∈ (S.erase m).image (fun d => idx m d % 8) :=
        Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hdm, hd⟩)
      rw [himg] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      omega
  have huniq : ∀ d ∈ S, idx m d % 8 = 7 → d = d7 := by
    intro d hd h
    have hdm : d ≠ m := by
      rintro rfl
      have := idx_self_mod hm
      omega
    exact hinj (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hdm, hd⟩)) (Finset.mem_coe.mpr hd7) (by simp only [h, h7])
  refine ⟨d7, hd7, h7, huniq, hres, fun d hd h1 => ?_⟩
  rcases hres d hd with h | h
  · exact h
  · omega

/-- **(3) THEOREM, literal form** [L].  If the six readings other than the unit have `idx mod 8` taking exactly the
values `{2,3,4,5,6,7}` (six readings, so each once), then the residue-7 reading `d7` is unique and `R = 1` is lonely iff
`e_{d7} ≤ 0`. -/
theorem lonely_one_complete_literal {m : ℝ} (hm : 0 < m) (S : Finset ℝ)
    (himg : (S.erase m).image (fun d => idx m d % 8) = ({2, 3, 4, 5, 6, 7} : Finset ℤ))
    (hcard : (S.erase m).card = 6) :
    ∃ d7 ∈ S.erase m, idx m d7 % 8 = 7 ∧ (∀ d ∈ S, idx m d % 8 = 7 → d = d7) ∧
      (Cascade.LonelyAt S (1 / (8 * m)) ↔ edev m d7 ≤ 0) := by
  obtain ⟨d7, hd7, h7, huniq, hres, -⟩ := complete_facts hm S himg hcard
  refine ⟨d7, hd7, h7, huniq, ?_⟩
  rw [lonely_one_complete hm S hres]
  constructor
  · intro h; exact h d7 (Finset.mem_of_mem_erase hd7) h7
  · intro h d hd hd7'
    rw [huniq d hd hd7']; exact h

#print axioms complete_facts
#print axioms lonely_one_complete_literal

/-! ## (5) The incomplete case -/

/-- **(5) The blocking patterns at `R = 1`** [L].  `R = 1` is NOT lonely iff some reading has residue `0`, or residue
`1` with `e < 0`, or residue `7` with `e > 0`.  The unit (`idx = 1`, `e = 0`) never matches, so the patterns are
patterns of the readings other than the unit.  Hypotheses: `m > 0` only. -/
theorem blocked_one_iff {m : ℝ} (hm : 0 < m) (S : Finset ℝ) :
    ¬ Cascade.LonelyAt S (1 / (8 * m)) ↔
      ∃ d ∈ S, (idx m d % 8 = 0 ∨ (idx m d % 8 = 1 ∧ edev m d < 0) ∨ (idx m d % 8 = 7 ∧ 0 < edev m d)) := by
  have key : ∀ d : ℝ, (idx m d % 8 ≠ 0 ∧ (idx m d % 8 = 1 → 0 ≤ edev m d) ∧ (idx m d % 8 = 7 → edev m d ≤ 0)) ↔
      ¬ (idx m d % 8 = 0 ∨ (idx m d % 8 = 1 ∧ edev m d < 0) ∨ (idx m d % 8 = 7 ∧ 0 < edev m d)) := by
    intro d
    constructor
    · rintro ⟨h0, h1, h7⟩ (h | ⟨h, hl⟩ | ⟨h, hl⟩)
      · exact h0 h
      · exact absurd (h1 h) (not_le.mpr hl)
      · exact absurd (h7 h) (not_le.mpr hl)
    · intro h
      refine ⟨fun h0 => h (Or.inl h0), fun h1 => ?_, fun h7 => ?_⟩
      · by_contra hc; exact h (Or.inr (Or.inl ⟨h1, not_le.mp hc⟩))
      · by_contra hc; exact h (Or.inr (Or.inr ⟨h7, not_le.mp hc⟩))
  rw [lonely_one_iff hm]
  constructor
  · intro h
    by_contra hne
    apply h
    intro d hd
    exact (key d).mpr (fun hq => hne ⟨d, hd, hq⟩)
  · rintro ⟨d, hd, hq⟩ h
    exact ((key d).mp (h d hd)) hq

#print axioms blocked_one_iff

/-- **A reading with residue in `2..6` never matters** [L]: erasing it does not change whether `R = 1` is lonely.
Hence repeated residues in `2..6` cannot block. -/
theorem slack_erase {m : ℝ} (hm : 0 < m) (S : Finset ℝ) (d : ℝ) (h2 : 2 ≤ idx m d % 8) (h6 : idx m d % 8 ≤ 6) :
    Cascade.LonelyAt S (1 / (8 * m)) ↔ Cascade.LonelyAt (S.erase d) (1 / (8 * m)) := by
  constructor
  · intro h x hx
    exact h x (Finset.mem_of_mem_erase hx)
  · intro h x hx
    by_cases hxd : x = d
    · subst hxd; exact clear_one_of_slack hm x h2 h6
    · exact h x (Finset.mem_erase.mpr ⟨hxd, hx⟩)

/-- **A repeated residue alone does not block `R = 1`** [L]: two readings `d₁`, `d₂` (distinctness NOT used) of `S` with the same
residue in `2..6` contribute nothing; `R = 1` is lonely for `S` iff it is lonely for `S` with both removed. -/
theorem repeated_residue_not_blocking {m : ℝ} (hm : 0 < m) (S : Finset ℝ) (d₁ d₂ : ℝ)
    (heq : idx m d₁ % 8 = idx m d₂ % 8) (h2 : 2 ≤ idx m d₁ % 8) (h6 : idx m d₁ % 8 ≤ 6) :
    Cascade.LonelyAt S (1 / (8 * m)) ↔ Cascade.LonelyAt ((S.erase d₁).erase d₂) (1 / (8 * m)) := by
  rw [slack_erase hm S d₁ h2 h6, slack_erase hm (S.erase d₁) d₂ (by omega) (by omega)]

#print axioms slack_erase
#print axioms repeated_residue_not_blocking

/-- A concrete instance with a repeated residue: `m = 1`, `S = {1,2,3,4,5,7,10}` has `idx mod 8 = 1,2,3,4,5,7,2`
(the residue `2` is repeated by `2` and `10`) and `R = 1` is lonely [L]. -/
theorem repeated_residue_instance :
    Cascade.LonelyAt ({1, 2, 3, 4, 5, 7, 10} : Finset ℝ) (1 / (8 * 1)) := by
  rw [lonely_one_complete (by norm_num : (0 : ℝ) < 1)]
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | (intro h; exfalso; revert h; unfold idx; norm_num [round_eq]; done)
      | (intro h; unfold edev idx at *; norm_num [round_eq] at *)
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · left; rfl
    all_goals (right; unfold idx; norm_num [round_eq])

#print axioms repeated_residue_instance

/-! ## (4) The displacement: the first cascade move -/

theorem round_eq_int (y : ℝ) (c : ℤ) (h1 : (c : ℝ) - 1 / 2 ≤ y) (h2 : y < (c : ℝ) + 1 / 2) : round y = c := by
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> linarith

/-- The signed residue from a decomposition `ρ = 8 z + r + x` with `round ((r + x)/8) = c` [L]. -/
theorem sres8_eq_of {ρ x : ℝ} {z r c : ℤ} (h : ρ = 8 * (z : ℝ) + (r : ℝ) + x)
    (hc : round (((r : ℝ) + x) / 8) = c) : RealCase.sres8 ρ = (r : ℝ) + x - 8 * (c : ℝ) := by
  unfold RealCase.sres8
  have e : ρ / 8 = ((r : ℝ) + x) / 8 + (z : ℝ) := by rw [h]; ring
  rw [e, round_add_intCast, hc]
  rw [h]; push_cast; ring

/-- The decomposition of `ρ_d` used by the dev lemmas: `ρ = 8 (idx / 8) + (idx mod 8) + e`. -/
theorem rho_decomp (m d : ℝ) :
    d / m * 1 = 8 * ((idx m d / 8 : ℤ) : ℝ) + ((idx m d % 8 : ℤ) : ℝ) + edev m d := by
  have h1 := Int.emod_add_mul_ediv (idx m d) 8
  have h2 : ((idx m d % 8 : ℤ) : ℝ) + 8 * ((idx m d / 8 : ℤ) : ℝ) = (idx m d : ℝ) := by exact_mod_cast h1
  unfold edev; linarith

/-- The signed residue `dev m 1 d` of a residue-`0` reading is `e` [L]. -/
theorem dev_one_r0 (m d : ℝ) (h : idx m d % 8 = 0) : RealCase.dev m 1 d = edev m d := by
  unfold RealCase.dev
  have := sres8_eq_of (c := 0) (rho_decomp m d) (by
    rw [h]
    have := edev_ge m d; have := edev_lt m d
    apply round_eq_int <;> push_cast <;> linarith)
  rw [this, h]; simp

/-- The signed residue of a residue-`1` reading with `e < 0` is `1 + e` [L]. -/
theorem dev_one_r1 (m d : ℝ) (h : idx m d % 8 = 1) (he : edev m d < 0) : RealCase.dev m 1 d = 1 + edev m d := by
  unfold RealCase.dev
  have := sres8_eq_of (c := 0) (rho_decomp m d) (by
    rw [h]
    have := edev_ge m d
    apply round_eq_int <;> push_cast <;> linarith)
  rw [this, h]; simp

/-- The signed residue of a residue-`7` reading with `e > 0` is `e - 1` [L] (not `e`: the integer part `7` is `8 - 1`). -/
theorem dev_one_r7 (m d : ℝ) (h : idx m d % 8 = 7) (he : 0 < edev m d) : RealCase.dev m 1 d = edev m d - 1 := by
  unfold RealCase.dev
  have := sres8_eq_of (c := 1) (rho_decomp m d) (by
    rw [h]
    have := edev_lt m d
    apply round_eq_int <;> push_cast <;> linarith)
  rw [this, h]; push_cast; ring

#print axioms dev_one_r0
#print axioms dev_one_r1
#print axioms dev_one_r7

/-- **Which readings are blocked at `R = 1`, and their signed residues** [L]: `|dev| < 1` iff the reading is one of the
three blocked classes, with `dev = e` (residue `0`), `1 + e` (residue `1`, `e < 0`), `e - 1` (residue `7`, `e > 0`). -/
theorem blocked_one_class {m : ℝ} (hm : 0 < m) (d : ℝ) :
    |RealCase.dev m 1 d| < 1 ↔
      ((idx m d % 8 = 0 ∧ RealCase.dev m 1 d = edev m d) ∨
       (idx m d % 8 = 1 ∧ edev m d < 0 ∧ RealCase.dev m 1 d = 1 + edev m d) ∨
       (idx m d % 8 = 7 ∧ 0 < edev m d ∧ RealCase.dev m 1 d = edev m d - 1)) := by
  rw [← RealCase.inWay_gate_iff hm (R0 := 1) (d := d), InWay, ← not_le]
  rw [clear_one_iff hm d]
  have hb := abs_edev_le m d
  constructor
  · intro h
    have h8 : idx m d % 8 < 8 := Int.emod_lt_of_pos _ (by norm_num)
    have h0 : 0 ≤ idx m d % 8 := Int.emod_nonneg _ (by norm_num)
    by_cases hr0 : idx m d % 8 = 0
    · exact Or.inl ⟨hr0, dev_one_r0 m d hr0⟩
    by_cases hr1 : idx m d % 8 = 1
    · have : edev m d < 0 := by
        by_contra hc; push Not at hc; exact h ⟨hr0, fun _ => hc, fun h7 => by omega⟩
      exact Or.inr (Or.inl ⟨hr1, this, dev_one_r1 m d hr1 this⟩)
    by_cases hr7 : idx m d % 8 = 7
    · have : 0 < edev m d := by
        by_contra hc; push Not at hc; exact h ⟨hr0, fun h1 => by omega, fun _ => hc⟩
      exact Or.inr (Or.inr ⟨hr7, this, dev_one_r7 m d hr7 this⟩)
    exact absurd ⟨hr0, fun h1 => absurd h1 hr1, fun h7 => absurd h7 hr7⟩ h
  · rintro (⟨h0, -⟩ | ⟨h1, he, -⟩ | ⟨h7, he, -⟩) ⟨hr0, hr1, hr7⟩
    · exact hr0 h0
    · linarith [hr1 h1]
    · linarith [hr7 h7]

#print axioms blocked_one_class

/-- **(4) The first move when the residue-7 reading is the only blocked runner** [L].  Let `m > 0`, `S` positive
disparities, `d7 ∈ S` with `idx mod 8 = 7` and `e = e_{d7} > 0`, and every other reading clear at `R = 1`
(for instance residues `2..6`, or `7` with `e ≤ 0`, or `1` with `e ≥ 0`).  Then `t'` is a cascade move from
`t = 1/(8m)` iff `8 m t' = 1 + (2 - e)/ρ₇`, `ρ₇ = d7/m`.  The grid isolation at `R = 1` is displaced by exactly
`(2 - e)/ρ₇` in `R`, where the `7`-reading sits at residue `1`. -/
theorem first_move_r7 {m : ℝ} (hm : 0 < m) (S : Finset ℝ) (hpos : ∀ d ∈ S, 0 < d) (d7 : ℝ) (h7S : d7 ∈ S)
    (h7 : idx m d7 % 8 = 7) (he : 0 < edev m d7)
    (hothers : ∀ d ∈ S, d ≠ d7 → (1 / 8 : ℝ) ≤ distInt (d * (1 / (8 * m)))) (t' : ℝ) :
    IsMove S (1 / (8 * m)) t' ↔ 8 * m * t' = 1 + (2 - edev m d7) / (d7 / m) := by
  have hdev7 : RealCase.dev m 1 d7 = edev m d7 - 1 := dev_one_r7 m d7 h7 he
  have hb7 : |RealCase.dev m 1 d7| < 1 := by
    rw [hdev7, abs_lt]; constructor <;> linarith [edev_lt m d7]
  have hoff : 1 - RealCase.dev m 1 d7 = 2 - edev m d7 := by rw [hdev7]; ring
  -- every blocked runner is `d7`
  have hbl : ∀ e' ∈ S, |RealCase.dev m 1 e'| < 1 → e' = d7 := by
    intro e' he' hb
    by_contra hne
    have hw : InWay e' (1 / (8 * m)) := (RealCase.inWay_gate_iff hm).mpr hb
    exact (Cascade.not_inWay_iff.mpr (hothers e' he' hne)) hw
  constructor
  · intro hmv
    rcases RealCase.isMove_gate hpos hm hmv with ⟨hall, -⟩ | ⟨e', he', hb, ht', -⟩
    · exact absurd (hall d7 h7S) (not_le.mpr hb7)
    · have := hbl e' he' hb
      subst this
      rw [ht', hdev7]; ring
  · intro ht
    refine RealCase.isMove_of_gate hpos hm h7S hb7 (by rw [ht, hoff]) ?_
    intro e' he' hb
    rw [hbl e' he' hb]

#print axioms first_move_r7

/-- **The first move, by class** [L].  If `t'` is a cascade move from `R = 1`, then either every reading is clear and
`t'` is `1/(8m)`, or some blocked reading `e'` of class `0`, `1` or `7` has `8 m t' = 1 + off/ρ` with `off = 1 - e`
(class `0`), `-e` (class `1`, `e < 0`), `2 - e` (class `7`, `e > 0`), and `ρ = e'/m`.  The move is the maximum of these
offsets over the blocked readings (`RealCase.isMove_gate`). -/
theorem isMove_one_classes {m : ℝ} (hm : 0 < m) (S : Finset ℝ) (hpos : ∀ d ∈ S, 0 < d) (t' : ℝ)
    (hmv : IsMove S (1 / (8 * m)) t') :
    ((∀ d ∈ S, (1 / 8 : ℝ) ≤ distInt (d * (1 / (8 * m)))) ∧ t' = 1 / (8 * m)) ∨
    (∃ x ∈ S, ((idx m x % 8 = 0 ∧ 8 * m * t' = 1 + (1 - edev m x) / (x / m)) ∨
        (idx m x % 8 = 1 ∧ edev m x < 0 ∧ 8 * m * t' = 1 + (-edev m x) / (x / m)) ∨
        (idx m x % 8 = 7 ∧ 0 < edev m x ∧ 8 * m * t' = 1 + (2 - edev m x) / (x / m)))) := by
  rcases RealCase.isMove_gate hpos hm hmv with ⟨hall, ht⟩ | ⟨x, hx, hb, ht', -⟩
  · left
    refine ⟨fun d hd => ?_, ht⟩
    have := hall d hd
    by_contra hc
    have hw : InWay d (1 / (8 * m)) := not_le.mp hc
    have := (RealCase.inWay_gate_iff hm).mp hw
    linarith
  · right
    refine ⟨x, hx, ?_⟩
    rcases (blocked_one_class hm x).mp hb with ⟨h0, hd⟩ | ⟨h1, he, hd⟩ | ⟨h7, he, hd⟩
    · left; refine ⟨h0, ?_⟩; rw [ht', hd]
    · right; left; refine ⟨h1, he, ?_⟩; rw [ht', hd]; congr 2; ring
    · right; right; refine ⟨h7, he, ?_⟩; rw [ht', hd]; congr 2; ring

#print axioms isMove_one_classes

/-! ## (6) The other unit instants `R = a` -/

/-- **(6) Clearness at `R = a`** [L], `a` any integer (oddness NOT used here): runner `d` is clear at
`t = a/(8m)` iff `Win (((idx_d · a) mod 8) + e_d · a)`: the residue of `idx_d · a` and the deviation `e_d · a`. -/
theorem clear_at_unit {m : ℝ} (hm : 0 < m) (a : ℤ) (d : ℝ) :
    (1 / 8 : ℝ) ≤ distInt (d * ((a : ℝ) / (8 * m))) ↔
      Win ((((idx m d * a) % 8 : ℤ) : ℝ) + edev m d * (a : ℝ)) := by
  have e : d * ((a : ℝ) / (8 * m)) = d / m * (a : ℝ) / 8 := RealCase.gate_reading hm
  rw [e]
  exact clear_at (d / m) (a : ℝ) (edev m d * (a : ℝ)) (idx m d * a) (by push_cast; unfold edev; ring)

#print axioms clear_at_unit

/-- **(6) Residue classes at `R = a`** [L].  `a > 0` an integer; if `|e_d · a| ≤ 1` for every `d ∈ S` then `R = a` is
lonely iff every reading satisfies `(r = 0 → 1 ≤ |e a|) ∧ (r = 1 → 0 ≤ e) ∧ (r = 7 → e ≤ 0)`, `r = (idx · a) mod 8`.
The window `|e a| ≤ 1` is REQUIRED (`win_mid_fails_above`, `not_win_window_seven_example`). -/
theorem lonely_at_iff {m : ℝ} (hm : 0 < m) (S : Finset ℝ) (a : ℤ) (ha : 0 < a)
    (hw : ∀ d ∈ S, |edev m d * (a : ℝ)| ≤ 1) :
    Cascade.LonelyAt S ((a : ℝ) / (8 * m)) ↔
      ∀ d ∈ S, ((idx m d * a % 8 = 0 → 1 ≤ |edev m d * (a : ℝ)|) ∧ (idx m d * a % 8 = 1 → 0 ≤ edev m d) ∧
        (idx m d * a % 8 = 7 → edev m d ≤ 0)) := by
  have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  unfold Cascade.LonelyAt
  refine forall₂_congr (fun d hd => ?_)
  rw [clear_at_unit hm a d,
    win_class (idx m d * a % 8) (Int.emod_nonneg _ (by norm_num)) (Int.emod_lt_of_pos _ (by norm_num)) _ (hw d hd)]
  have s1 : 0 ≤ edev m d * (a : ℝ) ↔ 0 ≤ edev m d :=
    ⟨fun h => by by_contra hc; push Not at hc; nlinarith, fun h => mul_nonneg h ha'.le⟩
  have s2 : edev m d * (a : ℝ) ≤ 0 ↔ edev m d ≤ 0 :=
    ⟨fun h => by by_contra hc; push Not at hc; nlinarith, fun h => mul_nonpos_of_nonpos_of_nonneg h ha'.le⟩
  rw [s1, s2]

#print axioms lonely_at_iff

/-- The window can fail: `ρ = 23/10`, `a = 7`: `idx = 2`, `r = 14 mod 8 = 6` (slack class), `e a = 21/10 > 1`, and the
runner is blocked [L]. -/
theorem not_win_window_seven_example : ¬ Win ((6 : ℝ) + 21 / 10) := by
  rw [show (6 : ℝ) + 21 / 10 = 81 / 10 by norm_num]
  have h : ¬ Win ((81 / 10 : ℝ) + 8 * ((-1 : ℤ) : ℝ)) := by
    rw [show (81 / 10 : ℝ) + 8 * ((-1 : ℤ) : ℝ) = 1 / 10 by norm_num, win_of_Ico (by norm_num) (by norm_num)]
    norm_num
  rwa [win_shift] at h

#print axioms not_win_window_seven_example

/-- **For odd `a` the residue map is a bijection** [L]: `(i a) mod 8 = 0 ↔ i mod 8 = 0`, `= 1 ↔ i ≡ a`, `= 7 ↔ i ≡ 7a`
(mod 8).  Oddness of `a` IS used (for even `a` the first fails: `i = 4`, `a = 2`). -/
theorem emod_mul_odd (a : ℤ) (ha : a % 2 = 1) (i : ℤ) :
    (i * a % 8 = 0 ↔ i % 8 = 0) ∧ (i * a % 8 = 1 ↔ i % 8 = a % 8) ∧ (i * a % 8 = 7 ↔ i % 8 = 7 * a % 8) := by
  have hs : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
  rw [Int.mul_emod i a 8]
  rcases hs with h | h | h | h <;> rw [h] <;> omega

theorem mul_odd_emod_inj (a : ℤ) (ha : a % 2 = 1) (i i' : ℤ) : i * a % 8 = i' * a % 8 ↔ i % 8 = i' % 8 := by
  have hs : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
  rw [Int.mul_emod i a 8, Int.mul_emod i' a 8]
  rcases hs with h | h | h | h <;> rw [h] <;> omega

/-- Multiplying the indices by an odd `a` preserves a complete residue system (and its failure) [L]. -/
theorem completeResidues_mul_odd (ix : Fin 8 → ℤ) (a : ℤ) (ha : a % 2 = 1) :
    CompleteResidues (fun j => ix j * a) ↔ CompleteResidues ix := by
  unfold CompleteResidues
  constructor
  · intro h j j' hjj; exact h j j' ((mul_odd_emod_inj a ha _ _).mpr hjj)
  · intro h j j' hjj; exact h j j' ((mul_odd_emod_inj a ha _ _).mp hjj)

#print axioms emod_mul_odd
#print axioms mul_odd_emod_inj
#print axioms completeResidues_mul_odd

/-- **(6) The complete case at `R = a`, `a` odd** [L].  `a > 0` odd, `|e_d a| ≤ 1` on `S`, and no reading has
`idx ≡ 0 (mod 8)` (nothing else about the residues: not distinct, not `≥ 2`).  Then `R = a` is lonely iff the readings with
`idx ≡ a` have `e ≥ 0` and the readings with `idx ≡ 7a` have `e ≤ 0` (mod 8).  At `a = 1` this is `lonely_one_complete`'s
condition (`idx ≡ 7`: `e ≤ 0`; `idx ≡ 1`: `e ≥ 0`). -/
theorem lonely_at_odd_iff {m : ℝ} (hm : 0 < m) (S : Finset ℝ) (a : ℤ) (ha : 0 < a) (hodd : a % 2 = 1)
    (hnz : ∀ d ∈ S, idx m d % 8 ≠ 0) (hw : ∀ d ∈ S, |edev m d * (a : ℝ)| ≤ 1) :
    Cascade.LonelyAt S ((a : ℝ) / (8 * m)) ↔
      ∀ d ∈ S, ((idx m d % 8 = a % 8 → 0 ≤ edev m d) ∧ (idx m d % 8 = 7 * a % 8 → edev m d ≤ 0)) := by
  rw [lonely_at_iff hm S a ha hw]
  refine forall₂_congr (fun d hd => ?_)
  obtain ⟨h0, h1, h7⟩ := emod_mul_odd a hodd (idx m d)
  constructor
  · rintro ⟨-, c1, c7⟩
    exact ⟨fun h => c1 (h1.mpr h), fun h => c7 (h7.mpr h)⟩
  · rintro ⟨c1, c7⟩
    exact ⟨fun h => absurd (h0.mp h) (hnz d hd), fun h => c1 (h1.mp h), fun h => c7 (h7.mp h)⟩

#print axioms lonely_at_odd_iff

/-- **R = 1 and R = 7 split on the sign of the residue-7 deviation** [L].  Complete residue case (the six readings other
than the unit have `idx mod 8` exactly `{2,…,7}`) with `|e_d| ≤ 1/7` for all `d ∈ S`.  Then `R = 1` is lonely iff
`e_{d7} ≤ 0` and `R = 7` is lonely iff `0 ≤ e_{d7}`; hence one of the two is lonely, and both iff `e_{d7} = 0` (the grid).
The window `|e| ≤ 1/7` is REQUIRED for the disjunction: see `dichotomy_example`. -/
theorem lonely_one_or_seven {m : ℝ} (hm : 0 < m) (S : Finset ℝ)
    (himg : (S.erase m).image (fun d => idx m d % 8) = ({2, 3, 4, 5, 6, 7} : Finset ℤ))
    (hcard : (S.erase m).card = 6) (hw : ∀ d ∈ S, |edev m d| ≤ 1 / 7) :
    ∃ d7 ∈ S.erase m, idx m d7 % 8 = 7 ∧
      (Cascade.LonelyAt S (1 / (8 * m)) ↔ edev m d7 ≤ 0) ∧
      (Cascade.LonelyAt S (7 / (8 * m)) ↔ 0 ≤ edev m d7) := by
  obtain ⟨d7, hd7, h7, huniq, hres, hone⟩ := complete_facts hm S himg hcard
  refine ⟨d7, hd7, h7, ?_, ?_⟩
  · rw [lonely_one_complete hm S hres]
    constructor
    · intro h; exact h d7 (Finset.mem_of_mem_erase hd7) h7
    · intro h d hd hd7'
      rw [huniq d hd hd7']; exact h
  · have hw7 : ∀ d ∈ S, |edev m d * ((7 : ℤ) : ℝ)| ≤ 1 := by
      intro d hd
      have := hw d hd
      rw [abs_mul]; push_cast
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 7)]
      linarith
    have hnz : ∀ d ∈ S, idx m d % 8 ≠ 0 := by
      intro d hd
      rcases hres d hd with rfl | h
      · rw [idx_self_mod hm]; norm_num
      · omega
    have e := lonely_at_odd_iff hm S 7 (by norm_num) (by norm_num) hnz hw7
    have e7 : ((7 : ℤ) : ℝ) = 7 := by norm_num
    rw [e7] at e
    rw [e]
    constructor
    · intro h
      exact (h d7 (Finset.mem_of_mem_erase hd7)).1 (by rw [h7]; norm_num)
    · intro h d hd
      refine ⟨fun h' => ?_, fun h' => ?_⟩
      · have : idx m d % 8 = 7 := by rw [h']; norm_num
        rw [huniq d hd this]; exact h
      · have h1 : idx m d % 8 = 1 := by rw [h']; norm_num
        have := hone d hd h1
        subst this
        rw [edev_self hm]

#print axioms lonely_one_or_seven

/-- Without the window the disjunction fails [L]: `m = 1`, readings `1, 23/10, 3, 4, 5, 6, 71/10` have residues
`1,2,3,4,5,6,7`; `R = 1` is blocked by `71/10` (`e = 1/10 > 0`) and `R = 7` is blocked by `23/10` (`e = 3/10`, `7e = 21/10 > 1`). -/
theorem dichotomy_example :
    ¬ ((1 / 8 : ℝ) ≤ distInt ((71 / 10 : ℝ) * (1 / (8 * 1)))) ∧
    ¬ ((1 / 8 : ℝ) ≤ distInt ((23 / 10 : ℝ) * ((7 : ℝ) / (8 * 1)))) := by
  constructor
  · have := clear_at (71 / 10) 1 (1 / 10) 7 (by norm_num)
    rw [show (71 / 10 : ℝ) * (1 / (8 * 1)) = 71 / 10 * 1 / 8 by norm_num, this]
    rw [show (((7 : ℤ) % 8 : ℤ) : ℝ) + 1 / 10 = 71 / 10 by norm_num, win_of_Ico (by norm_num) (by norm_num)]
    norm_num
  · have := clear_at (23 / 10) 7 (1 / 10) 16 (by norm_num)
    rw [show (23 / 10 : ℝ) * ((7 : ℝ) / (8 * 1)) = 23 / 10 * 7 / 8 by norm_num, this]
    rw [show (((16 : ℤ) % 8 : ℤ) : ℝ) + 1 / 10 = 1 / 10 by norm_num, win_of_Ico (by norm_num) (by norm_num)]
    norm_num

#print axioms dichotomy_example

/-- Oddness of `a` is REQUIRED for the residue translation `emod_mul_odd` [L]: `i = 4`, `a = 2` has `i a ≡ 0` but
`i ≢ 0` (mod 8). -/
theorem emod_mul_even_fails : (4 : ℤ) * 2 % 8 = 0 ∧ (4 : ℤ) % 8 ≠ 0 := by decide

/-- **(4), the brief's example** [L]: the perturbed progression `(1,2,3,4,5,6,7+e)`, `0 < e < 1/2`, `m = 1`.  Its first
cascade move from `R = 1` lands at `8 t' = 9/(7+e)`, i.e. `R = 1 + (2-e)/(7+e) = 9/(7+e)`: the residue-`7` reading is
displaced to residue `1` (`(7+e) · 9/(7+e) = 9`). -/
theorem first_move_AP_perturbed (e : ℝ) (he0 : 0 < e) (he1 : e < 1 / 2) (t' : ℝ) :
    IsMove ({1, 2, 3, 4, 5, 6, 7 + e} : Finset ℝ) (1 / (8 * 1)) t' ↔ 8 * t' = 9 / (7 + e) := by
  have hm : (0 : ℝ) < 1 := by norm_num
  have h7 : idx 1 (7 + e) = 7 := by
    unfold idx
    apply round_eq_int <;> push_cast <;> simp <;> linarith
  have hed : edev 1 (7 + e) = e := by unfold edev; rw [h7]; push_cast; simp
  have hpos : ∀ d ∈ ({1, 2, 3, 4, 5, 6, 7 + e} : Finset ℝ), 0 < d := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> positivity
  have key := first_move_r7 hm ({1, 2, 3, 4, 5, 6, 7 + e} : Finset ℝ) hpos (7 + e) (by simp)
    (by rw [h7]; norm_num) (by rw [hed]; exact he0) ?_ t'
  · rw [key, hed]
    have hne : (7 + e) ≠ 0 := by positivity
    rw [div_one, mul_one]
    constructor
    · intro h; field_simp at h ⊢; linarith
    · intro h; field_simp at h ⊢; linarith
  · intro d hd hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    have i2 : idx 1 (2 : ℝ) = 2 := by unfold idx; norm_num [round_eq]
    have i3 : idx 1 (3 : ℝ) = 3 := by unfold idx; norm_num [round_eq]
    have i4 : idx 1 (4 : ℝ) = 4 := by unfold idx; norm_num [round_eq]
    have i5 : idx 1 (5 : ℝ) = 5 := by unfold idx; norm_num [round_eq]
    have i6 : idx 1 (6 : ℝ) = 6 := by unfold idx; norm_num [round_eq]
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (clear_one_iff hm 1).mpr ⟨by rw [idx_self hm]; norm_num, fun _ => by rw [edev_self hm],
        fun h => by rw [idx_self hm] at h; norm_num at h⟩
    · exact clear_one_of_slack hm 2 (by rw [i2]; norm_num) (by rw [i2]; norm_num)
    · exact clear_one_of_slack hm 3 (by rw [i3]; norm_num) (by rw [i3]; norm_num)
    · exact clear_one_of_slack hm 4 (by rw [i4]; norm_num) (by rw [i4]; norm_num)
    · exact clear_one_of_slack hm 5 (by rw [i5]; norm_num) (by rw [i5]; norm_num)
    · exact clear_one_of_slack hm 6 (by rw [i6]; norm_num) (by rw [i6]; norm_num)
    · exact absurd rfl hne

#print axioms emod_mul_even_fails
#print axioms first_move_AP_perturbed

end Fresh.NormalForm
