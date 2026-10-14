import Mathlib
import Fresh.Framework
import Fresh.NormalForm
import Fresh.RealCase
import Fresh.TwoScale
import Fresh.Gate

/-!
# The quotient-reduced arrangement (Task BC)

Written 2026-10-09.  Imports `Mathlib` and the Fresh modules `Framework`, `NormalForm`, `RealCase`, `TwoScale`, `Gate`
only; nothing from the existing `LonelyRunner` repo.  Exact reals; no floats; no runner is stationary (the reduced
readings are proved positive, at least `1/2`).  No density, coverage, cap or move budget is the shape of any statement,
and no counting or covering step is used in any proof in this file.

Setting.  `m` is the base scale (in the application `m = d_min`), `ρ = d/m = idx + e` (`NormalForm.idx`, `NormalForm.edev`),
`R = 8 m t` the gate coordinate.  The grid index is split as `idx = ridx + 8 quo` with `ridx ∈ {1,…,8}` (so a residue-0
reading is represented by `8`, never by `0`) and `quo` an integer.  The QUOTIENT-REDUCED disparity is
`dRed = d - 8 quo m = m (ridx + e)`: the same deviation `e`, the index replaced by its representative.

Contents.
* (1) `idx_split`, `ridx_mem`, `dRed_div`, `idx_dRed`, `edev_dRed` (the reduced arrangement is its own normal form
  `(ridx, e)`), `dRed_pos` / `half_le_dRed` (positive, at least `m/2`), `dRed_unit` (the unit reading is kept).
  `reading_diff`: the readings differ by exactly `8 quo R`.  `win_orig_iff_fract`: `Win (ρR) ↔ Win (ρ~R + 8 {quo R})` (the exact
  formula at a general `R`).  `lonelyR_iff_shifted`: the lonely set of the original is the lonely condition of the reduced
  arrangement with reading `j` advanced by `8 {quo_j R}`.  `lonelyR_agree_of_int` / `lonelyR_agree_int`: they agree whenever
  every `quo_j R` is an integer, in particular at EVERY integer `R`.  `intSet_iff_gcd`: `{R : every quo_j R ∈ ℤ} = (1/g) ℤ`,
  `g = gcd quo_j`.  Examples: the agreement set is larger than that set (`agree_beyond_int_example`) and the two lonely sets
  differ at a non-integer `R` (`differ_example`).
* (2) `lonelyR_int_iff` (exact criterion at integer `R = a`, any integer `a`), `lonelyR_red_window_iff` (the residue-class form under the
  window `|e a| ≤ 1`), `lonelyR_odd_iff` (odd `a`, translated to residues of `ridx` mod 8).
* (3) `landing_le_of_int`, `landing_ge_of_int`, `landing_eq_of_both_int`, `landing_eq_of_quo_zero`, `landing_both_le_int` (landings, as least
  lonely `R > 0`), `opening_displacement` (`(R - a) ρ = 8 (z - w) - a e`), `opening_reduced`, `landing_family` (the landing of `(1,…,6,8k)` is
  `1 + 1/(8k)`: the displacement from the grid instant has no positive lower bound).
* Hypothesis tests (each by trying to drop it): `lonelyR_agree_int_any` / `lonelyR_agree_of_int_any` (`m ≠ 0` NOT required), `window_required_example`
  (window REQUIRED), `ge_one_needs_unit_example` (`m ∈ S` REQUIRED for `R ≥ 1`), `dRed_collision`, `dRed_below_unit_example` (the reduced set can
  lose distinctness and can have a member below the unit).

Provenance (existing declarations whose argument was read and understood; no proof was copied).
`NormalForm.clear_at_unit`, `NormalForm.lonely_at_iff`, `NormalForm.emod_mul_odd`, `NormalForm.win_shift` are used directly (this
repo).  The idea of a residue-and-quotient split corresponds to the `res`/`quo` data of the existing `LRC/Cascade/*` normal
form (read for the idea only).
-/

open Classical

namespace Fresh.QuotientReduction

open Fresh Fresh.NormalForm

/-! ## The reduction -/

/-- The residue representative of the grid index, in `{1,…,8}` (a residue-`0` reading is `8`, never `0`). -/
noncomputable def ridx (m d : ℝ) : ℤ := (idx m d - 1) % 8 + 1

/-- The quotient: `idx = ridx + 8 quo`. -/
noncomputable def quo (m d : ℝ) : ℤ := (idx m d - 1) / 8

/-- The quotient-reduced disparity: `d - 8 · quo · m`. -/
noncomputable def dRed (m d : ℝ) : ℝ := d - 8 * (quo m d : ℝ) * m

/-- The reduced disparity set. -/
noncomputable def redSet (m : ℝ) (S : Finset ℝ) : Finset ℝ := S.image (dRed m)

/-- The lonely predicate in the gate coordinate `R = 8 m t`. -/
-- STANDING: DEFINITION
def LonelyR (m : ℝ) (S : Finset ℝ) (R : ℝ) : Prop := Cascade.LonelyAt S (R / (8 * m))

/-- `R` is the landing of `S` at base `m`: the least `R > 0` at which `S` is lonely. -/
-- STANDING: DEFINITION
def IsLandingR (m : ℝ) (S : Finset ℝ) (R : ℝ) : Prop := IsLeast {x : ℝ | 0 < x ∧ LonelyR m S x} R

theorem idx_split (m d : ℝ) : idx m d = ridx m d + 8 * quo m d := by
  unfold ridx quo; omega

theorem ridx_ge (m d : ℝ) : 1 ≤ ridx m d := by unfold ridx; omega

theorem ridx_le (m d : ℝ) : ridx m d ≤ 8 := by unfold ridx; omega

theorem ridx_emod (m d : ℝ) : ridx m d % 8 = idx m d % 8 := by
  have := idx_split m d; omega

theorem ridx_zero_iff (m d : ℝ) : idx m d % 8 = 0 ↔ ridx m d = 8 := by
  have := ridx_ge m d; have := ridx_le m d; have := ridx_emod m d; omega

#print axioms idx_split
#print axioms ridx_ge
#print axioms ridx_le
#print axioms ridx_emod
#print axioms ridx_zero_iff

/-- **The reduced disparity in ratio form** [L]: `dRed / m = ridx + e`.  Needs `m ≠ 0` only. -/
theorem dRed_div (m d : ℝ) (hm : m ≠ 0) : dRed m d / m = (ridx m d : ℝ) + edev m d := by
  have h1 : (idx m d : ℝ) = (ridx m d : ℝ) + 8 * (quo m d : ℝ) := by exact_mod_cast idx_split m d
  have h2 : d / m = (idx m d : ℝ) + edev m d := by unfold edev; ring
  have h3 : dRed m d / m = d / m - 8 * (quo m d : ℝ) := by unfold dRed; field_simp
  rw [h3, h2, h1]; ring

theorem half_le_dRed_div (m d : ℝ) (hm : m ≠ 0) : 1 / 2 ≤ dRed m d / m := by
  rw [dRed_div m d hm]
  have := edev_ge m d
  have : (1 : ℝ) ≤ (ridx m d : ℝ) := by exact_mod_cast ridx_ge m d
  linarith

/-- **The reduced disparity is positive, at least `m/2`** [L] (`m > 0`; positivity of `d` is NOT used). -/
theorem half_le_dRed (m d : ℝ) (hm : 0 < m) : m / 2 ≤ dRed m d := by
  have h := half_le_dRed_div m d hm.ne'
  rw [le_div_iff₀ hm] at h
  linarith

theorem dRed_pos (m d : ℝ) (hm : 0 < m) : 0 < dRed m d := by
  have := half_le_dRed m d hm; linarith

/-- **The reduced arrangement is its own normal form** [L]: `idx` of the reduced disparity is `ridx` and its deviation is
the original `e`. -/
theorem idx_dRed (m d : ℝ) (hm : m ≠ 0) : idx m (dRed m d) = ridx m d := by
  unfold idx
  refine round_eq_int _ _ ?_ ?_
  · rw [dRed_div m d hm]; have := edev_ge m d; linarith
  · rw [dRed_div m d hm]; have := edev_lt m d; linarith

theorem edev_dRed (m d : ℝ) (hm : m ≠ 0) : edev m (dRed m d) = edev m d := by
  have h1 := dRed_div m d hm
  have h2 := idx_dRed m d hm
  have h3 : edev m (dRed m d) = dRed m d / m - (idx m (dRed m d) : ℝ) := rfl
  rw [h3, h2, h1]; ring

theorem quo_dRed_zero (m d : ℝ) (hm : m ≠ 0) : quo m (dRed m d) = 0 := by
  unfold quo; rw [idx_dRed m d hm]; unfold ridx; omega

theorem ridx_dRed (m d : ℝ) (hm : m ≠ 0) : ridx m (dRed m d) = ridx m d := by
  unfold ridx; rw [idx_dRed m d hm]; unfold ridx; omega

/-- **The unit reading is kept** [L]: `dRed m m = m` (so the reduced set contains `m` whenever the original does). -/
theorem dRed_unit (m : ℝ) (hm : 0 < m) : dRed m m = m := by
  have h1 : idx m m = 1 := idx_self hm
  have h2 : quo m m = 0 := by unfold quo; rw [h1]; norm_num
  unfold dRed; rw [h2]; simp

#print axioms dRed_div
#print axioms half_le_dRed_div
#print axioms half_le_dRed
#print axioms dRed_pos
#print axioms idx_dRed
#print axioms edev_dRed
#print axioms quo_dRed_zero
#print axioms ridx_dRed
#print axioms dRed_unit

/-! ## (1) The exact relation at a general `R` -/

/-- Runner `d` is clear at `R = 8 m t` iff `Win (ρ R)` [L].  Needs `m ≠ 0` only. -/
theorem clear_iff_win (m d R : ℝ) (hm : m ≠ 0) :
    (1 / 8 : ℝ) ≤ distInt (d * (R / (8 * m))) ↔ Win (d / m * R) := by
  have e : d * (R / (8 * m)) = d / m * R / 8 := by field_simp
  rw [e]; exact (win_iff_distInt _).symm

/-- **The difference of the two readings is exactly `8 quo R`** [L] (no hypothesis on `d`, `R`; `m ≠ 0`). -/
theorem reading_diff (m d R : ℝ) (hm : m ≠ 0) :
    d / m * R = dRed m d / m * R + 8 * ((quo m d : ℝ) * R) := by
  unfold dRed; field_simp; ring

/-- **The exact formula at a general `R`** [L]: the original reading is clear iff the reduced reading advanced by `8 {quo R}`
is clear, `{x}` the fractional part.  `8 ⌊quo R⌋` drops out (`win_shift`). -/
theorem win_orig_iff_fract (m d R : ℝ) (hm : m ≠ 0) :
    Win (d / m * R) ↔ Win (dRed m d / m * R + 8 * Int.fract ((quo m d : ℝ) * R)) := by
  have h := reading_diff m d R hm
  have hf := Int.floor_add_fract ((quo m d : ℝ) * R)
  have e : d / m * R = (dRed m d / m * R + 8 * Int.fract ((quo m d : ℝ) * R)) + 8 * ((⌊(quo m d : ℝ) * R⌋ : ℤ) : ℝ) := by
    rw [h]; linarith
  rw [e, win_shift]

/-- **Agreement of one runner whenever `quo R` is an integer** [L]. -/
theorem win_agree_of_int (m d R : ℝ) (hm : m ≠ 0) (n : ℤ) (h : (quo m d : ℝ) * R = n) :
    Win (d / m * R) ↔ Win (dRed m d / m * R) := by
  have e : d / m * R = dRed m d / m * R + 8 * (n : ℝ) := by rw [reading_diff m d R hm, h]
  rw [e, win_shift]

#print axioms clear_iff_win
#print axioms reading_diff
#print axioms win_orig_iff_fract
#print axioms win_agree_of_int

/-- **The lonely set of the original, through the reduced arrangement** [L]: `LonelyR m S R` iff every reduced reading,
advanced by `8 {quo_j R}`, is in the clear window.  This is the exact formula for the difference at a general `R`. -/
theorem lonelyR_iff_shifted (m : ℝ) (S : Finset ℝ) (R : ℝ) (hm : m ≠ 0) :
    LonelyR m S R ↔ ∀ d ∈ S, Win (dRed m d / m * R + 8 * Int.fract ((quo m d : ℝ) * R)) := by
  unfold LonelyR Cascade.LonelyAt
  refine forall₂_congr (fun d _ => ?_)
  rw [clear_iff_win m d R hm, win_orig_iff_fract m d R hm]

/-- The lonely set of the reduced arrangement, in residue-window form [L]. -/
theorem lonelyR_red_iff (m : ℝ) (S : Finset ℝ) (R : ℝ) (hm : m ≠ 0) :
    LonelyR m (redSet m S) R ↔ ∀ d ∈ S, Win (dRed m d / m * R) := by
  unfold LonelyR Cascade.LonelyAt redSet
  rw [Finset.forall_mem_image]
  refine forall₂_congr (fun d _ => ?_)
  rw [clear_iff_win m _ R hm]

/-- **Agreement whenever every `quo_j R` is an integer** [L].  Hypotheses: `m ≠ 0`.  No positivity, no oddness, no
distinctness, no window. -/
theorem lonelyR_agree_of_int (m : ℝ) (S : Finset ℝ) (R : ℝ) (hm : m ≠ 0)
    (h : ∀ d ∈ S, ∃ n : ℤ, (quo m d : ℝ) * R = n) : LonelyR m S R ↔ LonelyR m (redSet m S) R := by
  rw [lonelyR_red_iff m S R hm]
  unfold LonelyR Cascade.LonelyAt
  refine forall₂_congr (fun d hd => ?_)
  obtain ⟨n, hn⟩ := h d hd
  rw [clear_iff_win m d R hm, win_agree_of_int m d R hm n hn]

/-- **Agreement at every integer `R`** [L] (`quo_j` are integers, so `quo_j R` is). -/
theorem lonelyR_agree_int (m : ℝ) (S : Finset ℝ) (a : ℤ) (hm : m ≠ 0) :
    LonelyR m S (a : ℝ) ↔ LonelyR m (redSet m S) (a : ℝ) :=
  lonelyR_agree_of_int m S a hm (fun d _ => ⟨quo m d * a, by push_cast; ring⟩)

#print axioms lonelyR_iff_shifted
#print axioms lonelyR_red_iff
#print axioms lonelyR_agree_of_int
#print axioms lonelyR_agree_int

/-- `m ≠ 0` is NOT REQUIRED for the integer-`R` agreement [L]: at `m = 0` the reduction is the identity (`dRed 0 d = d`). -/
theorem lonelyR_agree_int_any (m : ℝ) (S : Finset ℝ) (a : ℤ) :
    LonelyR m S (a : ℝ) ↔ LonelyR m (redSet m S) (a : ℝ) := by
  by_cases hm : m = 0
  · subst hm
    have hid : dRed 0 = id := by funext d; simp [dRed]
    have : redSet 0 S = S := by simp [redSet, hid]
    rw [this]
  · exact lonelyR_agree_int m S a hm

#print axioms lonelyR_agree_int_any

/-- **`m ≠ 0` is not required for the general agreement either** [L]: at `m = 0` the reduction is the identity. -/
theorem lonelyR_agree_of_int_any (m : ℝ) (S : Finset ℝ) (R : ℝ)
    (h : ∀ d ∈ S, ∃ n : ℤ, (quo m d : ℝ) * R = n) : LonelyR m S R ↔ LonelyR m (redSet m S) R := by
  by_cases hm : m = 0
  · subst hm
    have hid : dRed 0 = id := by funext d; simp [dRed]
    have : redSet 0 S = S := by simp [redSet, hid]
    rw [this]
  · exact lonelyR_agree_of_int m S R hm h

#print axioms lonelyR_agree_of_int_any


/-! ### The set of `R` on which every `quo_j R` is an integer is `(1/g) ℤ` -/

theorem gcd_mul_int (f : ℝ → ℤ) (S : Finset ℝ) (R : ℝ) (h : ∀ d ∈ S, ∃ n : ℤ, (f d : ℝ) * R = n) :
    ∃ n : ℤ, ((S.gcd f : ℤ) : ℝ) * R = n := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨n1, h1⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨n2, h2⟩ := ih (fun d hd => h d (Finset.mem_insert_of_mem hd))
    rw [Finset.gcd_insert]
    have hb := Int.gcd_eq_gcd_ab (f a) (s.gcd f)
    have hc : ((GCDMonoid.gcd (f a) (s.gcd f) : ℤ) : ℝ) = ((f a : ℤ) : ℝ) * (Int.gcdA (f a) (s.gcd f) : ℝ) +
        ((s.gcd f : ℤ) : ℝ) * (Int.gcdB (f a) (s.gcd f) : ℝ) := by
      have := Int.coe_gcd (f a) (s.gcd f)
      rw [← this]
      exact_mod_cast hb
    refine ⟨n1 * Int.gcdA (f a) (s.gcd f) + n2 * Int.gcdB (f a) (s.gcd f), ?_⟩
    rw [hc]; push_cast
    rw [← h1, ← h2]; ring

/-- **The set of `R` with every `quo_j R` an integer** [L]: `{R | ∀ j, quo_j R ∈ ℤ} = {R | g R ∈ ℤ}`, `g = gcd_j quo_j`
(`g = 0`, all quotients zero, gives every `R`; otherwise `(1/g) ℤ`, which contains every integer). -/
theorem intSet_iff_gcd (m : ℝ) (S : Finset ℝ) (R : ℝ) :
    (∀ d ∈ S, ∃ n : ℤ, (quo m d : ℝ) * R = n) ↔ ∃ n : ℤ, ((S.gcd (quo m) : ℤ) : ℝ) * R = n := by
  constructor
  · exact gcd_mul_int (quo m) S R
  · rintro ⟨n, hn⟩ d hd
    obtain ⟨k, hk⟩ := Finset.gcd_dvd (f := quo m) hd
    refine ⟨k * n, ?_⟩
    have : (quo m d : ℝ) = ((S.gcd (quo m) : ℤ) : ℝ) * (k : ℝ) := by exact_mod_cast hk
    rw [this]; push_cast; rw [← hn]; ring

#print axioms gcd_mul_int
#print axioms intSet_iff_gcd

/-- **The agreement set is larger than the integrality set** [L]: `m = 1`, `d = 9` (`idx = 9`, `ridx = 1`, `quo = 1`), `R = 3/2`:
`quo R = 3/2` is not an integer, yet the original reading `13.5` and the reduced reading `1.5` are both clear. -/
theorem agree_beyond_int_example :
    (Win ((9 : ℝ) / 1 * (3 / 2)) ↔ Win (dRed 1 9 / 1 * (3 / 2))) ∧ ¬ ∃ n : ℤ, (quo 1 (9 : ℝ) : ℝ) * (3 / 2) = n := by
  have hidx : idx 1 (9 : ℝ) = 9 := by unfold idx; norm_num
  have hq : quo 1 (9 : ℝ) = 1 := by unfold quo; rw [hidx]; norm_num
  have hd : dRed 1 (9 : ℝ) = 1 := by unfold dRed; rw [hq]; norm_num
  rw [hd, hq]
  refine ⟨?_, ?_⟩
  · have h1 : Win ((9 : ℝ) / 1 * (3 / 2)) := by
      have : (9 : ℝ) / 1 * (3 / 2) = 11 / 2 + 8 * ((1 : ℤ) : ℝ) := by norm_num
      rw [this, win_shift, win_of_Ico (by norm_num) (by norm_num)]; norm_num
    have h2 : Win ((1 : ℝ) / 1 * (3 / 2)) := by
      rw [win_of_Ico (by norm_num) (by norm_num)]; norm_num
    exact ⟨fun _ => h2, fun _ => h1⟩
  · rintro ⟨n, hn⟩
    have h1 : (n : ℝ) = 3 / 2 := by push_cast at hn; linarith
    have h2 : (2 : ℝ) * n = 3 := by linarith
    have h3 : (2 : ℤ) * n = 3 := by exact_mod_cast h2
    omega

/-- **The two lonely sets differ at a non-integer `R`** [L]: `m = 1`, `S = {9}`, `R = 9/2`.  The original reading is
`40.5 ≡ 1/2 (mod 8)` (blocked); the reduced reading `4.5` is clear. -/
theorem differ_example : ¬ LonelyR 1 {(9 : ℝ)} (9 / 2) ∧ LonelyR 1 (redSet 1 {(9 : ℝ)}) (9 / 2) := by
  have hidx : idx 1 (9 : ℝ) = 9 := by unfold idx; norm_num
  have hq : quo 1 (9 : ℝ) = 1 := by unfold quo; rw [hidx]; norm_num
  have hd : dRed 1 (9 : ℝ) = 1 := by unfold dRed; rw [hq]; norm_num
  have hS : redSet 1 {(9 : ℝ)} = {1} := by simp [redSet, hd]
  rw [hS]
  unfold LonelyR Cascade.LonelyAt
  simp only [Finset.mem_singleton, forall_eq]
  rw [clear_iff_win 1 9 _ one_ne_zero, clear_iff_win 1 1 _ one_ne_zero]
  constructor
  · intro h
    have : Win ((9 : ℝ) / 1 * (9 / 2) + 8 * ((-5 : ℤ) : ℝ)) := by rw [win_shift]; exact h
    rw [win_of_Ico (by norm_num) (by norm_num)] at this
    norm_num at this
  · rw [win_of_Ico (by norm_num) (by norm_num)]; norm_num

#print axioms agree_beyond_int_example
#print axioms differ_example

/-- **The reduced set contains `m` whenever the original does, so the reduced lonely set still starts at `R ≥ 1`** [L]
(this is how `d_min` is kept: the coordinate is `R = 8 m t` with the ORIGINAL `m`; the reduced set may have a smaller own
minimum, see `dRed_below_unit_example`, but the unit reading `m` is present in it). -/
theorem lonelyR_ge_one {m : ℝ} {S : Finset ℝ} (hm : 0 < m) (hmS : m ∈ S) {R : ℝ} (hR : 0 < R) (h : LonelyR m S R) :
    1 ≤ R := by
  have h1 := h m hmS
  rw [clear_iff_win m m R hm.ne', div_self hm.ne', one_mul] at h1
  by_contra hlt
  push Not at hlt
  rw [win_of_Ico hR.le (by linarith)] at h1
  linarith [h1.1]

theorem redSet_unit {m : ℝ} {S : Finset ℝ} (hm : 0 < m) (hmS : m ∈ S) : m ∈ redSet m S := by
  unfold redSet; rw [Finset.mem_image]; exact ⟨m, hmS, dRed_unit m hm⟩

/-- The reduced set can have a member below the unit: `m = 2`, `d = 17` (`ρ = 8.5`, `idx = 9`, `e = -1/2`) reduces to `1 = m/2`
[L]. -/
theorem dRed_below_unit_example : dRed 2 (17 : ℝ) = 1 := by
  have hidx : idx 2 (17 : ℝ) = 9 := by
    unfold idx; rw [round_eq]; norm_num
  have hq : quo 2 (17 : ℝ) = 1 := by unfold quo; rw [hidx]; norm_num
  unfold dRed; rw [hq]; norm_num

/-- Distinct originals can reduce to the same disparity (the reduced arrangement need not be injective) [L]:
`m = 1`: `2` and `10` both reduce to `2`. -/
theorem dRed_collision : dRed 1 (2 : ℝ) = dRed 1 (10 : ℝ) ∧ (2 : ℝ) ≠ 10 := by
  have h2 : idx 1 (2 : ℝ) = 2 := by unfold idx; norm_num
  have h10 : idx 1 (10 : ℝ) = 10 := by unfold idx; norm_num
  have q2 : quo 1 (2 : ℝ) = 0 := by unfold quo; rw [h2]; norm_num
  have q10 : quo 1 (10 : ℝ) = 1 := by unfold quo; rw [h10]; norm_num
  refine ⟨?_, by norm_num⟩
  unfold dRed; rw [q2, q10]; norm_num

#print axioms lonelyR_ge_one
#print axioms redSet_unit
#print axioms dRed_below_unit_example
#print axioms dRed_collision

/-! ## (2) Existence on the grid instants `R = a` -/

theorem mul_emod_ridx (m d : ℝ) (a : ℤ) : idx m d * a % 8 = ridx m d * a % 8 := by
  have : idx m d * a = ridx m d * a + 8 * (quo m d * a) := by rw [idx_split m d]; ring
  rw [this]; exact Int.add_mul_emod_self_left _ _ _

/-- **The exact criterion at an integer instant `R = a`** [L].  `a` ANY integer (odd NOT used), `m > 0`; no window.  The original
is lonely at `R = a` iff every reading satisfies `Win (r + e a)`, `r = (ridx · a) mod 8`.  The criterion is the same for the
original and the reduced arrangement because `ridx ≡ idx` and `e` is unchanged. -/
theorem lonelyR_int_iff (m : ℝ) (S : Finset ℝ) (a : ℤ) (hm : 0 < m) :
    LonelyR m S (a : ℝ) ↔ ∀ d ∈ S, Win (((ridx m d * a % 8 : ℤ) : ℝ) + edev m d * (a : ℝ)) := by
  unfold LonelyR Cascade.LonelyAt
  refine forall₂_congr (fun d _ => ?_)
  rw [clear_at_unit hm a d, mul_emod_ridx]

/-- The same criterion for the reduced arrangement, computed from ITS OWN normal form `(ridx, e)` (`idx_dRed`, `edev_dRed`): a
second route to `lonelyR_agree_int` [L]. -/
theorem lonelyR_red_int_iff (m : ℝ) (S : Finset ℝ) (a : ℤ) (hm : 0 < m) :
    LonelyR m (redSet m S) (a : ℝ) ↔ ∀ d ∈ S, Win (((ridx m d * a % 8 : ℤ) : ℝ) + edev m d * (a : ℝ)) := by
  unfold LonelyR Cascade.LonelyAt redSet
  rw [Finset.forall_mem_image]
  refine forall₂_congr (fun d _ => ?_)
  rw [clear_at_unit hm a (dRed m d), idx_dRed m d hm.ne', edev_dRed m d hm.ne']

/-- **Residue-class form under the window** [L].  `a > 0` an integer (odd NOT used), `|e_j a| ≤ 1` for every `j`: the original
is lonely at `R = a` iff for every `j`, with `r = (ridx · a) mod 8`: `r = 0 → 1 ≤ |e a|`, `r = 1 → 0 ≤ e`, `r = 7 → e ≤ 0`.  The
window is REQUIRED (`NormalForm.not_win_window_seven_example`). -/
theorem lonelyR_window_iff (m : ℝ) (S : Finset ℝ) (a : ℤ) (hm : 0 < m) (ha : 0 < a)
    (hw : ∀ d ∈ S, |edev m d * (a : ℝ)| ≤ 1) :
    LonelyR m S (a : ℝ) ↔ ∀ d ∈ S, ((ridx m d * a % 8 = 0 → 1 ≤ |edev m d * (a : ℝ)|) ∧
      (ridx m d * a % 8 = 1 → 0 ≤ edev m d) ∧ (ridx m d * a % 8 = 7 → edev m d ≤ 0)) := by
  have := lonely_at_iff hm S a ha hw
  unfold LonelyR
  rw [this]
  refine forall₂_congr (fun d _ => ?_)
  rw [mul_emod_ridx]

/-- The same for the reduced arrangement [L]: its own `lonely_at_iff` with `idx = ridx`. -/
theorem lonelyR_red_window_iff (m : ℝ) (S : Finset ℝ) (a : ℤ) (hm : 0 < m) (ha : 0 < a)
    (hw : ∀ d ∈ S, |edev m d * (a : ℝ)| ≤ 1) :
    LonelyR m (redSet m S) (a : ℝ) ↔ ∀ d ∈ S, ((ridx m d * a % 8 = 0 → 1 ≤ |edev m d * (a : ℝ)|) ∧
      (ridx m d * a % 8 = 1 → 0 ≤ edev m d) ∧ (ridx m d * a % 8 = 7 → edev m d ≤ 0)) := by
  have hw' : ∀ d ∈ redSet m S, |edev m d * (a : ℝ)| ≤ 1 := by
    intro d' hd'
    unfold redSet at hd'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hd'
    rw [edev_dRed m d hm.ne']; exact hw d hd
  have := lonely_at_iff hm (redSet m S) a ha hw'
  unfold LonelyR
  rw [this]
  unfold redSet
  rw [Finset.forall_mem_image]
  refine forall₂_congr (fun d _ => ?_)
  rw [idx_dRed m d hm.ne', edev_dRed m d hm.ne']

/-- **Odd `a`, in residues of the representative `ridx ∈ {1,…,8}`** [L].  `a > 0` odd, window `|e_j a| ≤ 1`: the original is
lonely at `R = a` iff every reading with `ridx = 8` has `|e| a ≥ 1`, every reading with `ridx = a mod 8` has `e ≥ 0`, and
every reading with `ridx = 7a mod 8` has `e ≤ 0`.  Oddness is used (through `NormalForm.emod_mul_odd`) and is REQUIRED for this
translation (`NormalForm.emod_mul_even_fails`); for the criterion of `lonelyR_window_iff` it is not. -/
theorem lonelyR_odd_iff (m : ℝ) (S : Finset ℝ) (a : ℤ) (hm : 0 < m) (ha : 0 < a) (hodd : a % 2 = 1)
    (hw : ∀ d ∈ S, |edev m d * (a : ℝ)| ≤ 1) :
    LonelyR m S (a : ℝ) ↔ ∀ d ∈ S, ((ridx m d = 8 → 1 ≤ |edev m d * (a : ℝ)|) ∧
      (ridx m d = a % 8 → 0 ≤ edev m d) ∧ (ridx m d = 7 * a % 8 → edev m d ≤ 0)) := by
  rw [lonelyR_window_iff m S a hm ha hw]
  refine forall₂_congr (fun d _ => ?_)
  obtain ⟨h0, h1, h7⟩ := emod_mul_odd a hodd (ridx m d)
  have hge := ridx_ge m d
  have hle := ridx_le m d
  have hs : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
  have e0 : ridx m d * a % 8 = 0 ↔ ridx m d = 8 := by rw [h0]; omega
  have e1 : ridx m d * a % 8 = 1 ↔ ridx m d = a % 8 := by rw [h1]; omega
  have e7 : ridx m d * a % 8 = 7 ↔ ridx m d = 7 * a % 8 := by rw [h7]; omega
  rw [e0, e1, e7]

#print axioms mul_emod_ridx
#print axioms lonelyR_int_iff
#print axioms lonelyR_red_int_iff
#print axioms lonelyR_window_iff
#print axioms lonelyR_red_window_iff
#print axioms lonelyR_odd_iff

/-- The window is REQUIRED in `lonelyR_window_iff` [L]: `m = 1`, `S = {23/10}`, `a = 7`: `ridx = 2`, `e = 3/10`, `r = 14 mod 8 = 6`
(slack class, every clause holds) yet `Win (6 + 21/10)` fails, so the runner is blocked at `R = 7`. -/
theorem window_required_example :
    ¬ LonelyR 1 {(23 / 10 : ℝ)} ((7 : ℤ) : ℝ) ∧ ridx 1 (23 / 10 : ℝ) * 7 % 8 = 6 := by
  have hidx : idx 1 (23 / 10 : ℝ) = 2 := by
    unfold idx; refine round_eq_int _ _ ?_ ?_ <;> norm_num
  have hr : ridx 1 (23 / 10 : ℝ) = 2 := by unfold ridx; rw [hidx]; norm_num
  have he : edev 1 (23 / 10 : ℝ) = 3 / 10 := by unfold edev; rw [hidx]; norm_num
  refine ⟨?_, by rw [hr]; norm_num⟩
  rw [lonelyR_int_iff 1 _ 7 one_pos]
  intro h
  have h1 := h _ (Finset.mem_singleton_self _)
  rw [hr, he] at h1
  exact not_win_window_seven_example (by norm_num at h1 ⊢; exact h1)

/-- `m ∈ S` is REQUIRED for `lonelyR_ge_one` [L]: `m = 1`, `S = {2}` is lonely at `R = 1/2 < 1`. -/
theorem ge_one_needs_unit_example : LonelyR 1 {(2 : ℝ)} (1 / 2) := by
  unfold LonelyR Cascade.LonelyAt
  simp only [Finset.mem_singleton, forall_eq]
  rw [clear_iff_win 1 2 _ one_ne_zero, win_of_Ico (by norm_num) (by norm_num)]
  norm_num

#print axioms window_required_example
#print axioms ge_one_needs_unit_example


/-! ## (3) The displaced regime -/

/-- **A landing of the original at a point where every `quo_j R` is an integer bounds the reduced landing** [L]. -/
theorem landing_le_of_int {m : ℝ} {S : Finset ℝ} {Ro Rr : ℝ} (ho : IsLandingR m S Ro)
    (hr : IsLandingR m (redSet m S) Rr) (h : ∀ d ∈ S, ∃ n : ℤ, (quo m d : ℝ) * Ro = n) : Rr ≤ Ro :=
  hr.2 ⟨ho.1.1, (lonelyR_agree_of_int_any m S Ro h).mp ho.1.2⟩

/-- ... and symmetrically [L]. -/
theorem landing_ge_of_int {m : ℝ} {S : Finset ℝ} {Ro Rr : ℝ} (ho : IsLandingR m S Ro)
    (hr : IsLandingR m (redSet m S) Rr) (h : ∀ d ∈ S, ∃ n : ℤ, (quo m d : ℝ) * Rr = n) : Ro ≤ Rr :=
  ho.2 ⟨hr.1.1, (lonelyR_agree_of_int_any m S Rr h).mpr hr.1.2⟩

/-- **Both landings in the integrality set force equality** [L]. -/
theorem landing_eq_of_both_int {m : ℝ} {S : Finset ℝ} {Ro Rr : ℝ} (ho : IsLandingR m S Ro)
    (hr : IsLandingR m (redSet m S) Rr) (h1 : ∀ d ∈ S, ∃ n : ℤ, (quo m d : ℝ) * Ro = n)
    (h2 : ∀ d ∈ S, ∃ n : ℤ, (quo m d : ℝ) * Rr = n) : Ro = Rr :=
  le_antisymm (landing_ge_of_int ho hr h2) (landing_le_of_int ho hr h1)

/-- **When no reading has a quotient the two arrangements coincide and so do the landings** [L]. -/
theorem landing_eq_of_quo_zero {m : ℝ} {S : Finset ℝ} {Ro Rr : ℝ} (ho : IsLandingR m S Ro)
    (hr : IsLandingR m (redSet m S) Rr) (h : ∀ d ∈ S, quo m d = 0) : Ro = Rr :=
  landing_eq_of_both_int ho hr (fun d hd => ⟨0, by rw [h d hd]; simp⟩) (fun d hd => ⟨0, by rw [h d hd]; simp⟩)

/-- **A lonely integer instant bounds both landings** [L]: if `S` is lonely at the integer `R = a > 0` then both the original
and the reduced landing are at most `a`. -/
theorem landing_both_le_int {m : ℝ} {S : Finset ℝ} {Ro Rr : ℝ} (ho : IsLandingR m S Ro)
    (hr : IsLandingR m (redSet m S) Rr) (a : ℤ) (ha : 0 < a) (hl : LonelyR m S (a : ℝ)) :
    Ro ≤ a ∧ Rr ≤ a :=
  ⟨ho.2 ⟨by exact_mod_cast ha, hl⟩, hr.2 ⟨by exact_mod_cast ha, (lonelyR_agree_of_int_any m S a (fun d _ => ⟨quo m d * a, by push_cast; ring⟩)).mp hl⟩⟩

/-- **The displacement of an opening from a grid instant is the deviation term** [L].  If the flank `ρ = idx + e` has an opening
at `R` (`R ρ = 8 z + 1`) and `a` is a grid instant for it (`a · idx = 8 w + 1`, i.e. `a ≡ idx⁻¹ mod 8`), then
`(R - a) ρ = 8 (z - w) - a e`: on the same lap (`z = w`) the opening is the grid instant displaced by `-a e / ρ`. -/
theorem opening_displacement (R a ρ ix e : ℝ) (z w : ℤ) (hρ : ρ = ix + e) (hz : R * ρ = 8 * (z : ℝ) + 1)
    (hw : a * ix = 8 * (w : ℝ) + 1) : (R - a) * ρ = 8 * ((z : ℝ) - (w : ℝ)) - a * e := by
  subst hρ
  linear_combination hz - hw

/-- **An original opening is a reduced reading `8 {…}` off an opening** [L]: `R ρ = 8 z + 1` and `ρ = ρ~ + 8 q` give
`R ρ~ = 8 (z - q R) + 1`: the reduced reading is at an opening lap shifted by the REAL number `q R` (an integer exactly when
the quotient correction vanishes). -/
theorem opening_reduced (R ρ ρt q : ℝ) (z : ℤ) (hρ : ρ = ρt + 8 * q) (hz : R * ρ = 8 * (z : ℝ) + 1) :
    R * ρt = 8 * ((z : ℝ) - q * R) + 1 := by
  subst hρ
  linear_combination hz

#print axioms landing_le_of_int
#print axioms landing_ge_of_int
#print axioms landing_eq_of_both_int
#print axioms landing_eq_of_quo_zero
#print axioms landing_both_le_int
#print axioms opening_displacement
#print axioms opening_reduced

/-! ### An infinite family: the displacement from the grid instant has no positive lower bound -/

/-- **The landing of `(1,2,3,4,5,6,8k)` is `1 + 1/(8k)`** [L], every `k ≥ 1`.  The reading `8k` has residue `0` and `e = 0`, so it is in
the way at `R = 1` (`|8k R - 8k| < 1` for `R < 1 + 1/(8k)`) and it is the only runner that is; its opening is `(8k+1)/(8k)`.  So the
displacement from the grid instant `a = 1` is `1/(8k)`, which has no positive lower bound over arrangements (its grid part is
`Ngrid = 8z + 1 - a·idx = 8k + 1 - 8k = 1`, its deviation part `-a e = 0`). -/
theorem landing_family (k : ℕ) (hk : 1 ≤ k) :
    IsLandingR 1 ({1, 2, 3, 4, 5, 6, 8 * (k : ℝ)} : Finset ℝ) (1 + 1 / (8 * (k : ℝ))) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < 8 * (k : ℝ) := by linarith
  have hsmall : 1 / (8 * (k : ℝ)) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ hkpos (by norm_num)]; linarith
  have hpos : 0 < 1 / (8 * (k : ℝ)) := by positivity
  refine ⟨⟨by linarith, ?_⟩, ?_⟩
  · unfold LonelyR Cascade.LonelyAt
    intro d hd
    rw [clear_iff_win 1 d _ one_ne_zero]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [div_one, win_of_Ico (by linarith) (by linarith)]; constructor <;> linarith
    · rw [div_one, win_of_Ico (by linarith) (by linarith)]
      constructor <;> nlinarith
    · rw [div_one, win_of_Ico (by linarith) (by nlinarith)]
      constructor <;> nlinarith
    · rw [div_one, win_of_Ico (by linarith) (by nlinarith)]
      constructor <;> nlinarith
    · rw [div_one, win_of_Ico (by linarith) (by nlinarith)]
      constructor <;> nlinarith
    · rw [div_one, win_of_Ico (by linarith) (by nlinarith)]
      constructor <;> nlinarith
    · have e : 8 * (k : ℝ) / 1 * (1 + 1 / (8 * (k : ℝ))) = 1 + 8 * ((k : ℤ) : ℝ) := by
        push_cast; field_simp; ring
      rw [e, win_shift, win_of_Ico (by norm_num) (by norm_num)]; norm_num
  · rintro x ⟨hx, hl⟩
    have hmem : (1 : ℝ) ∈ ({1, 2, 3, 4, 5, 6, 8 * (k : ℝ)} : Finset ℝ) := by simp
    have h1 : 1 ≤ x := lonelyR_ge_one one_pos hmem hx hl
    by_contra hlt
    push Not at hlt
    have hmem2 : 8 * (k : ℝ) ∈ ({1, 2, 3, 4, 5, 6, 8 * (k : ℝ)} : Finset ℝ) := by simp
    have h2 := hl _ hmem2
    rw [clear_iff_win 1 _ _ one_ne_zero, div_one] at h2
    have e : 8 * (k : ℝ) * x = (8 * (k : ℝ) * (x - 1)) + 8 * ((k : ℤ) : ℝ) := by push_cast; ring
    rw [e, win_shift, win_of_Ico (by nlinarith) (by
      have : 8 * (k : ℝ) * (x - 1) < 1 := by
        have := mul_lt_mul_of_pos_left (show x - 1 < 1 / (8 * (k : ℝ)) by linarith) hkpos
        rwa [mul_one_div_cancel hkpos.ne'] at this
      linarith)] at h2
    have : 8 * (k : ℝ) * (x - 1) < 1 := by
      have := mul_lt_mul_of_pos_left (show x - 1 < 1 / (8 * (k : ℝ)) by linarith) hkpos
      rwa [mul_one_div_cancel hkpos.ne'] at this
    linarith [h2.1]

#print axioms landing_family

end Fresh.QuotientReduction
