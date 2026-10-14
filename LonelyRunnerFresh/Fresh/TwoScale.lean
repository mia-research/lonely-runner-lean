import Mathlib
import Fresh.Framework
import Fresh.Boundaries
import Fresh.Cascade
import Fresh.BlockLanding

/-!
# Two scales: an integer disparity set `D = D' ∪ 8C` (Task AM)

Written 2026-10-09.  Imports `Mathlib` and the Fresh modules `Framework`, `Boundaries`, `Cascade`, `BlockLanding`
(the last only for its transitive import of `Localisation.clear_of_window`/`le_distInt_iff`; vocabulary `IsLanding`
is used in the statements of the data in `experiments/n8/two_scale_v1.py/.out`, not in this file).  Nothing is imported
from the existing `LonelyRunner` repo.  Exact reals only; the disparities are integers (a commensurable population:
test cases, NOT a reduction); no density, coverage, cap, move budget or clock is the shape of any statement.

Notation.  `s = 8 t`.  A disparity `d` reads `d s / 8` laps.  `m8 x = x - 8 ⌊x/8⌋` is the residue of `x` mod 8 in
`[0,8)`.  `d` is clear at `t = s/8` iff `m8 (d s) ∈ [1,7]`.  For `d = 8c` this reads `c s` laps: the multiples of 8
form the sub-instance `C = {c}` read at the time `s`.  Writing `s = a + η` (`a` an integer), the multiples read
`distInt (c η)`; a non-multiple reads the residue `r_d = d a mod 8` plus `d η`.

Contents.
* `m8`, `window_iff`, `eighth_le_distInt_iff_m8`: clearness in residue form.
* (1) `lonely_iff_split`, `lonely_iff_shift` [L]: the exact decomposition equivalence for `D = D' ∪ 8C`, and its form at
  `t = (a+η)/8`: lonely iff every `d ∈ D'` has `m8 (d(a+η)) ∈ [1,7]` and every `c ∈ C` has `distInt (c η) ≥ 1/8`.
* `lonely_iff_windows`, `multiple_window`, `residue_window`: every runner of `D` (multiples included, with residue
  `r = 0`) allows `η` exactly in the windows `[(8j+1-r)/d, (8j+7-r)/d]`; for `d = 8c` they are `[(k+1/8)/c, (k+7/8)/c]`.
  `residue_slack`, `residue_blocked`, `r7_blocked_small`, `r7_clear_from_two`: the one-sided critical behaviour at
  residues 1 and 7 and the slack at residues 2 to 6.
* `explicit_instant_minus`, `explicit_instant_plus`, `residue_avoid_one`, `residue_avoid_seven`, `explicit_instant`:
  an explicit lonely instant `(m ∓ η)/8` when `D'` misses the odd residue class `m` mod 8 and `C` is lonely at some
  `η ∈ (0,1)` with `d η ≤ 1` for every `d ∈ D'`.
* `Compat`, `compat_iff_exists_lonely` [L]: the compatibility statement between the sub-instance `C` and `D'`, and the
  proof that it is EXACTLY the existence of a lonely instant of `D` (an `↔`, so nothing is easier).  `CompatAll`
  is the universally quantified statement, tagged OWED.
* `tower_two` [L]: the second level of the 8-adic tower when `C` itself contains multiples of 8.
* `reading_shift_real` [L]: the real-disparity form of the reading shift.

Provenance.  `unit_lonely`/`four_cells` of `Fresh.Boundaries` (existing repo: `GrandReturnN`, the φ(8) law) give the
case `C = ∅`, where `η = 0` works for every odd `a`; the present file treats `C ≠ ∅`.  The block decomposition of
`BlockLanding` (`lonelySet_union`) is the same intersection.  Existing-repo counterparts: `LRC/Spec/DoorFlank`,
`Cascade/Iteration.lean` (read for the idea only); no proof was copied that was not understood, and every proof was
written for this file.

Counting tool: none.  Covering: none used in any proof.  Statements about the populations are in the `.out` file.
-/

open Classical

namespace Fresh.TwoScale

open Fresh

/-! ## Residue form of clearness -/

/-- The residue of `x` modulo `8`, in `[0, 8)`. -/
noncomputable def m8 (x : ℝ) : ℝ := x - 8 * (⌊x / 8⌋ : ℝ)

theorem m8_nonneg (x : ℝ) : 0 ≤ m8 x := by
  unfold m8
  have := Int.floor_le (x / 8)
  linarith

theorem m8_lt (x : ℝ) : m8 x < 8 := by
  unfold m8
  have := Int.lt_floor_add_one (x / 8)
  linarith

theorem m8_add_int (x : ℝ) (z : ℤ) : m8 (x + 8 * (z : ℝ)) = m8 x := by
  unfold m8
  have h : (x + 8 * (z : ℝ)) / 8 = x / 8 + (z : ℝ) := by ring
  rw [h, Int.floor_add_intCast]
  push_cast
  ring

#print axioms m8_add_int

/-- The window form: `m8 y ∈ [1,7]` iff `y ∈ [8j+1, 8j+7]` for some integer `j`. -/
theorem window_iff (y : ℝ) :
    (1 ≤ m8 y ∧ m8 y ≤ 7) ↔ ∃ j : ℤ, 8 * (j : ℝ) + 1 ≤ y ∧ y ≤ 8 * (j : ℝ) + 7 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⌊y / 8⌋, ?_, ?_⟩ <;> unfold m8 at h1 h2 <;> linarith
  · rintro ⟨j, h1, h2⟩
    have hf : ⌊y / 8⌋ = j := by
      rw [Int.floor_eq_iff]
      constructor <;> push_cast <;> linarith
    unfold m8
    rw [hf]
    constructor <;> linarith

#print axioms window_iff

/-- `distInt (x/8) ≥ 1/8` iff the residue of `x` mod 8 is in `[1,7]`. -/
theorem eighth_le_distInt_iff_m8 (x : ℝ) :
    (1 / 8 : ℝ) ≤ distInt (x / 8) ↔ (1 ≤ m8 x ∧ m8 x ≤ 7) := by
  rw [window_iff]
  constructor
  · intro h
    rw [Localisation.le_distInt_iff] at h
    have h0 := h ⌊x / 8⌋
    have h1 := h (⌊x / 8⌋ + 1)
    have f0 := Int.floor_le (x / 8)
    have f1 := Int.lt_floor_add_one (x / 8)
    refine ⟨⌊x / 8⌋, ?_, ?_⟩
    · rw [abs_of_nonneg (by linarith)] at h0
      linarith
    · push_cast at h1
      rw [abs_of_nonpos (by linarith)] at h1
      linarith
  · rintro ⟨j, h1, h2⟩
    apply Localisation.clear_of_window j <;> linarith

#print axioms eighth_le_distInt_iff_m8

/-! ## (1) The decomposition `D = D' ∪ 8C` -/

/-- The real disparities of the integer set `D' ∪ 8C`. -/
noncomputable def realSet (D' C : Finset ℤ) : Finset ℝ :=
  (D' ∪ C.image (fun c => 8 * c)).image (fun d : ℤ => (d : ℝ))

/-- **Decomposition** [L].  At `t = s/8` the subject is lonely for `D' ∪ 8C` iff every `d ∈ D'` has residue
`m8 (d s) ∈ [1,7]` and every `c ∈ C` has `distInt (c s) ≥ 1/8`.  (No hypothesis on `D'`: a multiple of 8 inside `D'` is
simply read by the first clause; the content of the split is the form of the second.) -/
theorem lonely_iff_split (D' C : Finset ℤ) (s : ℝ) :
    Cascade.LonelyAt (realSet D' C) (s / 8) ↔
      (∀ d ∈ D', 1 ≤ m8 ((d : ℝ) * s) ∧ m8 ((d : ℝ) * s) ≤ 7) ∧
        (∀ c ∈ C, (1 / 8 : ℝ) ≤ distInt ((c : ℝ) * s)) := by
  unfold Cascade.LonelyAt realSet
  simp only [Finset.mem_image, Finset.mem_union, forall_exists_index, and_imp]
  constructor
  · intro h
    refine ⟨fun d hd => ?_, fun c hc => ?_⟩
    · have := h (d : ℝ) d (Or.inl hd) rfl
      rw [show (d : ℝ) * (s / 8) = ((d : ℝ) * s) / 8 by ring] at this
      exact (eighth_le_distInt_iff_m8 _).mp this
    · have := h ((8 * c : ℤ) : ℝ) (8 * c) (Or.inr ⟨c, hc, rfl⟩) rfl
      rw [show ((8 * c : ℤ) : ℝ) * (s / 8) = (c : ℝ) * s by push_cast; ring] at this
      exact this
  · rintro ⟨h1, h2⟩ x d hd hx
    subst hx
    rcases hd with hd | ⟨c, hc, rfl⟩
    · rw [show (d : ℝ) * (s / 8) = ((d : ℝ) * s) / 8 by ring]
      exact (eighth_le_distInt_iff_m8 _).mpr (h1 d hd)
    · rw [show ((8 * c : ℤ) : ℝ) * (s / 8) = (c : ℝ) * s by push_cast; ring]
      exact h2 c hc

#print axioms lonely_iff_split

/-- **Decomposition at `t = (a+η)/8`** [L] (the statement asked for): lonely iff every `d ∈ D'` has
`(d (a+η)) mod 8 ∈ [1,7]` and every `c ∈ C` has `distInt (c η) ≥ 1/8`.  The multiples read the SMALLER instance `C` at
the time `η`: the whole laps `c a` drop out. -/
theorem lonely_iff_shift (D' C : Finset ℤ) (a : ℤ) (η : ℝ) :
    Cascade.LonelyAt (realSet D' C) (((a : ℝ) + η) / 8) ↔
      (∀ d ∈ D', 1 ≤ m8 ((d : ℝ) * ((a : ℝ) + η)) ∧ m8 ((d : ℝ) * ((a : ℝ) + η)) ≤ 7) ∧
        (∀ c ∈ C, (1 / 8 : ℝ) ≤ distInt ((c : ℝ) * η)) := by
  rw [lonely_iff_split]
  apply and_congr Iff.rfl
  apply forall₂_congr
  intro c _
  have : (c : ℝ) * ((a : ℝ) + η) = (c : ℝ) * η + ((c * a : ℤ) : ℝ) := by push_cast; ring
  rw [this, Cascade.distInt_add_int]

#print axioms lonely_iff_shift

/-! ## The windows: residue `r_d = d a mod 8` plus `d η` -/

/-- The residue of `d a` modulo 8 (an integer in `0..7`). -/
def res (d a : ℤ) : ℤ := (d * a) % 8

theorem res_nonneg (d a : ℤ) : 0 ≤ res d a := Int.emod_nonneg _ (by norm_num)

theorem res_lt (d a : ℤ) : res d a < 8 := Int.emod_lt_of_pos _ (by norm_num)

/-- The reading of `d` at `s = a + η` equals the reading of the residue: `m8 (d (a+η)) = m8 (r_d + d η)`. -/
theorem m8_residue (d a : ℤ) (η : ℝ) :
    m8 ((d : ℝ) * ((a : ℝ) + η)) = m8 ((res d a : ℝ) + (d : ℝ) * η) := by
  have h : (d : ℝ) * ((a : ℝ) + η) = ((res d a : ℝ) + (d : ℝ) * η) + 8 * ((d * a / 8 : ℤ) : ℝ) := by
    have e : d * a = res d a + 8 * (d * a / 8) := by
      unfold res; omega
    have e' : ((d * a : ℤ) : ℝ) = (res d a : ℝ) + 8 * ((d * a / 8 : ℤ) : ℝ) := by exact_mod_cast e
    push_cast at e' ⊢
    linarith
  rw [h, m8_add_int]

#print axioms m8_residue

/-- **The windows of one runner** [L].  The runner `d` is clear at `t = (a+η)/8` iff `d η` lies in
`[8j + 1 - r, 8j + 7 - r]` for some integer `j`, where `r = d a mod 8`. -/
theorem residue_window (d a : ℤ) (η : ℝ) :
    (1 ≤ m8 ((d : ℝ) * ((a : ℝ) + η)) ∧ m8 ((d : ℝ) * ((a : ℝ) + η)) ≤ 7) ↔
      ∃ j : ℤ, 8 * (j : ℝ) + 1 - (res d a : ℝ) ≤ (d : ℝ) * η ∧ (d : ℝ) * η ≤ 8 * (j : ℝ) + 7 - (res d a : ℝ) := by
  rw [m8_residue, window_iff]
  constructor
  · rintro ⟨j, h1, h2⟩
    exact ⟨j, by linarith, by linarith⟩
  · rintro ⟨j, h1, h2⟩
    exact ⟨j, by linarith, by linarith⟩

#print axioms residue_window

/-- **Every runner of `D` as a window** [L] (multiples of 8 included, they have residue `0`). -/
theorem lonely_iff_windows (D : Finset ℤ) (a : ℤ) (η : ℝ) :
    Cascade.LonelyAt (D.image (fun d : ℤ => (d : ℝ))) (((a : ℝ) + η) / 8) ↔
      ∀ d ∈ D, ∃ j : ℤ, 8 * (j : ℝ) + 1 - (res d a : ℝ) ≤ (d : ℝ) * η ∧
        (d : ℝ) * η ≤ 8 * (j : ℝ) + 7 - (res d a : ℝ) := by
  unfold Cascade.LonelyAt
  simp only [Finset.mem_image, forall_exists_index, and_imp]
  constructor
  · intro h d hd
    have := h (d : ℝ) d hd rfl
    rw [show (d : ℝ) * (((a : ℝ) + η) / 8) = ((d : ℝ) * ((a : ℝ) + η)) / 8 by ring,
      eighth_le_distInt_iff_m8, residue_window] at this
    exact this
  · intro h x d hd hx
    subst hx
    rw [show (d : ℝ) * (((a : ℝ) + η) / 8) = ((d : ℝ) * ((a : ℝ) + η)) / 8 by ring,
      eighth_le_distInt_iff_m8, residue_window]
    exact h d hd

#print axioms lonely_iff_windows

/-- A multiple of 8 has residue 0. -/
theorem res_eight_mul (c a : ℤ) : res (8 * c) a = 0 := by
  unfold res
  rw [show 8 * c * a = 8 * (c * a) by ring]
  exact Int.mul_emod_right _ _

/-- **The window of a multiple `d = 8c`** [L]: `η` is allowed iff `c η ∈ [k + 1/8, k + 7/8]` for some `k`. -/
theorem multiple_window (c a : ℤ) (η : ℝ) :
    (∃ j : ℤ, 8 * (j : ℝ) + 1 - (res (8 * c) a : ℝ) ≤ ((8 * c : ℤ) : ℝ) * η ∧
        ((8 * c : ℤ) : ℝ) * η ≤ 8 * (j : ℝ) + 7 - (res (8 * c) a : ℝ)) ↔
      ∃ k : ℤ, (k : ℝ) + 1 / 8 ≤ (c : ℝ) * η ∧ (c : ℝ) * η ≤ (k : ℝ) + 7 / 8 := by
  rw [res_eight_mul]
  push_cast
  constructor
  · rintro ⟨j, h1, h2⟩
    exact ⟨j, by linarith, by linarith⟩
  · rintro ⟨k, h1, h2⟩
    exact ⟨k, by linarith, by linarith⟩

#print axioms multiple_window

/-! ## The critical residues -/

/-- Slack: residue `r ∈ [1,7]`, displacement `x ∈ [0, 7-r]` stays clear (window `j = 0`). -/
theorem residue_slack (r : ℤ) (hr1 : 1 ≤ r) (hr7 : r ≤ 7) (x : ℝ) (h0 : 0 ≤ x) (hx : x ≤ 7 - (r : ℝ)) :
    1 ≤ m8 ((r : ℝ) + x) ∧ m8 ((r : ℝ) + x) ≤ 7 := by
  have : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  rw [window_iff]
  exact ⟨0, by push_cast; linarith, by push_cast; linarith⟩

#print axioms residue_slack

/-- Blocking: with `7 < r + x < 9` the runner is in the way. -/
theorem residue_blocked (y : ℝ) (h1 : 7 < y) (h2 : y < 9) : ¬ (1 ≤ m8 y ∧ m8 y ≤ 7) := by
  rw [window_iff]
  rintro ⟨j, hj1, hj2⟩
  rcases le_or_gt j 0 with hj | hj
  · have : (j : ℝ) ≤ 0 := by exact_mod_cast hj
    linarith
  · have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    linarith

#print axioms residue_blocked

/-- Residue 7: for `0 < x < 2` the runner is in the way (it stands within 1/8 of a lap line, past it). -/
theorem r7_blocked_small (x : ℝ) (h0 : 0 < x) (h2 : x < 2) :
    ¬ (1 ≤ m8 ((7 : ℝ) + x) ∧ m8 ((7 : ℝ) + x) ≤ 7) :=
  residue_blocked _ (by linarith) (by linarith)

/-- Residue 7: from `x = 2` to `x = 8` the runner is clear (the opening is at exactly `x = 2`). -/
theorem r7_clear_from_two (x : ℝ) (h0 : 2 ≤ x) (h2 : x ≤ 8) :
    1 ≤ m8 ((7 : ℝ) + x) ∧ m8 ((7 : ℝ) + x) ≤ 7 := by
  rw [window_iff]
  exact ⟨1, by push_cast; linarith, by push_cast; linarith⟩

#print axioms r7_blocked_small
#print axioms r7_clear_from_two

/-- Residue 1: for `0 ≤ x ≤ 6` the runner is clear, and it stands exactly at the opening when `x = 0`. -/
theorem r1_clear (x : ℝ) (h0 : 0 ≤ x) (h6 : x ≤ 6) :
    1 ≤ m8 ((1 : ℝ) + x) ∧ m8 ((1 : ℝ) + x) ≤ 7 := by
  rw [window_iff]
  exact ⟨0, by push_cast; linarith, by push_cast; linarith⟩

/-- Residue 1, on the negative side: for `-2 < x < 0` the runner is in the way (it is before the lap line). -/
theorem r1_blocked_small (x : ℝ) (h0 : -2 < x) (h2 : x < 0) :
    ¬ (1 ≤ m8 ((1 : ℝ) + x) ∧ m8 ((1 : ℝ) + x) ≤ 7) := by
  have := m8_add_int ((1 : ℝ) + x) 1
  have e : m8 ((1 : ℝ) + x + 8 * ((1 : ℤ) : ℝ)) = m8 ((1 : ℝ) + x) := this
  rw [← e]
  exact residue_blocked _ (by push_cast; linarith) (by push_cast; linarith)

#print axioms r1_clear
#print axioms r1_blocked_small

/-! ## An explicit lonely instant -/

/-- Residues that are not 7: the window `j = 0` contains the displacement `[0,1]`. -/
theorem window_of_nonseven (d a : ℤ) (η : ℝ) (h0 : 0 ≤ (d : ℝ) * η) (h1 : (d : ℝ) * η ≤ 1)
    (hr : res d a ≠ 7) (hr1 : 1 ≤ res d a) :
    ∃ j : ℤ, 8 * (j : ℝ) + 1 - (res d a : ℝ) ≤ (d : ℝ) * η ∧ (d : ℝ) * η ≤ 8 * (j : ℝ) + 7 - (res d a : ℝ) := by
  have h8 := res_lt d a
  have : res d a ≤ 6 := by omega
  have h' : (res d a : ℝ) ≤ 6 := by exact_mod_cast this
  have h'' : (1 : ℝ) ≤ res d a := by exact_mod_cast hr1
  exact ⟨0, by push_cast; linarith, by push_cast; linarith⟩

/-- **Explicit instant, plus side** [L].  If `a` is an integer such that every `d ∈ D'` has `d a mod 8 ∈ [1,6]`, and
`η ≥ 0` is lonely for `C` with `d η ≤ 1` for every `d ∈ D'`, then `t = (a+η)/8` is lonely for `D' ∪ 8C`. -/
theorem explicit_instant_plus (D' C : Finset ℤ) (a : ℤ) (η : ℝ) (hη : 0 ≤ η)
    (hres : ∀ d ∈ D', 1 ≤ res d a ∧ res d a ≠ 7) (hd0 : ∀ d ∈ D', 0 ≤ d) (hsmall : ∀ d ∈ D', (d : ℝ) * η ≤ 1)
    (hC : ∀ c ∈ C, (1 / 8 : ℝ) ≤ distInt ((c : ℝ) * η)) :
    Cascade.LonelyAt (realSet D' C) (((a : ℝ) + η) / 8) := by
  rw [lonely_iff_shift]
  refine ⟨fun d hd => ?_, hC⟩
  rw [residue_window]
  have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd0 d hd
  exact window_of_nonseven d a η (mul_nonneg hd' hη) (hsmall d hd) (hres d hd).2 (hres d hd).1

#print axioms explicit_instant_plus

/-- **Explicit instant, minus side** [L].  If every `d ∈ D'` has `d a mod 8 ∈ [2,7]` and `η ≥ 0` is lonely for `C` with
`d η ≤ 1`, then `t = (a-η)/8` is lonely for `D' ∪ 8C`. -/
theorem explicit_instant_minus (D' C : Finset ℤ) (a : ℤ) (η : ℝ) (hη : 0 ≤ η)
    (hres : ∀ d ∈ D', 2 ≤ res d a) (hd0 : ∀ d ∈ D', 0 ≤ d) (hsmall : ∀ d ∈ D', (d : ℝ) * η ≤ 1)
    (hC : ∀ c ∈ C, (1 / 8 : ℝ) ≤ distInt ((c : ℝ) * η)) :
    Cascade.LonelyAt (realSet D' C) (((a : ℝ) + (-η)) / 8) := by
  rw [lonely_iff_shift]
  refine ⟨fun d hd => ?_, fun c hc => ?_⟩
  · rw [residue_window]
    have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd0 d hd
    have h2 : (2 : ℝ) ≤ res d a := by exact_mod_cast hres d hd
    have h8 : (res d a : ℝ) ≤ 7 := by
      have := res_lt d a
      have : res d a ≤ 7 := by omega
      exact_mod_cast this
    have h3 := mul_nonneg hd' hη
    have h4 := hsmall d hd
    refine ⟨0, ?_, ?_⟩ <;> push_cast <;> nlinarith
  · rw [show (c : ℝ) * (-η) = -((c : ℝ) * η) by ring, Cascade.distInt_neg]
    exact hC c hc

#print axioms explicit_instant_minus

/-- Odd `m`, odd or even `d` with `d % 8 ≠ m % 8`: the residue of `d m` mod 8 is not 1 (so `m` is a good `a` on the minus
side).  Proof by the 64 residue pairs. -/
theorem residue_avoid_one (d m : ℤ) (hm : m % 2 = 1) (hne : d % 8 ≠ m % 8) : res d m ≠ 1 := by
  unfold res
  have key : ∀ x y : ℤ, 0 ≤ x → x < 8 → 0 ≤ y → y < 8 → y % 2 = 1 → x ≠ y → (x * y) % 8 ≠ 1 := by
    intro x y hx0 hx8 hy0 hy8 hy2 hxy
    interval_cases x <;> interval_cases y <;> omega
  have := key (d % 8) (m % 8) (Int.emod_nonneg _ (by norm_num)) (Int.emod_lt_of_pos _ (by norm_num))
    (Int.emod_nonneg _ (by norm_num)) (Int.emod_lt_of_pos _ (by norm_num)) (by omega) hne
  rw [Int.mul_emod]
  exact this

/-- Odd `m` with `d % 8 ≠ m % 8`: with `a = 8 - m` the residue of `d a` mod 8 is not 7 (plus side). -/
theorem residue_avoid_seven (d m : ℤ) (hm : m % 2 = 1) (hne : d % 8 ≠ m % 8) : res d (8 - m) ≠ 7 := by
  unfold res
  have key : ∀ x y : ℤ, 0 ≤ x → x < 8 → 0 ≤ y → y < 8 → y % 2 = 1 → x ≠ y → (x * ((8 - y) % 8)) % 8 ≠ 7 := by
    intro x y hx0 hx8 hy0 hy8 hy2 hxy
    interval_cases x <;> interval_cases y <;> omega
  have := key (d % 8) (m % 8) (Int.emod_nonneg _ (by norm_num)) (Int.emod_lt_of_pos _ (by norm_num))
    (Int.emod_nonneg _ (by norm_num)) (Int.emod_lt_of_pos _ (by norm_num)) (by omega) hne
  rw [Int.mul_emod, show (8 - m) % 8 = (8 - m % 8) % 8 by omega]
  exact this

#print axioms residue_avoid_one
#print axioms residue_avoid_seven

/-- An odd multiplier keeps a non-multiple of 8 off residue 0. -/
theorem residue_ne_zero (d a : ℤ) (ha : a % 2 = 1) (hd : d % 8 ≠ 0) : res d a ≠ 0 := by
  unfold res
  have key : ∀ x y : ℤ, 0 ≤ x → x < 8 → 0 ≤ y → y < 8 → y % 2 = 1 → x ≠ 0 → (x * y) % 8 ≠ 0 := by
    intro x y hx0 hx8 hy0 hy8 hy2 hx
    interval_cases x <;> interval_cases y <;> omega
  have := key (d % 8) (a % 8) (Int.emod_nonneg _ (by norm_num)) (Int.emod_lt_of_pos _ (by norm_num))
    (Int.emod_nonneg _ (by norm_num)) (Int.emod_lt_of_pos _ (by norm_num)) (by omega) hd
  rw [Int.mul_emod]
  exact this

#print axioms residue_ne_zero

/-- **The explicit regime** [L].  Let `D'` be positive integers, none a multiple of 8, missing the odd residue class `m`
mod 8 (no `d ∈ D'` has `d ≡ m`), and let `η ∈ (0,1)` be lonely for the sub-instance `C` with `d η ≤ 1` for every
`d ∈ D'`.  Then the instant `t = (m - η)/8` is lonely for `D' ∪ 8C`, and so is `t = (8 - m + η)/8`.  Both are positive.
(The hypothesis `d η ≤ 1` compares `η` with the largest element of `D'`; it is a hypothesis of the statement, not a bound
offered as an argument.) -/
theorem explicit_instant (D' C : Finset ℤ) (m : ℤ) (hm : m % 2 = 1) (hmpos : 0 < m) (hmlt : m < 8) (η : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1) (hd0 : ∀ d ∈ D', 0 < d) (hd8 : ∀ d ∈ D', d % 8 ≠ 0)
    (hmiss : ∀ d ∈ D', d % 8 ≠ m % 8) (hsmall : ∀ d ∈ D', (d : ℝ) * η ≤ 1)
    (hC : ∀ c ∈ C, (1 / 8 : ℝ) ≤ distInt ((c : ℝ) * η)) :
    (0 < (m : ℝ) - η ∧ Cascade.LonelyAt (realSet D' C) (((m : ℝ) - η) / 8)) ∧
      (0 < ((8 - m : ℤ) : ℝ) + η ∧ Cascade.LonelyAt (realSet D' C) ((((8 - m : ℤ) : ℝ) + η) / 8)) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  refine ⟨⟨by linarith, ?_⟩, ⟨?_, ?_⟩⟩
  · have := explicit_instant_minus D' C m η hη0.le
      (fun d hd => by
        have h1 : res d m ≠ 1 := residue_avoid_one d m hm (hmiss d hd)
        have h0 : res d m ≠ 0 := residue_ne_zero d m hm (hd8 d hd)
        have := res_nonneg d m
        omega)
      (fun d hd => (hd0 d hd).le) hsmall hC
    simpa [sub_eq_add_neg] using this
  · have : (1 : ℝ) ≤ ((8 - m : ℤ) : ℝ) := by
      have : (1 : ℤ) ≤ 8 - m := by omega
      exact_mod_cast this
    linarith
  · refine explicit_instant_plus D' C (8 - m) η hη0.le (fun d hd => ⟨?_, residue_avoid_seven d m hm (hmiss d hd)⟩)
      (fun d hd => (hd0 d hd).le) hsmall hC
    have h0 : res d (8 - m) ≠ 0 := residue_ne_zero d (8 - m) (by omega) (hd8 d hd)
    have := res_nonneg d (8 - m)
    omega

#print axioms explicit_instant

/-! ## Why `a = 0` fails whenever a non-multiple reads less than a lap-fraction -/

/-- At `a = 0` (so `s = η ∈ (0,1)`) a non-multiple `d` with `d η < 1` is in the way: it reads `d η / 8 < 1/8` laps.
This is why the landing of `D' ∪ 8C` is displaced past the landing `η_C` of the sub-instance whenever some `d ∈ D'`
has `d η_C < 1` [L]. -/
theorem blocked_at_zero (d : ℤ) (η : ℝ) (h0 : 0 < (d : ℝ) * η) (h1 : (d : ℝ) * η < 1) :
    ¬ ((1 : ℝ) ≤ m8 ((d : ℝ) * (((0 : ℤ) : ℝ) + η)) ∧ m8 ((d : ℝ) * (((0 : ℤ) : ℝ) + η)) ≤ 7) := by
  rw [residue_window]
  rintro ⟨j, hj1, hj2⟩
  have hr : res d 0 = 0 := by unfold res; simp
  rw [hr] at hj1 hj2
  push_cast at hj1 hj2
  rcases (by omega : j ≤ -1 ∨ j = 0 ∨ 1 ≤ j) with hj | hj | hj
  · have : (j : ℝ) ≤ -1 := by exact_mod_cast hj
    linarith
  · subst hj
    push_cast at hj1
    linarith
  · have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    linarith

#print axioms blocked_at_zero

/-- The converse at `a = 0`: if `1 ≤ d η ≤ 7` the runner `d` is clear at `s = η` [L]. -/
theorem clear_at_zero (d : ℤ) (η : ℝ) (h1 : 1 ≤ (d : ℝ) * η) (h7 : (d : ℝ) * η ≤ 7) :
    (1 : ℝ) ≤ m8 ((d : ℝ) * (((0 : ℤ) : ℝ) + η)) ∧ m8 ((d : ℝ) * (((0 : ℤ) : ℝ) + η)) ≤ 7 := by
  rw [residue_window]
  have hr : res d 0 = 0 := by unfold res; simp
  rw [hr]
  exact ⟨0, by push_cast; linarith, by push_cast; linarith⟩

#print axioms clear_at_zero

/-! ## The compatibility statement -/

/-- **Compatibility of the sub-instance `C` with `D'`** (the statement owed): there are an integer `a` and a real `η`
with `a + η > 0` such that `C` is lonely at `η` (`distInt (c η) ≥ 1/8` for every `c ∈ C`) and every `d ∈ D'` lies in one
of its residue windows `[8j+1-r_d, 8j+7-r_d]` at `d η`, `r_d = d a mod 8`. -/
-- STANDING: DEFINITION
def Compat (D' C : Finset ℤ) : Prop :=
  ∃ (a : ℤ) (η : ℝ), 0 < (a : ℝ) + η ∧
    (∀ d ∈ D', ∃ j : ℤ, 8 * (j : ℝ) + 1 - (res d a : ℝ) ≤ (d : ℝ) * η ∧
      (d : ℝ) * η ≤ 8 * (j : ℝ) + 7 - (res d a : ℝ)) ∧
    ∀ c ∈ C, (1 / 8 : ℝ) ≤ distInt ((c : ℝ) * η)

/-- **The reduction is an `↔`** [L]: `Compat D' C` is exactly the existence of a lonely instant of `D' ∪ 8C`.  A lonely
instant of `D` follows from a lonely instant of the smaller instance `C` together with the window statement on `D'`,
and conversely; nothing is made easier by the split. -/
theorem compat_iff_exists_lonely (D' C : Finset ℤ) :
    Compat D' C ↔ ∃ t : ℝ, 0 < t ∧ Cascade.LonelyAt (realSet D' C) t := by
  constructor
  · rintro ⟨a, η, hpos, hD, hC⟩
    refine ⟨((a : ℝ) + η) / 8, by positivity, ?_⟩
    rw [lonely_iff_shift]
    exact ⟨fun d hd => (residue_window d a η).mpr (hD d hd), hC⟩
  · rintro ⟨t, ht, hl⟩
    have e : t = (((⌊8 * t⌋ : ℤ) : ℝ) + (8 * t - (⌊8 * t⌋ : ℝ))) / 8 := by ring
    rw [e, lonely_iff_shift] at hl
    refine ⟨⌊8 * t⌋, 8 * t - (⌊8 * t⌋ : ℝ), by linarith, fun d hd => ?_, hl.2⟩
    exact (residue_window d _ _).mp (hl.1 d hd)

#print axioms compat_iff_exists_lonely

/-- The universally quantified compatibility statement for seven distinct positive integer disparities with `D'` free of
multiples of 8.  It is the lonely runner statement at eight runners for integer speeds (by `compat_iff_exists_lonely`),
asserted here and proved nowhere in this folder. -/
-- STANDING: OWED
def CompatAll : Prop :=
  ∀ D' C : Finset ℤ, (∀ d ∈ D', 0 < d ∧ d % 8 ≠ 0) → (∀ c ∈ C, 0 < c) → D'.card + C.card = 7 → Compat D' C

/-! ## The tower: `C` itself contains multiples of 8 -/

theorem lonelyAt_realSet_iff (D' C : Finset ℤ) (t : ℝ) :
    Cascade.LonelyAt (realSet D' C) t ↔ ∀ d ∈ D' ∪ C.image (fun c => 8 * c), (1 / 8 : ℝ) ≤ distInt ((d : ℝ) * t) := by
  unfold Cascade.LonelyAt realSet
  simp only [Finset.mem_image, forall_exists_index, and_imp]
  constructor
  · intro h d hd
    exact h (d : ℝ) d hd rfl
  · intro h x d hd hx
    subst hx
    exact h d hd

/-- **Second level of the 8-adic tower** [L].  Let `C = C₁ ∪ 8 C₂` and `η₀ = (a₁ + η₁)/8`.  Then `D' ∪ 8C` is lonely at
`(a₀ + η₀)/8` iff `D'` reads in `[1,7]` at `a₀ + η₀`, `C₁` reads in `[1,7]` at `a₁ + η₁`, and `C₂` is lonely at `η₁`:
each level is the same decomposition applied to the sub-instance. -/
theorem tower_two (D' C₁ C₂ : Finset ℤ) (a₀ a₁ : ℤ) (η₀ η₁ : ℝ) (h : η₀ = ((a₁ : ℝ) + η₁) / 8) :
    Cascade.LonelyAt (realSet D' (C₁ ∪ C₂.image (fun c => 8 * c))) (((a₀ : ℝ) + η₀) / 8) ↔
      (∀ d ∈ D', 1 ≤ m8 ((d : ℝ) * ((a₀ : ℝ) + η₀)) ∧ m8 ((d : ℝ) * ((a₀ : ℝ) + η₀)) ≤ 7) ∧
        (∀ c ∈ C₁, 1 ≤ m8 ((c : ℝ) * ((a₁ : ℝ) + η₁)) ∧ m8 ((c : ℝ) * ((a₁ : ℝ) + η₁)) ≤ 7) ∧
        (∀ e ∈ C₂, (1 / 8 : ℝ) ≤ distInt ((e : ℝ) * η₁)) := by
  rw [lonely_iff_shift]
  refine and_congr Iff.rfl ?_
  have := lonely_iff_shift C₁ C₂ a₁ η₁
  rw [← h, lonelyAt_realSet_iff] at this
  exact this

#print axioms tower_two

/-! ## Real disparities -/

/-- **Reading shift for real disparities** [L].  If a runner of (real) speed ratio `ρ` stands, at the gate coordinate
`R`, at `ρ R = 8 z + δ` with `z` an integer (the "multiple of 8" is `δ = 0`, the nearly-multiple has `δ` small), then at
`R + ε` its reading in laps is that of `(δ + ρ ε)/8`: the whole laps `z` drop out.  The integer decomposition is the
case `ρ = d`, `R = a`, `δ = r_d`. -/
theorem reading_shift_real (ρ R ε δ : ℝ) (z : ℤ) (h : ρ * R = 8 * (z : ℝ) + δ) :
    distInt (ρ * (R + ε) / 8) = distInt ((δ + ρ * ε) / 8) := by
  have e : ρ * (R + ε) / 8 = (δ + ρ * ε) / 8 + (z : ℝ) := by
    have : ρ * (R + ε) = (δ + ρ * ε) + 8 * (z : ℝ) := by linarith
    rw [this]; ring
  rw [e, Cascade.distInt_add_int]

#print axioms reading_shift_real

end Fresh.TwoScale
