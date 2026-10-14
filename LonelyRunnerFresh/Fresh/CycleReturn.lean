import Mathlib
import Fresh.Framework
import Fresh.Cascade
import Fresh.Grid
import Fresh.DMax
import Fresh.Dilation
import Fresh.OneMultiple
import Fresh.Types

/-!
# The cycle, the grand return, and the four isolations of the AP (Task CE)

Written 2026-10-10.  Imports Mathlib and the Fresh modules `Framework`, `Cascade`, `Grid`, `DMax`, `Dilation`,
`OneMultiple`, `Types` only.  Nothing is imported from the existing `LonelyRunner` repo.  Exact reals; no floats; no
runner is stationary (every disparity is a positive difference from a subject of speed `s > 0`; the AP is
`{s, 2s, …, 7s}` with `s > 0`).

Owner's words (verbatim, the objects this file states natively):
* "We do have a cycle based on the full rotation of the slowest speed."
* "Our phi (n) law proves the existence of a global isolation for AP, arithmetic progression showing global isolation
  happens 4 times before a grand return.  AP isolation is scale invariant - 0.000001...0.00008 act the same as 1...8,
  the same as 1pi...8pi the same as 1m...8m."
* "A grand return is when all runners reach the starting point at the same time, hence starting the cycle again with no
  new information or new outcomes possible as it becomes a repeating pattern.  All integer patterns have a grand return."

Contents (each theorem is graded in the task report).
* (1) CYCLE.  `cycle m = [0, 1/m]`.  `cycle_slowest_range`, `cycle_slowest_clear` (the slowest reading's clear set over
  the cycle is `[1/(8m), 7/(8m)]`, i.e. `R = 8mt ∈ [1,7]`), `lonely_cycle_window` (any lonely instant of the cycle lies
  there), `clear_iff_window` (the window form of any reading), `cycle_image_other` (reading `d` runs through `[0, d/m]`,
  at least one whole lap), `returns_at_cycle_end_iff`, `cycle_is_grandReturn_iff` (the cycle is a grand return iff the
  slowest reading divides every disparity), `cycle_not_grandReturn_example`.
* (2) GRAND RETURN.  `GrandReturn ds T`.  `lonelyAt_add_of_return`, `lonelyAt_add_int_mul`, `lonelyAt_sub_of_return`,
  `lonelySet_add_period`, `lonelySet_mirror` (period `T` and mirror `t ↦ T − t` as lonely-set equalities),
  `grandReturn_one_of_int`, `int_lonely_shift_of_return` (the `T = 1` instance, the statement of `Types.int_lonely_shift`),
  `gcd_mul_int`, `grandReturn_ofInts_iff`, `grandReturn_ofInts_isLeast` (least grand return `1/gcd`),
  `ratio_rational_of_return`, `return_of_ratio_rational`, `exists_grandReturn_iff` (a grand return exists iff the
  disparities are pairwise commensurable), `sqrt2_no_grandReturn`, `sqrt2_lonely_no_return_cascade_fixes` (the
  cascade does not need a grand return).
* (3) THE AP.  `apDisp s`; `lonelyAt_apDisp_iff` (from `OneMultiple.ap7_lonely_iff`); `lonely_apDisp_cycle` (the lonely
  instants of one grand return `[0, 1/s]` are exactly `k/(8s)`, `k ∈ {1,3,5,7}`); `card_apInstants` (their number is
  `Nat.totient 8`); `ap_global_iff` (from `Grid.ap_globalIsolation_iff`: global isolation of the eight runners is the
  same set of instants); `touch_readings` (zero margin: exactly two readings, `j s` and `(8 − j) s`, stand at an edge);
  `no_lonely_between` (nothing lonely between them).
* (4) SCALE.  `lonelyAt_scale`, `lonelySet_apDisp_scale`, `apInstants_scale`, the cascade commutes with the dilation
  (`isMove_scale`, `cascadeFixes_scale`); instances at `s = π`, `s = 1/12500`, `s = m`.
* (5) D_MAX.  `complete_iff_odd`: the eight indices `j·a` form a complete residue system iff `a` is odd; the four instants
  are the `a ∈ [0,8]` where this holds (`four_instants_complete_residue`); `dmax_four_instants` (a D_max shift keeps the
  four instants).

Counting tools, tagged at the step: **[PROVISIONAL: counting tool]** `card_apInstants` (number of instants equals the
number of residues coprime to 8, the definition of `Nat.totient`; supports the claim "four isolations per grand
return", not a shape of any result), `exists_grandReturn_iff` (the product of denominators, supports "a common return
exists").  No covering, density, cap or move budget appears in any statement.

Provenance (existing declarations whose argument was read and understood; no proof was copied).  Existing repo:
`LRC/Spec/GrandReturnN`-style totient law and `Spec/DoorFlank` were read for the idea only.  In this folder:
`Types.int_lonely_shift` (T = 1 instance; `Types.first_window_of_small_dmin` and `Types.no_crossing_of_small_dmin` use
exactly the period-`1` and mirror `t ↦ k − t` symmetries, so those two rest on the case `T = 1` of
`lonelyAt_add_of_return` / `lonelyAt_sub_of_return`), `OneMultiple.ap7_lonely_iff`, `Grid.ap_globalIsolation_iff`,
`Grid.grid_extra_instant`, `dmax_complete`, `dmax_globalIsolation`, `Dilation.reading_dilation`.  The earlier
`Fresh/Cycle.lean` (Task X) was not imported; its `ap18_four_before_return` is the `s = 1` case of `lonely_apDisp_cycle`.
-/

open Classical

namespace Fresh

namespace CycleReturn

/-! ## Arithmetic of the clear window -/

/-- A reading is clear (`distInt ≥ 1/8`) iff it lies in a window `[z + 1/8, z + 7/8]` between two lap lines. -/
theorem clear_iff_window (x : ℝ) :
    (1 / 8 : ℝ) ≤ distInt x ↔ ∃ z : ℤ, (z : ℝ) + 1 / 8 ≤ x ∧ x ≤ (z : ℝ) + 7 / 8 := by
  constructor
  · intro h
    have hf := (Localisation.clear_iff_fract x).mp h
    refine ⟨⌊x⌋, ?_, ?_⟩ <;> unfold Int.fract at hf <;> linarith [hf.1, hf.2]
  · rintro ⟨z, h1, h2⟩
    exact Localisation.clear_of_window z h1 h2

#print axioms clear_iff_window

/-- `distInt x = 0` iff `x` is a whole number. -/
theorem distInt_eq_zero_iff (x : ℝ) : distInt x = 0 ↔ ∃ z : ℤ, x = z := by
  constructor
  · intro h
    refine ⟨round x, ?_⟩
    unfold distInt at h
    have := abs_eq_zero.mp h
    linarith
  · rintro ⟨z, rfl⟩
    exact Localisation.distInt_intCast z

#print axioms distInt_eq_zero_iff

/-! ## (1) The cycle of the slowest reading -/

/-- The cycle: one full rotation of the slowest reading `m`, the instants `[0, 1/m]`. -/
def cycle (m : ℝ) : Set ℝ := Set.Icc 0 (1 / m)

/-- The set of instants at which `ds` is lonely. -/
def lonelySet (ds : Finset ℝ) : Set ℝ := {t | Cascade.LonelyAt ds t}

/-- **The slowest reading runs once through `[0, 1]` over the cycle.** -/
theorem cycle_slowest_range {m : ℝ} (hm : 0 < m) :
    (fun t => m * t) '' cycle m = Set.Icc 0 1 := by
  ext u
  constructor
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
    refine ⟨by positivity, ?_⟩
    rw [le_div_iff₀ hm] at h1
    linarith
  · rintro ⟨h0, h1⟩
    refine ⟨u / m, ⟨by positivity, ?_⟩, by field_simp⟩
    rw [div_le_div_iff_of_pos_right hm]
    exact h1

#print axioms cycle_slowest_range

/-- **The clear set of the slowest reading over the cycle is `[1/(8m), 7/(8m)]`** (in `R = 8mt`: `[1, 7]`).
Over `[0, 1/m]` the reading is `m t ∈ [0, 1]`, and a reading in `[0,1]` is clear iff it lies in `[1/8, 7/8]`. -/
theorem cycle_slowest_clear {m : ℝ} (hm : 0 < m) {t : ℝ} (ht : t ∈ cycle m) :
    (1 / 8 : ℝ) ≤ distInt (m * t) ↔ 1 / (8 * m) ≤ t ∧ t ≤ 7 / (8 * m) := by
  obtain ⟨h0, h1⟩ := ht
  have hx0 : 0 ≤ m * t := by positivity
  have hx1 : m * t ≤ 1 := by
    rw [le_div_iff₀ hm] at h1
    linarith
  have e1 : 1 / (8 * m) ≤ t ↔ 1 / 8 ≤ m * t := by
    rw [div_le_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith
  have e2 : t ≤ 7 / (8 * m) ↔ m * t ≤ 7 / 8 := by
    rw [le_div_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith
  rw [e1, e2, clear_iff_window]
  constructor
  · rintro ⟨z, hz1, hz2⟩
    have hz0 : z = 0 := by
      have a1 : (z : ℝ) < 1 := by linarith
      have a2 : (-1 : ℝ) < z := by linarith
      have b1 : z < 1 := by exact_mod_cast a1
      have b2 : -1 < z := by exact_mod_cast a2
      omega
    subst hz0
    simp only [Int.cast_zero, zero_add] at hz1 hz2
    exact ⟨hz1, hz2⟩
  · rintro ⟨a, b⟩
    exact ⟨0, by simpa using a, by simpa using b⟩

#print axioms cycle_slowest_clear

/-- **Any lonely instant inside the cycle lies in the slowest reading's clear window**: `1 ≤ 8 m t ≤ 7`.  Needs only
that `m` is a disparity (`m ∈ ds`) and `m > 0`; that `m` is the least is not used. -/
theorem lonely_cycle_window {ds : Finset ℝ} {m : ℝ} (hm : 0 < m) (hmem : m ∈ ds) {t : ℝ}
    (hl : Cascade.LonelyAt ds t) (ht : t ∈ cycle m) : 1 ≤ 8 * m * t ∧ 8 * m * t ≤ 7 := by
  have h := (cycle_slowest_clear hm ht).mp (hl m hmem)
  obtain ⟨a, b⟩ := h
  rw [div_le_iff₀ (by positivity)] at a
  rw [le_div_iff₀ (by positivity)] at b
  constructor <;> nlinarith

#print axioms lonely_cycle_window

/-- **Another reading runs through `[0, d/m]` over the cycle**, and `d/m ≥ 1` when `m ≤ d`: every other reading
completes at least one lap line during the cycle (it reads `1` at `t = 1/d ≤ 1/m`). -/
theorem cycle_image_other {m d : ℝ} (hm : 0 < m) (hd : 0 < d) :
    (fun t => d * t) '' cycle m = Set.Icc 0 (d / m) := by
  ext u
  constructor
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
    refine ⟨by positivity, ?_⟩
    calc d * t ≤ d * (1 / m) := mul_le_mul_of_nonneg_left h1 hd.le
      _ = d / m := by ring
  · rintro ⟨h0, h1⟩
    refine ⟨u / d, ⟨by positivity, ?_⟩, by field_simp⟩
    rw [div_le_div_iff₀ hd hm]
    rw [le_div_iff₀ hm] at h1
    linarith

#print axioms cycle_image_other

theorem one_le_div_of_le {m d : ℝ} (hm : 0 < m) (hmd : m ≤ d) : 1 ≤ d / m := by
  rw [le_div_iff₀ hm]; linarith

#print axioms one_le_div_of_le

/-- At the end of the cycle the reading `d` stands at `d/m`. -/
theorem reading_at_cycle_end (d m : ℝ) : d * (1 / m) = d / m := by ring

#print axioms reading_at_cycle_end

/-- A reading is back at its start at the end of the cycle iff `d` is a whole multiple of `m`. -/
theorem returns_at_cycle_end_iff {m : ℝ} (hm : 0 < m) (d : ℝ) :
    distInt (d * (1 / m)) = 0 ↔ ∃ z : ℤ, d = z * m := by
  rw [distInt_eq_zero_iff]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    field_simp at hz
    linarith
  · rintro ⟨z, rfl⟩
    exact ⟨z, by field_simp⟩

#print axioms returns_at_cycle_end_iff

/-! ## (2) The grand return -/

/-- A grand return: a positive instant `T` at which every reading `d·T` is a whole number of laps (every runner is
back at its starting point relative to the subject).  The framework's own objects do not use it (`Cascade.LonelyAt`,
`IsMove` and `CascadeFixes` mention no `T`). -/
-- STANDING: DEFINITION
def GrandReturn (ds : Finset ℝ) (T : ℝ) : Prop := 0 < T ∧ ∀ d ∈ ds, ∃ z : ℤ, d * T = z

/-- **The cycle of the slowest reading is a grand return iff `m` divides every disparity** (`d = z m`, `z` an integer). -/
theorem cycle_is_grandReturn_iff {ds : Finset ℝ} {m : ℝ} (hm : 0 < m) :
    GrandReturn ds (1 / m) ↔ ∀ d ∈ ds, ∃ z : ℤ, d = z * m := by
  unfold GrandReturn
  constructor
  · rintro ⟨-, h⟩ d hd
    obtain ⟨z, hz⟩ := h d hd
    refine ⟨z, ?_⟩
    field_simp at hz
    linarith
  · intro h
    refine ⟨by positivity, fun d hd => ?_⟩
    obtain ⟨z, hz⟩ := h d hd
    exact ⟨z, by rw [hz]; field_simp⟩

#print axioms cycle_is_grandReturn_iff

/-- The cycle is not always a grand return (the failed hypothesis is `m ∣ d`): for `{2, 3}` the cycle is `1/2` and the
grand return is `1`, two rotations of the slowest reading. -/
theorem cycle_not_grandReturn_example :
    ¬ GrandReturn ({2, 3} : Finset ℝ) (1 / 2) ∧ GrandReturn ({2, 3} : Finset ℝ) 1 := by
  constructor
  · rw [cycle_is_grandReturn_iff (by norm_num)]
    intro h
    obtain ⟨z, hz⟩ := h 3 (by simp)
    have h1 : (z : ℝ) * 2 = 3 := hz.symm
    have h2 : z * 2 = (3 : ℤ) := by exact_mod_cast h1
    omega
  · refine ⟨by norm_num, fun d hd => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact ⟨2, by norm_num⟩
    · exact ⟨3, by norm_num⟩

#print axioms cycle_not_grandReturn_example

/-- **Period `T`.**  If every reading `d·T` is a whole number (no positivity of `T` or of `ds` used), the lonely set is
unchanged by `t ↦ t + T`. -/
theorem lonelyAt_add_of_return {ds : Finset ℝ} {T : ℝ} (h : ∀ d ∈ ds, ∃ z : ℤ, d * T = z) (t : ℝ) :
    Cascade.LonelyAt ds (t + T) ↔ Cascade.LonelyAt ds t := by
  unfold Cascade.LonelyAt
  refine forall_congr' fun d => forall_congr' fun hd => ?_
  obtain ⟨z, hz⟩ := h d hd
  rw [mul_add, hz, distInt_add_int]

#print axioms lonelyAt_add_of_return

/-- Period `k T` for every integer `k`. -/
theorem lonelyAt_add_int_mul {ds : Finset ℝ} {T : ℝ} (h : ∀ d ∈ ds, ∃ z : ℤ, d * T = z) (k : ℤ) (t : ℝ) :
    Cascade.LonelyAt ds (t + k * T) ↔ Cascade.LonelyAt ds t := by
  unfold Cascade.LonelyAt
  refine forall_congr' fun d => forall_congr' fun hd => ?_
  obtain ⟨z, hz⟩ := h d hd
  have e : d * (t + k * T) = d * t + ((k * z : ℤ) : ℝ) := by
    push_cast; rw [← hz]; ring
  rw [e, distInt_add_int]

#print axioms lonelyAt_add_int_mul

/-- **Mirror symmetry.**  If every reading `d·T` is a whole number, the lonely set is unchanged by `t ↦ T − t`. -/
theorem lonelyAt_sub_of_return {ds : Finset ℝ} {T : ℝ} (h : ∀ d ∈ ds, ∃ z : ℤ, d * T = z) (t : ℝ) :
    Cascade.LonelyAt ds (T - t) ↔ Cascade.LonelyAt ds t := by
  unfold Cascade.LonelyAt
  refine forall_congr' fun d => forall_congr' fun hd => ?_
  obtain ⟨z, hz⟩ := h d hd
  have e : d * (T - t) = -(d * t) + (z : ℝ) := by rw [← hz]; ring
  rw [e, distInt_add_int, Cascade.distInt_neg]

#print axioms lonelyAt_sub_of_return

/-- **The lonely set is periodic with period `T`**, as a set equality. -/
theorem lonelySet_add_period {ds : Finset ℝ} {T : ℝ} (hT : GrandReturn ds T) :
    (fun t => t + T) ⁻¹' lonelySet ds = lonelySet ds := by
  ext t
  exact lonelyAt_add_of_return hT.2 t

#print axioms lonelySet_add_period

/-- **The lonely set is symmetric under `t ↦ T − t`**, as a set equality. -/
theorem lonelySet_mirror {ds : Finset ℝ} {T : ℝ} (hT : GrandReturn ds T) :
    (fun t => T - t) ⁻¹' lonelySet ds = lonelySet ds := by
  ext t
  exact lonelyAt_sub_of_return hT.2 t

#print axioms lonelySet_mirror

/-- **Integer disparities have the grand return `T = 1`.** -/
theorem grandReturn_one_of_int {ds : Finset ℝ} (hint : ∀ d ∈ ds, ∃ z : ℤ, d = z) : GrandReturn ds 1 := by
  refine ⟨one_pos, fun d hd => ?_⟩
  obtain ⟨z, rfl⟩ := hint d hd
  exact ⟨z, by ring⟩

#print axioms grandReturn_one_of_int

/-- **Provenance record: `Types.int_lonely_shift` is the case `T = 1`.**  The two symmetries used by
`Types.first_window_of_small_dmin` and `Types.no_crossing_of_small_dmin` (`t ↦ t + k`, `t ↦ k − t`) are the period and the
mirror of the grand return `T = 1` of integer disparities; the statement below is derived from the grand-return lemmas
(for the integer `k`, the grand return is `k·1`, i.e. `lonelyAt_add_int_mul`). -/
theorem int_lonely_shift_of_return {ds : Finset ℝ} (hint : ∀ d ∈ ds, ∃ z : ℤ, d = z) {t : ℝ} (k : ℤ)
    (hl : Cascade.LonelyAt ds t) : Cascade.LonelyAt ds (t + k) ∧ Cascade.LonelyAt ds (k - t) := by
  have h1 := (grandReturn_one_of_int hint).2
  constructor
  · have := (lonelyAt_add_int_mul h1 k t).mpr hl
    simpa using this
  · -- `k - t = 1·k - t`; mirror about `k/2` is the composite of the mirror about `1/2` and a shift by `k - 1`.
    have a := (lonelyAt_sub_of_return h1 t).mpr hl
    have b := (lonelyAt_add_int_mul h1 (k - 1) (1 - t)).mpr a
    have e : 1 - t + ((k - 1 : ℤ) : ℝ) * 1 = (k : ℝ) - t := by push_cast; ring
    rwa [e] at b

#print axioms int_lonely_shift_of_return

/-! ### Integer disparities: the least grand return is `1/gcd` -/

/-- The real disparity set of a finite set of integers. -/
noncomputable def ofInts (S : Finset ℤ) : Finset ℝ := S.image (fun z => (z : ℝ))

theorem mem_ofInts {S : Finset ℤ} {d : ℝ} : d ∈ ofInts S ↔ ∃ z ∈ S, (z : ℝ) = d := by
  unfold ofInts; simp [Finset.mem_image]

#print axioms mem_ofInts

/-- **Bezout for the grand return**: if `z·T` is a whole number for every `z ∈ S`, then `g·T` is, for `g = gcd S`. -/
theorem gcd_mul_int (S : Finset ℤ) (T : ℝ) (h : ∀ z ∈ S, ∃ w : ℤ, (z : ℝ) * T = w) :
    ∃ w : ℤ, ((S.gcd id : ℤ) : ℝ) * T = w := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨w', hw'⟩ := ih (fun z hz => h z (Finset.mem_insert_of_mem hz))
    obtain ⟨wa, hwa⟩ := h a (Finset.mem_insert_self a s)
    rw [Finset.gcd_insert]
    simp only [id]
    set b := s.gcd id with hb
    have hg : GCDMonoid.gcd a b = (Int.gcd a b : ℤ) := (Int.coe_gcd a b).symm
    rw [hg, Int.gcd_eq_gcd_ab a b]
    refine ⟨wa * Int.gcdA a b + w' * Int.gcdB a b, ?_⟩
    push_cast
    have e1 : (a : ℝ) * T = wa := hwa
    have e2 : (b : ℝ) * T = w' := by simpa [hb] using hw'
    calc ((a : ℝ) * Int.gcdA a b + b * Int.gcdB a b) * T
        = ((a : ℝ) * T) * Int.gcdA a b + ((b : ℝ) * T) * Int.gcdB a b := by ring
      _ = _ := by rw [e1, e2]

#print axioms gcd_mul_int

theorem gcd_pos_of_ne (S : Finset ℤ) (hS : ∃ z ∈ S, z ≠ 0) : 0 < S.gcd id := by
  have h0 : 0 ≤ S.gcd id := by
    have h : normalize (S.gcd id) = S.gcd id := Finset.normalize_gcd
    exact Int.nonneg_of_normalize_eq_self h
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨z, hz, hz0⟩ := hS
    have := Finset.gcd_dvd (f := id) hz
    simp only [id] at this
    rw [← h, zero_dvd_iff] at this
    exact hz0 this

#print axioms gcd_pos_of_ne

/-- **All grand returns of integer disparities.**  With `g = gcd S > 0`, `T` is a grand return iff `T = n/g` for a positive
integer `n`.  Hypothesis `∃ z ∈ S, z ≠ 0` is REQUIRED: for `S = {0}` every `T > 0` is a grand return and there is no
least one (and `gcd = 0`). -/
theorem grandReturn_ofInts_iff (S : Finset ℤ) (hS : ∃ z ∈ S, z ≠ 0) (T : ℝ) :
    GrandReturn (ofInts S) T ↔ ∃ n : ℕ, 0 < n ∧ T = (n : ℝ) / ((S.gcd id : ℤ) : ℝ) := by
  have hg := gcd_pos_of_ne S hS
  have hgr : (0 : ℝ) < ((S.gcd id : ℤ) : ℝ) := by exact_mod_cast hg
  constructor
  · rintro ⟨hT, h⟩
    obtain ⟨w, hw⟩ := gcd_mul_int S T (fun z hz => h (z : ℝ) (mem_ofInts.mpr ⟨z, hz, rfl⟩))
    have hwpos : 0 < w := by
      have : (0 : ℝ) < w := by rw [← hw]; positivity
      exact_mod_cast this
    refine ⟨w.toNat, by omega, ?_⟩
    have : ((w.toNat : ℕ) : ℝ) = (w : ℝ) := by
      have : ((w.toNat : ℕ) : ℤ) = w := Int.toNat_of_nonneg hwpos.le
      exact_mod_cast this
    rw [this, ← hw]
    field_simp
  · rintro ⟨n, hn, rfl⟩
    refine ⟨by positivity, fun d hd => ?_⟩
    obtain ⟨z, hz, rfl⟩ := mem_ofInts.mp hd
    obtain ⟨c, hc⟩ := Finset.gcd_dvd (f := id) hz
    simp only [id] at hc
    refine ⟨c * n, ?_⟩
    have : (z : ℝ) = ((S.gcd id : ℤ) : ℝ) * c := by exact_mod_cast hc
    rw [this]; push_cast; field_simp

#print axioms grandReturn_ofInts_iff

/-- **The least grand return of integer disparities is `1/gcd`.** -/
theorem grandReturn_ofInts_isLeast (S : Finset ℤ) (hS : ∃ z ∈ S, z ≠ 0) :
    IsLeast {T | GrandReturn (ofInts S) T} (1 / ((S.gcd id : ℤ) : ℝ)) := by
  have hg := gcd_pos_of_ne S hS
  have hgr : (0 : ℝ) < ((S.gcd id : ℤ) : ℝ) := by exact_mod_cast hg
  constructor
  · exact (grandReturn_ofInts_iff S hS _).mpr ⟨1, one_pos, by simp⟩
  · intro T hT
    obtain ⟨n, hn, rfl⟩ := (grandReturn_ofInts_iff S hS T).mp hT
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_le_div_of_nonneg_right this hgr.le

#print axioms grandReturn_ofInts_isLeast

/-! ### Real disparities: a grand return exists iff the disparities are pairwise commensurable -/

/-- **Two readings both whole at `T ≠ 0` force a rational ratio.**  Hypotheses `b ≠ 0`, `T ≠ 0` only (no positivity). -/
theorem ratio_rational_of_return {a b T : ℝ} (hb : b ≠ 0) (hT : T ≠ 0) (ha : ∃ z : ℤ, a * T = z)
    (hb' : ∃ w : ℤ, b * T = w) : ∃ q : ℚ, a = q * b := by
  obtain ⟨z, hz⟩ := ha
  obtain ⟨w, hw⟩ := hb'
  have hw0 : (w : ℝ) ≠ 0 := by rw [← hw]; exact mul_ne_zero hb hT
  refine ⟨(z : ℚ) / (w : ℚ), ?_⟩
  have e1 : a = (z : ℝ) / T := by rw [← hz]; field_simp
  have e2 : b = (w : ℝ) / T := by rw [← hw]; field_simp
  push_cast
  rw [e1, e2]
  field_simp

#print axioms ratio_rational_of_return

/-- **A rational ratio gives a grand return.** -/
theorem return_of_ratio_rational {a b : ℝ} (hb : 0 < b) (q : ℚ) (h : a = q * b) :
    GrandReturn {a, b} ((q.den : ℝ) / b) := by
  refine ⟨by positivity, fun d hd => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl
  · refine ⟨q.num, ?_⟩
    rw [h]
    have hq : (q : ℝ) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
    calc (q : ℝ) * b * ((q.den : ℝ) / b) = (q : ℝ) * q.den := by field_simp
      _ = q.num := hq
  · exact ⟨q.den, by push_cast; field_simp⟩

#print axioms return_of_ratio_rational

/-- **A grand return exists iff the (positive) disparities are pairwise commensurable.**
[PROVISIONAL: counting tool] the product of the denominators is a common denominator; supports "a common return exists"
for the finite set, not a shape of any result. -/
theorem exists_grandReturn_iff (ds : Finset ℝ) (hpos : ∀ d ∈ ds, 0 < d) :
    (∃ T, GrandReturn ds T) ↔ ∀ a ∈ ds, ∀ b ∈ ds, ∃ q : ℚ, a = q * b := by
  constructor
  · rintro ⟨T, hT, h⟩ a ha b hb
    exact ratio_rational_of_return (hpos b hb).ne' hT.ne' (h a ha) (h b hb)
  · intro h
    rcases ds.eq_empty_or_nonempty with rfl | ⟨b0, hb0⟩
    · exact ⟨1, one_pos, by simp⟩
    · choose! q hq using fun a (ha : a ∈ ds) => h a ha b0 hb0
      refine ⟨((∏ a ∈ ds, (q a).den : ℕ) : ℝ) / b0, ?_, fun d hd => ?_⟩
      · have : 0 < ∏ a ∈ ds, (q a).den := Finset.prod_pos (fun a _ => (q a).pos)
        have hb : 0 < b0 := hpos b0 hb0
        positivity
      · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun a => (q a).den) hd
        refine ⟨(q d).num * c, ?_⟩
        have hb : b0 ≠ 0 := (hpos b0 hb0).ne'
        have hqd : (q d : ℝ) * (q d).den = (q d).num := by exact_mod_cast Rat.mul_den_eq_num (q d)
        have hdb : d / b0 = (q d : ℝ) := by rw [div_eq_iff hb]; exact hq d hd
        rw [hc]
        push_cast
        calc d * (((q d).den * c : ℝ) / b0) = (d / b0) * ((q d).den * c) := by ring
          _ = ((q d : ℝ) * (q d).den) * c := by rw [hdb]; ring
          _ = _ := by rw [hqd]

#print axioms exists_grandReturn_iff

/-- **Non-commensurable readings have no grand return.**  `{1, √2}`. -/
theorem sqrt2_no_grandReturn : ¬ ∃ T, GrandReturn ({1, Real.sqrt 2} : Finset ℝ) T := by
  rw [exists_grandReturn_iff _ (by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact one_pos
    · positivity)]
  intro h
  obtain ⟨q, hq⟩ := h (Real.sqrt 2) (by simp) 1 (by simp)
  exact irrational_sqrt_two ⟨q, by rw [hq]; ring⟩

#print axioms sqrt2_no_grandReturn

/-- **This does not touch the conjecture's frame.**  For `{1, √2}` there is no grand return, yet an instant is lonely
(`t = 1/2`) and the cascade from any positive start `t₀ ≤ 1/2` reaches a fixed point
(`Cascade.exists_fixed_of_lonely`, whose hypotheses mention no `T`). -/
theorem sqrt2_lonely_no_return_cascade_fixes :
    Cascade.LonelyAt ({1, Real.sqrt 2} : Finset ℝ) (1 / 2) ∧
      (∃ N, Cascade.cascadeSeq ({1, Real.sqrt 2} : Finset ℝ) (1 / 16) (N + 1) =
        Cascade.cascadeSeq ({1, Real.sqrt 2} : Finset ℝ) (1 / 16) N) ∧
      ¬ ∃ T, GrandReturn ({1, Real.sqrt 2} : Finset ℝ) T := by
  have hs1 : (7 / 5 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hl : Cascade.LonelyAt ({1, Real.sqrt 2} : Finset ℝ) (1 / 2) := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact Localisation.clear_of_window 0 (by norm_num) (by norm_num)
    · exact Localisation.clear_of_window 0 (by push_cast; nlinarith) (by push_cast; nlinarith)
  refine ⟨hl, ?_, sqrt2_no_grandReturn⟩
  apply Cascade.exists_fixed_of_lonely (s := 1 / 2) _ (by norm_num) hl (by norm_num)
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl
  · exact one_pos
  · positivity

#print axioms sqrt2_lonely_no_return_cascade_fixes

/-! ## (3) The AP `{s, 2s, …, 7s}`: four isolations per grand return -/

/-- The seven disparities `s, 2s, …, 7s` of the AP (eight runners with the subject).  Positive for `s > 0`. -/
noncomputable def apDisp (s : ℝ) : Finset ℝ := (Finset.Icc (1 : ℕ) 7).image (fun k => (k : ℝ) * s)

theorem mem_apDisp {s d : ℝ} : d ∈ apDisp s ↔ ∃ k : ℕ, 1 ≤ k ∧ k ≤ 7 ∧ (k : ℝ) * s = d := by
  unfold apDisp; simp [Finset.mem_image, Finset.mem_Icc, and_assoc]

#print axioms mem_apDisp

theorem apDisp_pos {s : ℝ} (hs : 0 < s) : ∀ d ∈ apDisp s, 0 < d := by
  intro d hd
  obtain ⟨k, hk1, -, rfl⟩ := mem_apDisp.mp hd
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  positivity

#print axioms apDisp_pos

/-- Loneliness for the AP in the coordinates of `{1,…,7}` at the instant `s t`. -/
theorem lonelyAt_apDisp_iff (s t : ℝ) :
    Cascade.LonelyAt (apDisp s) t ↔ ∀ k : ℤ, 1 ≤ k → k ≤ 7 → (1 / 8 : ℝ) ≤ distInt ((k : ℝ) * (s * t)) := by
  constructor
  · intro h k hk1 hk7
    have hmem : ((k.toNat : ℕ) : ℝ) * s ∈ apDisp s :=
      mem_apDisp.mpr ⟨k.toNat, by omega, by omega, rfl⟩
    have := h _ hmem
    have hk : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
      have : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [hk] at this
    rwa [mul_assoc] at this
  · intro h d hd
    obtain ⟨k, hk1, hk7, rfl⟩ := mem_apDisp.mp hd
    have := h (k : ℤ) (by exact_mod_cast hk1) (by exact_mod_cast hk7)
    push_cast at this
    rwa [← mul_assoc] at this

#print axioms lonelyAt_apDisp_iff

/-- **The lonely set of the AP, exactly** (`OneMultiple.ap7_lonely_iff` transported by `u = s t`): `t` is lonely iff
`8 s t` is an odd integer.  Any `s` (no sign, no `s ≠ 0` used: for `s = 0` the right side is false at every `t` because
`8·0 = 0` is even). -/
theorem lonelyAt_apDisp_iff_odd (s t : ℝ) :
    Cascade.LonelyAt (apDisp s) t ↔ ∃ j : ℤ, 8 * (s * t) = j ∧ j % 2 = 1 := by
  rw [lonelyAt_apDisp_iff]
  exact OneMultiple.ap7_lonely_iff (s * t)

#print axioms lonelyAt_apDisp_iff_odd

/-- The cycle of the AP is a grand return, and the grand returns are the positive multiples of `1/s`. -/
theorem ap_grandReturn_iff {s : ℝ} (hs : 0 < s) (T : ℝ) :
    GrandReturn (apDisp s) T ↔ ∃ n : ℕ, 0 < n ∧ T = (n : ℝ) / s := by
  constructor
  · rintro ⟨hT, h⟩
    obtain ⟨z, hz⟩ := h (1 * s) (mem_apDisp.mpr ⟨1, le_refl _, by norm_num, by norm_num⟩)
    have hz' : (z : ℝ) = s * T := by rw [← hz]; ring
    have hzpos : 0 < z := by
      have : (0 : ℝ) < z := by rw [hz']; positivity
      exact_mod_cast this
    refine ⟨z.toNat, by omega, ?_⟩
    have : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
      have : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hzpos.le
      exact_mod_cast this
    rw [this, hz']
    field_simp
  · rintro ⟨n, hn, rfl⟩
    refine ⟨by positivity, fun d hd => ?_⟩
    obtain ⟨k, -, -, rfl⟩ := mem_apDisp.mp hd
    exact ⟨k * n, by push_cast; field_simp⟩

#print axioms ap_grandReturn_iff

theorem ap_cycle_is_grandReturn {s : ℝ} (hs : 0 < s) : GrandReturn (apDisp s) (1 / s) := by
  have := (ap_grandReturn_iff hs (1 / s)).mpr ⟨1, one_pos, by simp⟩
  exact this

#print axioms ap_cycle_is_grandReturn

/-- The instants `a/(8s)`, `a` a residue mod 8 coprime to 8 (the units mod 8), `0 ≤ a < 8`. -/
noncomputable def apInstants (s : ℝ) : Finset ℝ :=
  ((Finset.range 8).filter (fun a => Nat.Coprime 8 a)).image (fun a : ℕ => (a : ℝ) / (8 * s))

theorem coprime_filter_eq : (Finset.range 8).filter (fun a => Nat.Coprime 8 a) = {1, 3, 5, 7} := by decide

#print axioms coprime_filter_eq

theorem mem_apInstants {s t : ℝ} :
    t ∈ apInstants s ↔ t = 1 / (8 * s) ∨ t = 3 / (8 * s) ∨ t = 5 / (8 * s) ∨ t = 7 / (8 * s) := by
  unfold apInstants
  rw [coprime_filter_eq]
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases ha with rfl | rfl | rfl | rfl <;> simp
  · rintro (h | h | h | h)
    · exact ⟨1, Or.inl rfl, by rw [h]; simp⟩
    · exact ⟨3, Or.inr (Or.inl rfl), by rw [h]; norm_num⟩
    · exact ⟨5, Or.inr (Or.inr (Or.inl rfl)), by rw [h]; norm_num⟩
    · exact ⟨7, Or.inr (Or.inr (Or.inr rfl)), by rw [h]; norm_num⟩

#print axioms mem_apInstants

/-- **FOUR ISOLATIONS PER GRAND RETURN.**  For `s > 0`, the lonely instants of the AP `{s,…,7s}` inside one grand return
`[0, 1/s]` are exactly `t = k/(8s)`, `k ∈ {1,3,5,7}`.  Uses `OneMultiple.ap7_lonely_iff` (through
`lonelyAt_apDisp_iff_odd`). -/
theorem lonely_apDisp_cycle {s : ℝ} (hs : 0 < s) (t : ℝ) :
    (t ∈ cycle s ∧ Cascade.LonelyAt (apDisp s) t) ↔ t ∈ apInstants s := by
  rw [mem_apInstants, lonelyAt_apDisp_iff_odd]
  constructor
  · rintro ⟨⟨h0, h1⟩, j, hj, hodd⟩
    have hst1 : s * t ≤ 1 := by
      rw [le_div_iff₀ hs] at h1; linarith
    have hst0 : 0 ≤ s * t := by positivity
    have hj0 : (0 : ℝ) ≤ j := by rw [← hj]; linarith
    have hj8 : (j : ℝ) ≤ 8 := by rw [← hj]; linarith
    have hj0' : 0 ≤ j := by exact_mod_cast hj0
    have hj8' : j ≤ 8 := by exact_mod_cast hj8
    have ht : t = (j : ℝ) / (8 * s) := by
      field_simp; linarith
    have hc : j = 1 ∨ j = 3 ∨ j = 5 ∨ j = 7 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> simp [ht]
  · intro h
    have key : ∀ (a : ℕ), (a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7) → t = (a : ℝ) / (8 * s) →
        (t ∈ cycle s ∧ ∃ j : ℤ, 8 * (s * t) = j ∧ j % 2 = 1) := by
      intro a ha ht
      refine ⟨⟨by rw [ht]; positivity, ?_⟩, (a : ℤ), ?_, by omega⟩
      · rw [ht, div_le_div_iff₀ (by positivity) hs]
        have : (a : ℝ) ≤ 8 := by
          have : a ≤ 8 := by omega
          exact_mod_cast this
        nlinarith
      · rw [ht]; push_cast; field_simp
    rcases h with h | h | h | h
    · exact key 1 (by simp) (by rw [h]; simp)
    · exact key 3 (by simp) (by rw [h]; norm_num)
    · exact key 5 (by simp) (by rw [h]; norm_num)
    · exact key 7 (by simp) (by rw [h]; norm_num)

#print axioms lonely_apDisp_cycle

/-- The same, as a set equality: `lonelySet ∩ cycle = the four instants`. -/
theorem lonelySet_inter_cycle {s : ℝ} (hs : 0 < s) :
    lonelySet (apDisp s) ∩ cycle s = ↑(apInstants s) := by
  ext t
  have := lonely_apDisp_cycle hs t
  simp only [Set.mem_inter_iff, lonelySet, Set.mem_setOf_eq, Finset.mem_coe]
  rw [← this]
  tauto

#print axioms lonelySet_inter_cycle

/-- **Their number is `Nat.totient 8 = 4`**: the instants are indexed by the residues `a` mod 8 coprime to 8, which is the
definition of `Nat.totient 8`.  [PROVISIONAL: counting tool] the count of the instants equals the count of coprime
residues; supports the claim "four isolations per grand return", it is not a shape of the result (the result is
`lonely_apDisp_cycle`). -/
theorem card_apInstants {s : ℝ} (hs : 0 < s) : (apInstants s).card = Nat.totient 8 := by
  unfold apInstants
  rw [Finset.card_image_of_injective]
  · rfl
  · intro a b hab
    have h8 : (8 * s) ≠ 0 := by positivity
    have : (a : ℝ) = b := by
      have := hab
      simp only at this
      field_simp at this
      exact this
    exact_mod_cast this

#print axioms card_apInstants

theorem totient_eight : Nat.totient 8 = 4 := by decide

#print axioms totient_eight

/-- The units mod 8 number `Nat.totient 8 = 4`, and a residue is a unit iff it is coprime to 8: the instants are indexed
by `(ZMod 8)ˣ`. -/
theorem units_mod_eight_card : Fintype.card (ZMod 8)ˣ = 4 := by
  rw [ZMod.card_units_eq_totient]; exact totient_eight

#print axioms units_mod_eight_card

theorem isUnit_iff_coprime_eight (a : ℕ) : IsUnit (a : ZMod 8) ↔ Nat.Coprime 8 a := by
  rw [ZMod.isUnit_iff_coprime]; exact Nat.coprime_comm

#print axioms isUnit_iff_coprime_eight

theorem card_apInstants_eq_four {s : ℝ} (hs : 0 < s) : (apInstants s).card = 4 := by
  rw [card_apInstants hs, totient_eight]

#print axioms card_apInstants_eq_four

/-- No instant between two consecutive lonely instants is lonely (`j` any odd integer): `8 s t` would be an even
integer.  This includes the grand return itself, `t = 1/s`, `8 s t = 8`. -/
theorem no_lonely_between {s : ℝ} (hs : 0 < s) (j : ℤ) (hj : j % 2 = 1) (t : ℝ)
    (h1 : (j : ℝ) / (8 * s) < t) (h2 : t < ((j : ℝ) + 2) / (8 * s)) :
    ¬ Cascade.LonelyAt (apDisp s) t := by
  rw [lonelyAt_apDisp_iff_odd]
  rintro ⟨n, hn, hodd⟩
  rw [div_lt_iff₀ (by positivity)] at h1
  rw [lt_div_iff₀ (by positivity)] at h2
  have a1 : (j : ℝ) < n := by rw [← hn]; nlinarith
  have a2 : (n : ℝ) < j + 2 := by rw [← hn]; nlinarith
  have b1 : j < n := by exact_mod_cast a1
  have b2 : n < j + 2 := by
    have : (n : ℝ) < ((j + 2 : ℤ) : ℝ) := by push_cast; exact a2
    exact_mod_cast this
  omega

#print axioms no_lonely_between

/-- Below the first and the grand return itself are not lonely. -/
theorem not_lonely_start_end {s : ℝ} (hs : 0 < s) :
    ¬ Cascade.LonelyAt (apDisp s) 0 ∧ ¬ Cascade.LonelyAt (apDisp s) (1 / s) := by
  constructor
  · rw [lonelyAt_apDisp_iff_odd]
    rintro ⟨j, hj, hodd⟩
    have : j = 0 := by
      have : (j : ℝ) = 0 := by rw [← hj]; ring
      exact_mod_cast this
    omega
  · rw [lonelyAt_apDisp_iff_odd]
    rintro ⟨j, hj, hodd⟩
    have : j = 8 := by
      have : (j : ℝ) = 8 := by rw [← hj]; field_simp
      exact_mod_cast this
    omega

#print axioms not_lonely_start_end

/-- Why the midpoint is blocked: at an even `8 s t` the runner `4 s` stands on a lap line. -/
theorem blocked_at_even {s t : ℝ} (b : ℤ) (h : 8 * (s * t) = 2 * b) :
    4 * s ∈ apDisp s ∧ distInt ((4 * s) * t) = 0 := by
  refine ⟨mem_apDisp.mpr ⟨4, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  rw [distInt_eq_zero_iff]
  exact ⟨b, by linarith⟩

#print axioms blocked_at_even

/-! ### Zero margin: each lonely instant is a touch -/

/-- `distInt` at the eighths: `distInt (n/8) = min (n mod 8) (8 − n mod 8) / 8`. -/
theorem distInt_nat_div_eight (n : ℕ) :
    distInt ((n : ℝ) / 8) = ((min (n % 8) (8 - n % 8) : ℕ) : ℝ) / 8 := by
  have hn : (n : ℝ) / 8 = ((n % 8 : ℕ) : ℝ) / 8 + (((n / 8 : ℕ) : ℤ) : ℝ) := by
    have : (n : ℝ) = ((n % 8 : ℕ) : ℝ) + 8 * ((n / 8 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mod_add_div n 8).symm
    rw [Int.cast_natCast]
    nth_rewrite 1 [this]
    ring
  rw [hn, distInt_add_int]
  have hr : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
  generalize n % 8 = r at hr ⊢
  interval_cases r <;> unfold distInt <;> norm_num [round_eq, Int.floor_eq_iff]

#print axioms distInt_nat_div_eight

theorem touch_table :
    ∀ j ∈ ({1, 3, 5, 7} : Finset ℕ), ∀ k ∈ Finset.Icc 1 7,
      (min ((k * j) % 8) (8 - (k * j) % 8) = 1 ↔ (k = j ∨ k + j = 8)) := by decide

#print axioms touch_table

/-- **Zero-margin touch.**  At the lonely instant `t = j/(8s)` (`j ∈ {1,3,5,7}`) the reading `k s` stands exactly at an edge
of its window (`distInt = 1/8`) iff `k = j` or `k + j = 8`: exactly two readings touch, `j s` and `(8 − j) s`, and every
other reading is strictly inside its window (`distInt` is a multiple of `1/8`, at least `2/8`). -/
theorem touch_readings {s : ℝ} (hs : 0 < s) (j k : ℕ) (hj : j = 1 ∨ j = 3 ∨ j = 5 ∨ j = 7)
    (hk1 : 1 ≤ k) (hk7 : k ≤ 7) :
    distInt (((k : ℝ) * s) * ((j : ℝ) / (8 * s))) = 1 / 8 ↔ (k = j ∨ k + j = 8) := by
  have e : ((k : ℝ) * s) * ((j : ℝ) / (8 * s)) = ((k * j : ℕ) : ℝ) / 8 := by
    push_cast; field_simp
  rw [e, distInt_nat_div_eight]
  have hjm : j ∈ ({1, 3, 5, 7} : Finset ℕ) := by
    rcases hj with rfl | rfl | rfl | rfl <;> simp
  have := touch_table j hjm k (Finset.mem_Icc.mpr ⟨hk1, hk7⟩)
  rw [← this]
  constructor
  · intro h
    have : ((min (k * j % 8) (8 - k * j % 8) : ℕ) : ℝ) = 1 := by linarith
    exact_mod_cast this
  · intro h
    rw [h]; norm_num

#print axioms touch_readings

/-- Every lonely instant of the cycle is a zero-margin touch: some disparity of the AP stands at exactly `1/8`. -/
theorem zeroMargin {s : ℝ} (hs : 0 < s) (t : ℝ) (ht : t ∈ apInstants s) :
    Cascade.LonelyAt (apDisp s) t ∧ ∃ d ∈ apDisp s, distInt (d * t) = 1 / 8 := by
  have hc := (lonely_apDisp_cycle hs t).mpr ht
  refine ⟨hc.2, ?_⟩
  rw [mem_apInstants] at ht
  have key : ∀ j : ℕ, (j = 1 ∨ j = 3 ∨ j = 5 ∨ j = 7) → t = (j : ℝ) / (8 * s) →
      ∃ d ∈ apDisp s, distInt (d * t) = 1 / 8 := by
    intro j hj htj
    refine ⟨(j : ℝ) * s, mem_apDisp.mpr ⟨j, by omega, by omega, rfl⟩, ?_⟩
    rw [htj]
    exact (touch_readings hs j j hj (by omega) (by omega)).mpr (Or.inl rfl)
  rcases ht with h | h | h | h
  · exact key 1 (by simp) (by rw [h]; simp)
  · exact key 3 (by simp) (by rw [h]; norm_num)
  · exact key 5 (by simp) (by rw [h]; norm_num)
  · exact key 7 (by simp) (by rw [h]; norm_num)

#print axioms zeroMargin

/-! ### The eight-runner AP: the subject and the global isolation are the same set of instants -/

/-- The disparities of the AP `v j = v₀ + j s` seen from its slowest runner (subject `0`) are `apDisp s`. -/
theorem disparitySet_ap (v : Fin 8 → ℝ) (s v₀ : ℝ) (hs : 0 < s)
    (hv : ∀ j : Fin 8, v j = v₀ + ((j : ℕ) : ℝ) * s) : disparitySet v 0 = apDisp s := by
  ext d
  rw [Localisation.mem_disparitySet, mem_apDisp]
  have hdiff : ∀ i : Fin 8, |v i - v 0| = ((i : ℕ) : ℝ) * s := by
    intro i
    rw [hv i, hv 0]
    simp only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero]
    rw [abs_of_nonneg (by have : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _; nlinarith)]
    ring
  constructor
  · rintro ⟨i, hi, rfl⟩
    have h1 : 1 ≤ (i : ℕ) := by
      rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
      · exact absurd (Fin.ext h) hi
      · exact h
    exact ⟨i, h1, by have := i.isLt; omega, (hdiff i).symm⟩
  · rintro ⟨k, hk1, hk7, rfl⟩
    refine ⟨⟨k, by omega⟩, ?_, ?_⟩
    · intro h
      have := congrArg (fun x : Fin 8 => (x : ℕ)) h
      simp at this
      omega
    · rw [hdiff]

#print axioms disparitySet_ap

theorem isCoprime_eight_iff (a : ℤ) : IsCoprime a 8 ↔ a % 2 = 1 := by
  constructor
  · intro h
    by_contra hne
    have he : Even a := Int.even_iff.mpr (by omega)
    obtain ⟨b, rfl⟩ := he
    have h2 : IsCoprime (2 : ℤ) 8 := by
      have : IsCoprime (b + b) 8 := h
      rw [← two_mul] at this
      exact this.of_mul_left_left
    rw [Int.isCoprime_iff_gcd_eq_one] at h2
    revert h2; decide
  · intro h
    exact isCoprime_eight_of_odd (Int.odd_iff.mpr h)

#print axioms isCoprime_eight_iff

/-- **Global isolation of the eight runners = loneliness of the slowest** at the AP: the same set of instants.  Uses
`Grid.ap_globalIsolation_iff` (the φ(8) law, both directions) and `lonelyAt_apDisp_iff_odd`
(`OneMultiple.ap7_lonely_iff`): two independent characterisations of the same set `{t : 8 s t odd}`. -/
theorem ap_global_iff (v : Fin 8 → ℝ) (s v₀ : ℝ) (hs : 0 < s)
    (hv : ∀ j : Fin 8, v j = v₀ + ((j : ℕ) : ℝ) * s) (t : ℝ) :
    GloballyIsolatedAt v t ↔ Cascade.LonelyAt (apDisp s) t := by
  rw [ap_globalIsolation_iff v s v₀ hs hv t, lonelyAt_apDisp_iff_odd]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, by field_simp, (isCoprime_eight_iff a).mp ha⟩
  · rintro ⟨j, hj, hodd⟩
    refine ⟨j, (isCoprime_eight_iff j).mpr hodd, ?_⟩
    field_simp
    linarith

#print axioms ap_global_iff

theorem ap_subject_iff (v : Fin 8 → ℝ) (s v₀ : ℝ) (hs : 0 < s)
    (hv : ∀ j : Fin 8, v j = v₀ + ((j : ℕ) : ℝ) * s) (t : ℝ) :
    IsolatedAt v 0 t ↔ GloballyIsolatedAt v t := by
  rw [ap_global_iff v s v₀ hs hv, Cascade.isolatedAt_iff_lonelyAt, disparitySet_ap v s v₀ hs hv]

#print axioms ap_subject_iff

/-! ## (4) Scale invariance -/

/-- Dilating every disparity by `c` is the same as dilating the instant by `c` (any `c`). -/
theorem lonelyAt_scale (c : ℝ) (ds : Finset ℝ) (t : ℝ) :
    Cascade.LonelyAt (ds.image (fun d => c * d)) t ↔ Cascade.LonelyAt ds (c * t) := by
  unfold Cascade.LonelyAt
  simp only [Finset.mem_image, forall_exists_index, and_imp]
  constructor
  · intro h d hd
    have := h (c * d) d hd rfl
    rwa [show c * d * t = d * (c * t) by ring] at this
  · intro h x d hd hx
    subst hx
    rw [show c * d * t = d * (c * t) by ring]
    exact h d hd

#print axioms lonelyAt_scale

theorem apDisp_eq_scale (s : ℝ) : apDisp s = (apDisp 1).image (fun d => s * d) := by
  ext d
  rw [mem_apDisp, Finset.mem_image]
  constructor
  · rintro ⟨k, hk1, hk7, rfl⟩
    exact ⟨(k : ℝ) * 1, mem_apDisp.mpr ⟨k, hk1, hk7, rfl⟩, by ring⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, hk1, hk7, rfl⟩ := mem_apDisp.mp hx
    exact ⟨k, hk1, hk7, by ring⟩

#print axioms apDisp_eq_scale

theorem lonelyAt_apDisp_scale (s t : ℝ) :
    Cascade.LonelyAt (apDisp s) t ↔ Cascade.LonelyAt (apDisp 1) (s * t) := by
  rw [apDisp_eq_scale s, lonelyAt_scale]

#print axioms lonelyAt_apDisp_scale

/-- **Scale invariance, exact.**  The lonely set of `{s,…,7s}` is the preimage of the lonely set of `{1,…,7}` under
`t ↦ s t` (any `s`), and, for `s ≠ 0`, the image of it under `u ↦ u / s`. -/
theorem lonelySet_apDisp_preimage (s : ℝ) :
    lonelySet (apDisp s) = (fun t => s * t) ⁻¹' lonelySet (apDisp 1) := by
  ext t
  exact lonelyAt_apDisp_scale s t

#print axioms lonelySet_apDisp_preimage

theorem lonelySet_apDisp_scale {s : ℝ} (hs : s ≠ 0) :
    lonelySet (apDisp s) = (fun u => u / s) '' lonelySet (apDisp 1) := by
  ext t
  rw [lonelySet_apDisp_preimage]
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · intro h
    exact ⟨s * t, h, by field_simp⟩
  · rintro ⟨u, hu, rfl⟩
    have : s * (u / s) = u := by field_simp
    rw [this]; exact hu

#print axioms lonelySet_apDisp_scale

/-- **The hypothesis `s ≠ 0` of the image form is REQUIRED**: for `s = 0` the lonely set of `{0,…,0}` is empty while the
image under `u ↦ u/0 = 0` is not. -/
theorem scale_needs_ne_zero :
    lonelySet (apDisp 0) ≠ (fun u => u / 0) '' lonelySet (apDisp 1) := by
  intro h
  have h1 : (1 / 8 : ℝ) ∈ lonelySet (apDisp 1) := by
    show Cascade.LonelyAt (apDisp 1) (1 / 8)
    rw [lonelyAt_apDisp_iff_odd]
    exact ⟨1, by norm_num, by norm_num⟩
  have h2 : (0 : ℝ) ∈ (fun u => u / 0) '' lonelySet (apDisp 1) :=
    ⟨1 / 8, h1, by simp⟩
  rw [← h] at h2
  have h3 : Cascade.LonelyAt (apDisp 0) 0 := h2
  rw [lonelyAt_apDisp_iff_odd] at h3
  obtain ⟨j, hj, hodd⟩ := h3
  have : j = 0 := by
    have : (j : ℝ) = 0 := by rw [← hj]; ring
    exact_mod_cast this
  omega

#print axioms scale_needs_ne_zero

/-- **The four instants scale with `s`**: `apInstants s` is `apInstants 1` divided by `s`. -/
theorem apInstants_scale {s : ℝ} (hs : 0 < s) :
    apInstants s = (apInstants 1).image (fun u => u / s) := by
  ext t
  rw [Finset.mem_image, mem_apInstants]
  constructor
  · rintro (h | h | h | h)
    · exact ⟨1 / 8, mem_apInstants.mpr (Or.inl (by norm_num)), by rw [h]; field_simp⟩
    · exact ⟨3 / 8, mem_apInstants.mpr (Or.inr (Or.inl (by norm_num))), by rw [h]; field_simp⟩
    · exact ⟨5 / 8, mem_apInstants.mpr (Or.inr (Or.inr (Or.inl (by norm_num)))), by rw [h]; field_simp⟩
    · exact ⟨7 / 8, mem_apInstants.mpr (Or.inr (Or.inr (Or.inr (by norm_num)))), by rw [h]; field_simp⟩
  · rintro ⟨u, hu, rfl⟩
    rw [mem_apInstants] at hu
    rcases hu with h | h | h | h <;> rw [h]
    · left; field_simp
    · right; left; field_simp
    · right; right; left; field_simp
    · right; right; right; field_simp

#print axioms apInstants_scale

/-- **Exact instances** (no decimals): `s = π`, `s = 1/12500` (the owner's `0.00008`), `s = m` for any `m > 0`: four
isolations per grand return `[0, 1/s]`, at `k/(8s)`. -/
theorem four_isolations_instances :
    (apInstants 1).card = 4 ∧ (apInstants Real.pi).card = 4 ∧ (apInstants (1 / 12500)).card = 4 ∧
      ∀ m : ℝ, 0 < m → (apInstants m).card = 4 := by
  refine ⟨card_apInstants_eq_four one_pos, card_apInstants_eq_four Real.pi_pos,
    card_apInstants_eq_four (by norm_num), fun m hm => card_apInstants_eq_four hm⟩

#print axioms four_isolations_instances

/-- One cascade step commutes with the dilation (`Dilation.reading_dilation` is the same fact for the readings: every
reading is multiplied by one common factor). -/
theorem inWay_scale {c : ℝ} (hc : 0 < c) (d t : ℝ) : InWay (c * d) (t / c) ↔ InWay d t := by
  unfold InWay
  rw [show c * d * (t / c) = d * t by field_simp]

#print axioms inWay_scale

theorem nextOpening_scale {c : ℝ} (hc : 0 < c) (d t : ℝ) :
    nextOpening (c * d) (t / c) = nextOpening d t / c := by
  unfold nextOpening
  rw [show c * d * (t / c) = d * t by field_simp, div_div, mul_comm c d]

#print axioms nextOpening_scale

theorem isMove_scale {c : ℝ} (hc : 0 < c) (ds : Finset ℝ) (t t' : ℝ) :
    IsMove (ds.image (fun d => c * d)) (t / c) (t' / c) ↔ IsMove ds t t' := by
  have hcne : c ≠ 0 := hc.ne'
  unfold IsMove
  simp only [Finset.forall_mem_image, Finset.exists_mem_image, inWay_scale hc, nextOpening_scale hc,
    div_left_inj' hcne, div_le_div_iff_of_pos_right hc]

#print axioms isMove_scale

/-- **The cascade is scale invariant**: the cascade of `{c d}` from `t₀/c` reaches a fixed point iff the cascade of `ds`
from `t₀` does. -/
theorem cascadeFixes_scale {c : ℝ} (hc : 0 < c) (ds : Finset ℝ) (t₀ : ℝ) :
    CascadeFixes (ds.image (fun d => c * d)) (t₀ / c) ↔ CascadeFixes ds t₀ := by
  have hcne : c ≠ 0 := hc.ne'
  unfold CascadeFixes
  constructor
  · rintro ⟨seq, h0, hmv, N, hN⟩
    refine ⟨fun n => seq n * c, by simp [h0]; field_simp, fun n => ?_, N, by simp [hN]⟩
    have := hmv n
    rw [show seq n = (seq n * c) / c by field_simp, show seq (n + 1) = (seq (n + 1) * c) / c by field_simp] at this
    exact (isMove_scale hc ds _ _).mp this
  · rintro ⟨seq, h0, hmv, N, hN⟩
    refine ⟨fun n => seq n / c, by simp [h0], fun n => ?_, N, by simp [hN]⟩
    exact (isMove_scale hc ds _ _).mpr (hmv n)

#print axioms cascadeFixes_scale

/-! ## (5) D_max, and what the AP needs -/

/-- **The eight indices `j·a` form a complete residue system mod 8 iff `a` is odd** (a unit mod 8). -/
theorem complete_iff_odd (a : ℤ) :
    CompleteResidues (fun j : Fin 8 => ((j : ℕ) : ℤ) * a) ↔ a % 2 = 1 := by
  constructor
  · intro h
    by_contra hne
    have h04 := h 0 4 (by simp only [Fin.val_zero, Nat.cast_zero, zero_mul]; norm_num [Fin.val_ofNat]; omega)
    exact absurd h04 (by decide)
  · intro hodd j j' hjj
    have hcop : IsCoprime 8 a := ((isCoprime_eight_iff a).mpr hodd).symm
    have h1 := Int.emod_emod_of_dvd
    have h2 : (8 : ℤ) ∣ ((j : ℕ) : ℤ) * a - ((j' : ℕ) : ℤ) * a := by
      have := Int.emod_emod_of_dvd
      exact Int.ModEq.dvd (show Int.ModEq 8 (((j' : ℕ) : ℤ) * a) (((j : ℕ) : ℤ) * a) from hjj.symm)
    have h3 : (8 : ℤ) ∣ ((j : ℕ) : ℤ) - ((j' : ℕ) : ℤ) := by
      apply hcop.dvd_of_dvd_mul_right
      rw [sub_mul]; exact h2
    have := j.isLt
    have := j'.isLt
    apply Fin.ext
    omega

#print axioms complete_iff_odd

/-- At the instant `t = a/(8s)` the reading of runner `j` against runner `0` is `j a / 8`: the eighth-grid index of
runner `j` is `j·a`. -/
theorem reading_index (v : Fin 8 → ℝ) (s v₀ : ℝ) (hs : 0 < s)
    (hv : ∀ j : Fin 8, v j = v₀ + ((j : ℕ) : ℝ) * s) (a : ℤ) (j : Fin 8) :
    (v j - v 0) * ((a : ℝ) / (8 * s)) = ((((j : ℕ) : ℤ) * a : ℤ) : ℝ) / 8 := by
  have e : v j - v 0 = ((j : ℕ) : ℝ) * s := by rw [hv j, hv 0]; simp
  rw [e]
  push_cast
  field_simp

#print axioms reading_index

/-- **The AP case of Grid.deviation_iff** (`e = 0`, `w = 0`, `idx j = j`): global isolation at `a/(8s)` iff the eight
indices `j·a` are a complete residue system mod 8. -/
theorem ap_global_iff_complete (v : Fin 8 → ℝ) (s v₀ : ℝ) (hs : 0 < s)
    (hv : ∀ j : Fin 8, v j = v₀ + ((j : ℕ) : ℝ) * s) (a : ℤ) :
    GloballyIsolatedAt v ((a : ℝ) / (8 * s)) ↔ CompleteResidues (fun j : Fin 8 => ((j : ℕ) : ℤ) * a) := by
  rw [deviation_iff v s v₀ (fun j => ((j : ℕ) : ℤ)) (fun _ => 0) hs rfl (fun j => by rw [hv j]; push_cast; ring) a]
  constructor
  · rintro ⟨w, hw, hc⟩
    have : w = fun _ => 0 := by
      funext j; have := hw j; simp at this; exact_mod_cast this.symm
    subst this
    simpa using hc
  · intro hc
    exact ⟨fun _ => 0, fun j => by simp, by simpa using hc⟩

#print axioms ap_global_iff_complete

/-- **Relation to D_max.**  For `a ∈ [0,8]` the instant `a/(8s)` is one of the four instants of the grand return iff the
eight indices `j·a` form a complete residue system (`complete_iff_odd`); shifting any index by a multiple of 8
(`dmax_complete`) keeps the system complete, hence keeps the four instants. -/
theorem four_instants_complete_residue {s : ℝ} (hs : 0 < s) (a : ℕ) (ha : a ≤ 8) :
    ((a : ℝ) / (8 * s) ∈ apInstants s) ↔ CompleteResidues (fun j : Fin 8 => ((j : ℕ) : ℤ) * (a : ℤ)) := by
  rw [complete_iff_odd, mem_apInstants]
  have h8 : (8 * s) ≠ 0 := by positivity
  have inj : ∀ b : ℕ, (a : ℝ) / (8 * s) = (b : ℝ) / (8 * s) ↔ a = b := by
    intro b
    rw [div_left_inj' h8]
    exact Nat.cast_inj
  constructor
  · rintro (h | h | h | h)
    · have := (inj 1).mp (by rw [h]; simp); omega
    · have := (inj 3).mp (by rw [h]; simp); omega
    · have := (inj 5).mp (by rw [h]; simp); omega
    · have := (inj 7).mp (by rw [h]; simp); omega
  · intro h
    have : a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · left; simp
    · right; left; simp
    · right; right; left; simp
    · right; right; right; simp

#print axioms four_instants_complete_residue

theorem dmax_index_complete (a : ℤ) (ha : a % 2 = 1) (c : Fin 8 → ℤ) :
    CompleteResidues (fun j : Fin 8 => ((j : ℕ) : ℤ) * a + 8 * c j) :=
  dmax_complete _ c ((complete_iff_odd a).mpr ha)

#print axioms dmax_index_complete

/-- **A D_max shift keeps the four instants**: if each runner's speed is moved by `8 c_j s` the eight runners are still
globally isolated at every `a/(8s)`, `a ∈ {1,3,5,7}` (`dmax_globalIsolation`, with `idx j = j`). -/
theorem dmax_four_instants (v : Fin 8 → ℝ) (s v₀ : ℝ) (hs : 0 < s) (c : Fin 8 → ℤ)
    (hv : ∀ j : Fin 8, v j = v₀ + ((j : ℕ) : ℝ) * s + 8 * (c j : ℝ) * s) :
    ∀ t ∈ apInstants s, GloballyIsolatedAt v t := by
  intro t ht
  rw [mem_apInstants] at ht
  have key : ∀ a : ℤ, IsCoprime a 8 → t = (a : ℝ) / (8 * s) → GloballyIsolatedAt v t := by
    intro a ha htt
    rw [htt]
    exact dmax_globalIsolation v s v₀ (fun j => ((j : ℕ) : ℤ)) c hs completeResidues_id hv a ha
  rcases ht with h | h | h | h
  · exact key 1 (by norm_num) (by rw [h]; simp)
  · exact key 3 (by rw [Int.isCoprime_iff_gcd_eq_one]; decide) (by rw [h]; simp)
  · exact key 5 (by rw [Int.isCoprime_iff_gcd_eq_one]; decide) (by rw [h]; simp)
  · exact key 7 (by rw [Int.isCoprime_iff_gcd_eq_one]; decide) (by rw [h]; simp)

#print axioms dmax_four_instants

/-! ## Hypothesis tests (each by trying to drop it) -/

/-- **`m ∈ ds` is REQUIRED for `lonely_cycle_window`**: `ds = {2}`, `m = 1`: the instant `1/16` is in the cycle `[0,1]` and
lonely, but `8 m t = 1/2 < 1`.  (Leastness of `m` is not used by the theorem.) -/
theorem window_needs_member :
    Cascade.LonelyAt ({2} : Finset ℝ) (1 / 16) ∧ (1 / 16 : ℝ) ∈ cycle 1 ∧ ¬ (1 ≤ 8 * (1 : ℝ) * (1 / 16)) := by
  refine ⟨?_, ⟨by norm_num, by norm_num⟩, by norm_num⟩
  intro d hd
  rw [Finset.mem_singleton] at hd
  subst hd
  exact Localisation.clear_of_window 0 (by norm_num) (by norm_num)

#print axioms window_needs_member

/-- **`∃ z ∈ S, z ≠ 0` is REQUIRED for the least grand return**: for `S = {0}` every positive `T` is a grand return, so
there is no least one. -/
theorem no_least_for_zero : ¬ ∃ T, IsLeast {T | GrandReturn (ofInts {0}) T} T := by
  rintro ⟨T, hT, hmin⟩
  have hT0 : 0 < T := hT.1
  have h2 : GrandReturn (ofInts {0}) (T / 2) := by
    refine ⟨by positivity, fun d hd => ?_⟩
    obtain ⟨z, hz, rfl⟩ := mem_ofInts.mp hd
    rw [Finset.mem_singleton] at hz
    subst hz
    exact ⟨0, by simp⟩
  have := hmin h2
  linarith

#print axioms no_least_for_zero

/-- **`0 < s` is REQUIRED for `lonely_apDisp_cycle`** (the cycle `[0, 1/s]` is empty for `s < 0`, while the four values
`k/(8s)` exist). -/
theorem lonely_cycle_needs_pos : ∃ t ∈ apInstants (-1), t ∉ cycle (-1) := by
  refine ⟨1 / (8 * (-1)), mem_apInstants.mpr (Or.inl rfl), ?_⟩
  rintro ⟨h0, h1⟩
  norm_num at h0

#print axioms lonely_cycle_needs_pos

end CycleReturn

end Fresh
