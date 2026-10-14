import Mathlib
import Fresh.Framework
import Fresh.Grid
import Fresh.DMax

/-!
# The cycle, the grand return, and the displacement between grids (Task X)

Written 2026-10-08.  Imports Mathlib and `Fresh.Framework`, `Fresh.Grid`, `Fresh.DMax` only.  Nothing is imported from
the existing `LonelyRunner` repo.  Source: the owner's own words,

* "We do have a cycle based on the full rotation of the slowest speed."
* "A grand return is when all runners reach the starting point at the same time, hence starting the cycle again with no
  new information or new outcomes possible as it becomes a repeating pattern.  All integer patterns have a grand return."
* "From any AP speed and from any Grid speed to the next AP/Grid speed any individual isolation is deformed with that
  isolation being displaced.  This is called D-min. ... Dmin also works from one Grid speed to the next."

Contents.
* Part 1 (integer speeds).  `GrandReturnAt`; with `G = gcdOf w` the instants at which every runner is at its start are
  exactly `z / G` (`grandReturn_iff`), the least positive one is `1/G` (`grandReturn_isLeast`).  The position pattern is
  periodic with period `τ` iff `τ` is a grand return (`positions_period_iff`, any real speeds).  A grand return is a
  period of every subject's isolation (`isolatedAt_add_grandReturn`); the exact period of a subject's reading pattern is
  `1/Gk` with `Gk` the gcd of its disparities (`readingPattern_period_iff`, `readingPattern_pos_period_iff`), and
  `G ∣ Gk` (`gcd_dvd_gcdDiff`).
* Part 1b (the slowest runner's rotation).  The rotation `1/m` of the slowest speed `m` equals the grand return iff
  `m` divides every speed (`gcd_eq_slowest_iff`, `grandReturn_slowest_iff`); in general the grand return is `m/G`
  rotations of the slowest runner (`grandReturn_eq_rotations`).  At the AP `1..8` they coincide
  (`ap18_cycles_equal`); counterexamples with the failed hypothesis named: `ap3_counter`, `ap_odd_counter`.
* Part 2 (real speeds).  A grand return exists iff all speeds are pairwise commensurable (`exists_grandReturn_iff`);
  an incommensurable pair has no common return and no period of any pattern containing it
  (`no_period_of_incommensurable`, `no_positions_period`, `no_reading_period`), with an explicit arrangement
  (`sqrt2_no_grandReturn`).
* Part 3 (D_min between grids).  Exact displacement of every reading when speeds change
  (`reading_displacement`), for a grid-to-grid change at the instant `a/(8d)` (`grid_reading_shift`), the isolation
  criterion at the old instant (`isolatedAt_gridShift_iff`), the single-runner case (`single_change_other`, `single_change_self`, `single_change_losers`, `single_change_all_iff`), and the fact
  that a single-runner change stays a grid only when it is a D_max shift (`shiftIdx_complete_iff`).  Nothing says a new
  isolation exists; that is the conjecture.

Counting tools: tagged **[PROVISIONAL: counting tool]** at the step (surjectivity of an injective `Fin 8 → ZMod 8`).
No density, coverage, cap or move budget appears.  No runner is stationary: every speed is positive, every isolation
statement is about differences.
-/

open Classical

namespace Fresh

namespace Cycle

/-! ## The gcd of eight integers, with Bezout -/

/-- The gcd of the eight integer speeds (or of eight integer disparities). -/
def gcdOf (w : Fin 8 → ℤ) : ℤ := Finset.univ.gcd w

theorem gcdOf_dvd (w : Fin 8 → ℤ) (i : Fin 8) : gcdOf w ∣ w i :=
  Finset.gcd_dvd (Finset.mem_univ i)

#print axioms gcdOf_dvd

theorem dvd_gcdOf (w : Fin 8 → ℤ) (n : ℤ) (h : ∀ i, n ∣ w i) : n ∣ gcdOf w :=
  Finset.dvd_gcd fun i _ => h i

#print axioms dvd_gcdOf

theorem gcdOf_nonneg (w : Fin 8 → ℤ) : 0 ≤ gcdOf w := by
  have h : normalize (gcdOf w) = gcdOf w := Finset.normalize_gcd
  exact Int.nonneg_of_normalize_eq_self h

#print axioms gcdOf_nonneg

theorem gcdOf_pos_of_ne (w : Fin 8 → ℤ) (i : Fin 8) (hi : w i ≠ 0) : 0 < gcdOf w := by
  rcases (gcdOf_nonneg w).lt_or_eq with h | h
  · exact h
  · exfalso
    have := gcdOf_dvd w i
    rw [← h, zero_dvd_iff] at this
    exact hi this

#print axioms gcdOf_pos_of_ne

/-- Bezout for eight integers. -/
theorem gcdOf_bezout (w : Fin 8 → ℤ) : ∃ c : Fin 8 → ℤ, ∑ i, c i * w i = gcdOf w := by
  obtain ⟨g0, hg0⟩ := IsPrincipalIdealRing.principal (Ideal.span (Set.range w))
  have hdvd : ∀ i, g0 ∣ w i := fun i => by
    have h : w i ∈ Ideal.span (Set.range w) := Ideal.subset_span ⟨i, rfl⟩
    rw [hg0] at h
    exact Submodule.mem_span_singleton.mp h |>.elim fun a ha => ⟨a, by rw [← ha]; ring⟩
  have hmem : g0 ∈ Ideal.span (Set.range w) := by
    rw [hg0]; exact Submodule.mem_span_singleton_self g0
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun ℤ |>.mp hmem
  have h1 : gcdOf w ∣ g0 := by
    rw [← hc]
    exact Finset.dvd_sum fun i _ => by simpa using (gcdOf_dvd w i).mul_left (c i)
  have h2 : g0 ∣ gcdOf w := dvd_gcdOf w g0 hdvd
  have h3 : (gcdOf w).natAbs = g0.natAbs := Nat.dvd_antisymm (Int.natAbs_dvd_natAbs.mpr h1)
    (Int.natAbs_dvd_natAbs.mpr h2)
  rcases Int.natAbs_eq_natAbs_iff.mp h3 with h | h
  · exact ⟨c, by rw [h, ← hc]; simp⟩
  · exact ⟨fun i => - c i, by rw [h, ← hc]; simp [Finset.sum_neg_distrib]⟩

#print axioms gcdOf_bezout


/-! ## Part 1: the grand return for integer speeds -/

/-- Every runner is at its start at the instant `t`: each position `v i · t` is a whole number of laps. -/
-- STANDING: DEFINITION
def GrandReturnAt (v : Fin 8 → ℝ) (t : ℝ) : Prop := ∀ i, ∃ z : ℤ, v i * t = z

/-- The return condition for integers `u i` (speeds or disparities) is the single condition `gcd · t ∈ ℤ`. -/
theorem returns_iff_gcd (u : Fin 8 → ℤ) (t : ℝ) :
    (∀ i, ∃ z : ℤ, (u i : ℝ) * t = z) ↔ ∃ z : ℤ, (gcdOf u : ℝ) * t = z := by
  constructor
  · intro h
    choose z hz using h
    obtain ⟨c, hc⟩ := gcdOf_bezout u
    refine ⟨∑ i, c i * z i, ?_⟩
    rw [← hc]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc, hz i]
  · rintro ⟨z, hz⟩ i
    obtain ⟨q, hq⟩ := gcdOf_dvd u i
    exact ⟨q * z, by rw [hq]; push_cast; rw [mul_assoc, ← hz]; ring⟩

#print axioms returns_iff_gcd

/-- **The grand return instants (integer speeds).**  With `G` the gcd of the speeds, every runner is at its start at
`t` exactly when `t = z/G`, `z` an integer.  [L] -/
theorem grandReturn_iff (w : Fin 8 → ℤ) (hw : ∀ i, 0 < w i) (t : ℝ) :
    GrandReturnAt (fun i => (w i : ℝ)) t ↔ ∃ z : ℤ, t = z / (gcdOf w : ℝ) := by
  have hG : (0 : ℝ) < gcdOf w := by exact_mod_cast gcdOf_pos_of_ne w 0 (hw 0).ne'
  unfold GrandReturnAt
  rw [returns_iff_gcd w t]
  refine exists_congr fun z => ?_
  rw [eq_div_iff hG.ne']
  constructor <;> intro h <;> linarith

#print axioms grandReturn_iff

/-- **All integer patterns have a grand return, and the first one is `1/G`.** -/
theorem grandReturn_isLeast (w : Fin 8 → ℤ) (hw : ∀ i, 0 < w i) :
    IsLeast {t : ℝ | 0 < t ∧ GrandReturnAt (fun i => (w i : ℝ)) t} (1 / (gcdOf w : ℝ)) := by
  have hG : (0 : ℝ) < gcdOf w := by exact_mod_cast gcdOf_pos_of_ne w 0 (hw 0).ne'
  refine ⟨⟨by positivity, (grandReturn_iff w hw _).mpr ⟨1, by simp⟩⟩, ?_⟩
  rintro t ⟨ht, hr⟩
  obtain ⟨z, rfl⟩ := (grandReturn_iff w hw t).mp hr
  have hz : 0 < z := by
    have : (0 : ℝ) < z := by
      have := div_pos_iff.mp ht
      rcases this with ⟨h, _⟩ | ⟨_, h⟩
      · exact h
      · exact absurd h (not_lt.mpr hG.le)
    exact_mod_cast this
  have : (1 : ℝ) ≤ z := by exact_mod_cast hz
  exact div_le_div_of_nonneg_right this hG.le

#print axioms grandReturn_isLeast

/-- The positive grand returns are exactly the positive multiples of `1/G`. -/
theorem grandReturn_pos_iff (w : Fin 8 → ℤ) (hw : ∀ i, 0 < w i) (t : ℝ) :
    (0 < t ∧ GrandReturnAt (fun i => (w i : ℝ)) t) ↔ ∃ n : ℕ, 0 < n ∧ t = n / (gcdOf w : ℝ) := by
  have hG : (0 : ℝ) < gcdOf w := by exact_mod_cast gcdOf_pos_of_ne w 0 (hw 0).ne'
  constructor
  · rintro ⟨ht, hr⟩
    obtain ⟨z, rfl⟩ := (grandReturn_iff w hw t).mp hr
    have hz : 0 < z := by
      have : (0 : ℝ) < z := by
        rcases div_pos_iff.mp ht with ⟨h, _⟩ | ⟨_, h⟩
        · exact h
        · exact absurd h (not_lt.mpr hG.le)
      exact_mod_cast this
    exact ⟨z.toNat, by omega, by rw [show ((z.toNat : ℕ) : ℝ) = (z : ℝ) by exact_mod_cast Int.toNat_of_nonneg hz.le]⟩
  · rintro ⟨n, hn, rfl⟩
    refine ⟨by positivity, (grandReturn_iff w hw _).mpr ⟨n, by simp⟩⟩

#print axioms grandReturn_pos_iff

/-- **The pattern repeats after exactly the grand returns (any real speeds).**  The position pattern
`t ↦ (frac (v i · t))` has period `τ` iff `τ` is a grand return: after a grand return nothing new can happen. -/
theorem positions_period_iff (v : Fin 8 → ℝ) (τ : ℝ) :
    (∀ t i, Int.fract (v i * (t + τ)) = Int.fract (v i * t)) ↔ GrandReturnAt v τ := by
  constructor
  · intro h i
    have h0 := h 0 i
    simp only [zero_add, mul_zero, Int.fract_zero] at h0
    refine ⟨⌊v i * τ⌋, ?_⟩
    have := Int.floor_add_fract (v i * τ)
    rw [h0] at this
    linarith
  · intro h t i
    obtain ⟨z, hz⟩ := h i
    rw [mul_add, hz, Int.fract_add_intCast]

#print axioms positions_period_iff

theorem distInt_eq_zero_iff (x : ℝ) : distInt x = 0 ↔ ∃ z : ℤ, x = z := by
  constructor
  · intro h
    refine ⟨round x, ?_⟩
    unfold distInt at h
    have := abs_eq_zero.mp h
    linarith
  · rintro ⟨z, rfl⟩
    exact distInt_intCast z

#print axioms distInt_eq_zero_iff

/-- **The reading pattern has period `τ` iff every `u i · τ` is a whole number.**  `u i` are the disparities of a
subject; this is the exact period of everything isolation depends on. -/
theorem readingPattern_period_iff (u : Fin 8 → ℝ) (τ : ℝ) :
    (∀ t i, distInt (u i * (t + τ)) = distInt (u i * t)) ↔ ∀ i, ∃ z : ℤ, u i * τ = z := by
  constructor
  · intro h i
    have h0 := h 0 i
    simp only [zero_add, mul_zero] at h0
    have : distInt (u i * τ) = 0 := by rw [h0]; simpa using distInt_intCast 0
    exact (distInt_eq_zero_iff _).mp this
  · intro h t i
    obtain ⟨z, hz⟩ := h i
    rw [mul_add, hz, distInt_add_int]

#print axioms readingPattern_period_iff

/-- Whole-number disparity readings: isolation of the subject at `t + τ` iff at `t`. -/
theorem isolatedAt_add_period (v : Fin 8 → ℝ) (k : Fin 8) (τ : ℝ)
    (h : ∀ i, ∃ z : ℤ, (v i - v k) * τ = z) (t : ℝ) :
    IsolatedAt v k (t + τ) ↔ IsolatedAt v k t := by
  unfold IsolatedAt
  refine forall_congr' fun i => forall_congr' fun _ => ?_
  obtain ⟨z, hz⟩ := h i
  rw [mul_add, hz, distInt_add_int]

#print axioms isolatedAt_add_period

/-- **A grand return is a period of every subject's isolation.**  If every runner is at its start at `τ`, then for
every subject `k` and every instant `t`: isolated at `t + τ` iff isolated at `t`.  (Any real speeds.) -/
theorem isolatedAt_add_grandReturn (v : Fin 8 → ℝ) (τ : ℝ) (hτ : GrandReturnAt v τ) (k : Fin 8) (t : ℝ) :
    IsolatedAt v k (t + τ) ↔ IsolatedAt v k t := by
  refine isolatedAt_add_period v k τ (fun i => ?_) t
  obtain ⟨a, ha⟩ := hτ i
  obtain ⟨b, hb⟩ := hτ k
  exact ⟨a - b, by rw [sub_mul, ha, hb]; push_cast; ring⟩

#print axioms isolatedAt_add_grandReturn

/-- The gcd of the disparities of subject `k`, for integer speeds. -/
def gcdDiff (w : Fin 8 → ℤ) (k : Fin 8) : ℤ := gcdOf (fun i => w i - w k)

theorem gcd_dvd_gcdDiff (w : Fin 8 → ℤ) (k : Fin 8) : gcdOf w ∣ gcdDiff w k :=
  dvd_gcdOf _ _ fun i => dvd_sub (gcdOf_dvd w i) (gcdOf_dvd w k)

#print axioms gcd_dvd_gcdDiff

theorem gcdDiff_pos (w : Fin 8 → ℤ) (hinj : Function.Injective w) (k : Fin 8) : 0 < gcdDiff w k := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 8, i ≠ k := by
    by_cases h : k = 0
    · exact ⟨1, by rw [h]; decide⟩
    · exact ⟨0, fun h' => h h'.symm⟩
  exact gcdOf_pos_of_ne _ i (sub_ne_zero.mpr fun h => hi (hinj h))

#print axioms gcdDiff_pos

/-- **The exact period of a subject's pattern (integer speeds).**  The reading pattern of subject `k` has period `τ`
iff `Gk · τ` is a whole number, `Gk` the gcd of its disparities.  [L] -/
theorem readingPattern_period_gcd (w : Fin 8 → ℤ) (k : Fin 8) (τ : ℝ) :
    (∀ t i, distInt (((w i : ℝ) - w k) * (t + τ)) = distInt (((w i : ℝ) - w k) * t)) ↔
      ∃ z : ℤ, (gcdDiff w k : ℝ) * τ = z := by
  rw [readingPattern_period_iff]
  have := returns_iff_gcd (fun i => w i - w k) τ
  simpa [gcdDiff] using this

#print axioms readingPattern_period_gcd

/-- The positive periods of subject `k`'s reading pattern are the positive multiples of `1/Gk`, and the least is
`1/Gk`.  [L] -/
theorem readingPattern_least_period (w : Fin 8 → ℤ) (hinj : Function.Injective w) (k : Fin 8) :
    IsLeast {τ : ℝ | 0 < τ ∧ ∀ t i, distInt (((w i : ℝ) - w k) * (t + τ)) = distInt (((w i : ℝ) - w k) * t)}
      (1 / (gcdDiff w k : ℝ)) := by
  have hG : (0 : ℝ) < gcdDiff w k := by exact_mod_cast gcdDiff_pos w hinj k
  refine ⟨⟨by positivity, (readingPattern_period_gcd w k _).mpr ⟨1, by push_cast; field_simp⟩⟩, ?_⟩
  rintro τ ⟨hτ, hp⟩
  obtain ⟨z, hz⟩ := (readingPattern_period_gcd w k τ).mp hp
  have hz1 : (0 : ℝ) < z := by rw [← hz]; positivity
  have hz2 : (1 : ℝ) ≤ z := by exact_mod_cast (show (1 : ℤ) ≤ z by exact_mod_cast hz1)
  rw [div_le_iff₀ hG]
  linarith

#print axioms readingPattern_least_period

/-- **Isolation of subject `k` is periodic with period `1/Gk`** (integer speeds, `Gk` the gcd of its disparities).
This is the cycle of the subject's isolation, `Gk` a multiple of the pattern's `G` (`gcd_dvd_gcdDiff`).  [L] -/
theorem isolatedAt_add_gcdDiff (w : Fin 8 → ℤ) (hinj : Function.Injective w) (k : Fin 8) (t : ℝ) :
    IsolatedAt (fun i => (w i : ℝ)) k (t + 1 / (gcdDiff w k : ℝ)) ↔ IsolatedAt (fun i => (w i : ℝ)) k t := by
  have hG : (0 : ℝ) < gcdDiff w k := by exact_mod_cast gcdDiff_pos w hinj k
  refine isolatedAt_add_period _ k _ (fun i => ?_) t
  have := (returns_iff_gcd (fun i => w i - w k) (1 / (gcdDiff w k : ℝ))).mpr ⟨1, by
    show (gcdDiff w k : ℝ) * (1 / (gcdDiff w k : ℝ)) = ((1 : ℤ) : ℝ)
    push_cast; field_simp⟩ i
  simpa using this

#print axioms isolatedAt_add_gcdDiff

/-! ## Part 1b: the slowest runner's rotation -/

/-- The slowest runner is back at its start at `1/m` (its own full rotation).  Trivial; recorded as the owner's cycle. -/
theorem slowest_rotation (m : ℤ) (hm : 0 < m) : ∃ z : ℤ, (m : ℝ) * (1 / (m : ℝ)) = z :=
  by
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨1, ?_⟩
  push_cast; field_simp

#print axioms slowest_rotation

/-- **When the slowest rotation is the whole pattern.**  For a runner of speed `m = w j0 > 0`: `G = m` iff `m` divides
every speed.  (With `m` the minimum this says: the slowest runner's rotation is the grand return iff the slowest speed
divides all the others.) -/
theorem gcd_eq_slowest_iff (w : Fin 8 → ℤ) (j0 : Fin 8) (hpos : 0 < w j0) :
    gcdOf w = w j0 ↔ ∀ i, w j0 ∣ w i := by
  constructor
  · intro h i; rw [← h]; exact gcdOf_dvd w i
  · intro h
    exact Int.dvd_antisymm (gcdOf_nonneg w) hpos.le (gcdOf_dvd w j0) (dvd_gcdOf w _ h)

#print axioms gcd_eq_slowest_iff

/-- The slowest runner's rotation `1/m` is a grand return iff `m` divides every speed. -/
theorem grandReturn_slowest_iff (w : Fin 8 → ℤ) (j0 : Fin 8) (hpos : 0 < w j0) :
    GrandReturnAt (fun i => (w i : ℝ)) (1 / (w j0 : ℝ)) ↔ ∀ i, w j0 ∣ w i := by
  have hm : (w j0 : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  constructor
  · intro h i
    obtain ⟨z, hz⟩ := h i
    refine ⟨z, ?_⟩
    have : (w i : ℝ) = (w j0 : ℝ) * z := by
      field_simp at hz; linarith
    exact_mod_cast this
  · intro h i
    obtain ⟨q, hq⟩ := h i
    refine ⟨q, ?_⟩
    show ((w i : ℤ) : ℝ) * (1 / (w j0 : ℝ)) = q
    rw [hq]; push_cast; field_simp

#print axioms grandReturn_slowest_iff

/-- **In general the grand return is `q = m/G` rotations of the slowest runner** (`m = w j0`, `G ∣ m`, so `q` is an
integer, `1 ≤ q`, and `q = 1` iff `m` divides every speed). -/
theorem grandReturn_eq_rotations (w : Fin 8 → ℤ) (j0 : Fin 8) (hpos : 0 < w j0) :
    ∃ q : ℤ, 1 ≤ q ∧ w j0 = gcdOf w * q ∧ 1 / (gcdOf w : ℝ) = (q : ℝ) * (1 / (w j0 : ℝ)) ∧
      (q = 1 ↔ ∀ i, w j0 ∣ w i) := by
  obtain ⟨q, hq⟩ := gcdOf_dvd w j0
  have hG : 0 < gcdOf w := gcdOf_pos_of_ne w j0 hpos.ne'
  have hq1 : 1 ≤ q := by
    by_contra hlt
    have : q ≤ 0 := by omega
    nlinarith
  refine ⟨q, hq1, hq, ?_, ?_⟩
  · have hGr : (gcdOf w : ℝ) ≠ 0 := by exact_mod_cast hG.ne'
    have hqr : (w j0 : ℝ) = gcdOf w * q := by exact_mod_cast hq
    rw [hqr]
    have hq0 : (q : ℝ) ≠ 0 := by
      intro h0; have : q = 0 := by exact_mod_cast h0
      omega
    field_simp
  · rw [← gcd_eq_slowest_iff w j0 hpos]
    constructor
    · rintro rfl; omega
    · intro h
      rw [h] at hq
      nlinarith

#print axioms grandReturn_eq_rotations

/-- The integer AP `v₀ + j d`: the slowest speed `v₀` divides all speeds iff `v₀ ∣ d`. -/
theorem ap_slowest_dvd_iff (v₀ d : ℤ) :
    (∀ j : Fin 8, v₀ ∣ v₀ + (j : ℕ) * d) ↔ v₀ ∣ d := by
  constructor
  · intro h
    have := h 1
    simpa using this
  · intro h j
    exact dvd_add (dvd_refl _) (dvd_mul_of_dvd_right h _)

#print axioms ap_slowest_dvd_iff

/-- **The AP `1,…,8`: the owner's cycle and the grand return are the same instant, `t = 1`.** -/
theorem ap18_cycles_equal :
    gcdOf (fun j : Fin 8 => 1 + ((j : ℕ) : ℤ)) = 1 ∧
      GrandReturnAt (fun j : Fin 8 => ((1 + ((j : ℕ) : ℤ) : ℤ) : ℝ)) (1 / (1 : ℝ)) := by
  have hpos : 0 < (fun j : Fin 8 => 1 + ((j : ℕ) : ℤ)) 0 := by simp
  have hall : ∀ i, (fun j : Fin 8 => 1 + ((j : ℕ) : ℤ)) 0 ∣ (fun j : Fin 8 => 1 + ((j : ℕ) : ℤ)) i := by
    intro i; simp
  refine ⟨?_, ?_⟩
  · simpa using (gcd_eq_slowest_iff (fun j : Fin 8 => 1 + ((j : ℕ) : ℤ)) 0 hpos).mpr hall
  · have := (grandReturn_slowest_iff (fun j : Fin 8 => 1 + ((j : ℕ) : ℤ)) 0 hpos).mpr hall
    simpa using this

#print axioms ap18_cycles_equal

/-- **Counterexample: the AP `3,4,…,10`.**  The slowest runner (speed 3) is back at its start at `1/3`, but runner
speed `4` is not (`4/3` is not whole): the hypothesis `3 ∣ 4` fails.  The grand return is `t = 1 = 3 · (1/3)`, three
rotations of the slowest runner, as `grandReturn_eq_rotations` predicts with `q = 3/1`. -/
theorem ap3_counter :
    ¬ GrandReturnAt (fun j : Fin 8 => ((3 + ((j : ℕ) : ℤ) : ℤ) : ℝ)) (1 / (3 : ℝ)) ∧
      gcdOf (fun j : Fin 8 => 3 + ((j : ℕ) : ℤ)) = 1 ∧
      GrandReturnAt (fun j : Fin 8 => ((3 + ((j : ℕ) : ℤ) : ℤ) : ℝ)) 1 := by
  have hpos : 0 < (fun j : Fin 8 => 3 + ((j : ℕ) : ℤ)) 0 := by simp
  have hG : gcdOf (fun j : Fin 8 => 3 + ((j : ℕ) : ℤ)) = 1 := by
    have h3 : gcdOf (fun j : Fin 8 => 3 + ((j : ℕ) : ℤ)) ∣ 3 := by simpa using gcdOf_dvd (fun j : Fin 8 => 3 + ((j : ℕ) : ℤ)) 0
    have h4 : gcdOf (fun j : Fin 8 => 3 + ((j : ℕ) : ℤ)) ∣ 4 := by simpa using gcdOf_dvd (fun j : Fin 8 => 3 + ((j : ℕ) : ℤ)) 1
    have h1 : gcdOf (fun j : Fin 8 => 3 + ((j : ℕ) : ℤ)) ∣ 1 := by
      have := dvd_sub h4 h3; norm_num at this; exact this
    exact Int.eq_one_of_dvd_one (gcdOf_nonneg _) h1
  refine ⟨?_, hG, ?_⟩
  · intro h
    have := (grandReturn_slowest_iff (fun j : Fin 8 => 3 + ((j : ℕ) : ℤ)) 0 hpos).mp (by simpa using h) 1
    revert this; decide
  · intro i
    exact ⟨3 + ((i : ℕ) : ℤ), by simp⟩

#print axioms ap3_counter

/-- **Counterexample with the three cycles distinct: the odd AP `3,5,…,17`.**  Slowest rotation `1/3`; grand return
`1` (`G = 1`); each subject's isolation period is `1/2` (`Gk = 2`: every disparity is even and neighbours differ by 2).
The cycle of the owner's definition (`1/3`), the pattern's grand return (`1`) and the isolation period (`1/2`)
are three different instants; the hypothesis that fails for the first two to agree is `3 ∣ 5`. -/
theorem ap_odd_counter :
    gcdOf (fun j : Fin 8 => 3 + 2 * ((j : ℕ) : ℤ)) = 1 ∧
      (∀ k : Fin 8, gcdDiff (fun j : Fin 8 => 3 + 2 * ((j : ℕ) : ℤ)) k = 2) ∧
      ¬ GrandReturnAt (fun j : Fin 8 => ((3 + 2 * ((j : ℕ) : ℤ) : ℤ) : ℝ)) (1 / (3 : ℝ)) := by
  have hpos : 0 < (fun j : Fin 8 => 3 + 2 * ((j : ℕ) : ℤ)) 0 := by simp
  refine ⟨?_, ?_, ?_⟩
  · have h3 : gcdOf (fun j : Fin 8 => 3 + 2 * ((j : ℕ) : ℤ)) ∣ 3 := by
      simpa using gcdOf_dvd (fun j : Fin 8 => 3 + 2 * ((j : ℕ) : ℤ)) 0
    have h5 : gcdOf (fun j : Fin 8 => 3 + 2 * ((j : ℕ) : ℤ)) ∣ 5 := by
      simpa using gcdOf_dvd (fun j : Fin 8 => 3 + 2 * ((j : ℕ) : ℤ)) 1
    have h1 : gcdOf (fun j : Fin 8 => 3 + 2 * ((j : ℕ) : ℤ)) ∣ 1 := by
      have := dvd_sub (dvd_mul_of_dvd_right h3 2) h5
      norm_num at this
      exact this
    exact Int.eq_one_of_dvd_one (gcdOf_nonneg _) h1
  · intro k
    unfold gcdDiff
    apply Int.dvd_antisymm (gcdOf_nonneg _) (by norm_num)
    · have hk := k.isLt
      obtain ⟨i, hi⟩ : ∃ i : Fin 8, (i : ℕ) = if (k : ℕ) = 0 then 1 else (k : ℕ) - 1 := by
        exact ⟨⟨if (k : ℕ) = 0 then 1 else (k : ℕ) - 1, by split_ifs <;> omega⟩, rfl⟩
      have := gcdOf_dvd (fun j : Fin 8 => (3 + 2 * ((j : ℕ) : ℤ)) - (3 + 2 * ((k : ℕ) : ℤ))) i
      have hv : (3 + 2 * ((i : ℕ) : ℤ)) - (3 + 2 * ((k : ℕ) : ℤ)) = 2 * (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) := by ring
      simp only [hv] at this
      have hne : ((i : ℕ) : ℤ) - ((k : ℕ) : ℤ) = 1 ∨ ((i : ℕ) : ℤ) - ((k : ℕ) : ℤ) = -1 := by
        split_ifs at hi <;> omega
      rcases hne with h | h <;> simpa [h] using this
    · apply dvd_gcdOf
      intro i
      exact ⟨(i : ℕ) - (k : ℕ), by push_cast; ring⟩
  · intro h
    have := (grandReturn_slowest_iff (fun j : Fin 8 => 3 + 2 * ((j : ℕ) : ℤ)) 0 hpos).mp (by simpa using h) 1
    revert this; decide

#print axioms ap_odd_counter

/-- **The AP `1,…,8` has exactly four global isolations in its cycle `(0, 1]`**, at `1/8, 3/8, 5/8, 7/8`, and none at
the grand return `t = 1`.  (Wrapper over `ap_globalIsolation_iff`.) -/
theorem ap18_four_before_return (v : Fin 8 → ℝ) (hv : ∀ j : Fin 8, v j = 1 + ((j : ℕ) : ℝ) * 1) (t : ℝ) :
    (0 < t ∧ t ≤ 1 ∧ GloballyIsolatedAt v t) ↔ t = 1 / 8 ∨ t = 3 / 8 ∨ t = 5 / 8 ∨ t = 7 / 8 := by
  rw [ap_globalIsolation_iff v 1 1 one_pos hv t]
  constructor
  · rintro ⟨h0, h1, a, ha, rfl⟩
    have hodd : Odd a := by
      by_contra hne
      rw [Int.not_odd_iff_even] at hne
      obtain ⟨b, rfl⟩ := hne
      have h2 : IsCoprime (2 : ℤ) 8 := by
        have : IsCoprime (b + b) 8 := ha
        rw [← two_mul] at this
        exact this.of_mul_left_left
      rw [Int.isCoprime_iff_gcd_eq_one] at h2
      revert h2; decide
    have ha0 : 0 < a := by
      have : (0 : ℝ) < a := by
        exact (div_pos_iff_of_pos_right (by norm_num : (0 : ℝ) < 8 * 1)).mp h0
      exact_mod_cast this
    have ha8 : a ≤ 8 := by
      have : (a : ℝ) / (8 * 1) ≤ 1 := h1
      have : (a : ℝ) ≤ 8 := by linarith
      exact_mod_cast this
    obtain ⟨b, hb⟩ := hodd
    have : a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> norm_num
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨by norm_num, by norm_num, 1, isCoprime_one_left, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, 3, by
        rw [Int.isCoprime_iff_gcd_eq_one]; decide, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, 5, by
        rw [Int.isCoprime_iff_gcd_eq_one]; decide, by norm_num⟩
    · exact ⟨by norm_num, by norm_num, 7, by
        rw [Int.isCoprime_iff_gcd_eq_one]; decide, by norm_num⟩

#print axioms ap18_four_before_return


/-! ## Part 2: real speeds have no grand return unless all speeds are commensurable -/

/-- **Two incommensurable quantities have no common return.**  If `x` is not a rational multiple of `y ≠ 0`, no
`τ ≠ 0` makes both `x τ` and `y τ` whole numbers.  (This is the whole content of "no grand return".) -/
theorem no_period_of_incommensurable (x y : ℝ) (hy : y ≠ 0) (hinc : ∀ q : ℚ, x ≠ q * y) (τ : ℝ) (hτ : τ ≠ 0) :
    ¬ ((∃ a : ℤ, x * τ = a) ∧ (∃ b : ℤ, y * τ = b)) := by
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have hb0 : (b : ℝ) ≠ 0 := by rw [← hb]; exact mul_ne_zero hy hτ
  apply hinc ((a : ℚ) / b)
  have : x = (a : ℝ) / τ := by field_simp; linarith
  have h2 : y = (b : ℝ) / τ := by field_simp; linarith
  rw [this, h2]
  push_cast
  field_simp

#print axioms no_period_of_incommensurable

/-- If two speeds are incommensurable, the position pattern has no period `τ ≠ 0`. -/
theorem no_positions_period (v : Fin 8 → ℝ) (i j : Fin 8) (hy : v j ≠ 0) (hinc : ∀ q : ℚ, v i ≠ q * v j)
    (τ : ℝ) (hτ : τ ≠ 0) : ¬ (∀ t l, Int.fract (v l * (t + τ)) = Int.fract (v l * t)) := by
  intro h
  have hr := (positions_period_iff v τ).mp h
  exact no_period_of_incommensurable (v i) (v j) hy hinc τ hτ ⟨hr i, hr j⟩

#print axioms no_positions_period

/-- If two disparities of a subject are incommensurable, its reading pattern has no period `τ ≠ 0`. -/
theorem no_reading_period (v : Fin 8 → ℝ) (k i j : Fin 8) (hy : v j - v k ≠ 0)
    (hinc : ∀ q : ℚ, v i - v k ≠ q * (v j - v k)) (τ : ℝ) (hτ : τ ≠ 0) :
    ¬ (∀ t l, distInt ((v l - v k) * (t + τ)) = distInt ((v l - v k) * t)) := by
  intro h
  have hr := (readingPattern_period_iff (fun l => v l - v k) τ).mp h
  exact no_period_of_incommensurable _ _ hy hinc τ hτ ⟨hr i, hr j⟩

#print axioms no_reading_period

/-- **A grand return exists exactly when all speeds are pairwise commensurable.**  (Positive real speeds.)
Integer speeds are the case of rational ratios; this is why "all integer patterns have a grand return" and why a
real-valued arrangement in general has none. -/
theorem exists_grandReturn_iff (v : Fin 8 → ℝ) (hv : ∀ i, 0 < v i) :
    (∃ t : ℝ, 0 < t ∧ GrandReturnAt v t) ↔ ∀ i j, ∃ q : ℚ, v i = q * v j := by
  constructor
  · rintro ⟨t, ht, hr⟩ i j
    obtain ⟨a, ha⟩ := hr i
    obtain ⟨b, hb⟩ := hr j
    have hb0 : (b : ℝ) ≠ 0 := by rw [← hb]; exact (mul_pos (hv j) ht).ne'
    refine ⟨(a : ℚ) / b, ?_⟩
    have h1 : v i = (a : ℝ) / t := by field_simp; linarith
    have h2 : v j = (b : ℝ) / t := by field_simp; linarith
    rw [h1, h2]; push_cast; field_simp
  · intro h
    choose q hq using fun i => h i 0
    set L : ℕ := ∏ i, (q i).den with hL
    have hLpos : 0 < L := Finset.prod_pos fun i _ => (q i).den_pos
    have hv0 : v 0 ≠ 0 := (hv 0).ne'
    refine ⟨(L : ℝ) / v 0, by have := hv 0; positivity, fun i => ?_⟩
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun i => (q i).den) (Finset.mem_univ i)
    refine ⟨(q i).num * r, ?_⟩
    have hden : ((q i).den : ℝ) ≠ 0 := by exact_mod_cast (q i).den_nz
    have hLr : (L : ℝ) = ((q i).den : ℝ) * (r : ℝ) := by exact_mod_cast hr
    rw [hq i, Rat.cast_def, hLr]
    push_cast
    field_simp

#print axioms exists_grandReturn_iff

/-- **A real-valued arrangement with no grand return, and no period of its position pattern.**  Speeds
`1, √2, 3, 4, …, 8`: positive, pairwise distinct, `√2` not a rational multiple of `1`. -/
theorem sqrt2_no_grandReturn :
    let v : Fin 8 → ℝ := fun i => if i = 1 then Real.sqrt 2 else ((i : ℕ) : ℝ) + 1
    IsArrangement v ∧ (¬ ∃ t : ℝ, 0 < t ∧ GrandReturnAt v t) ∧
      ∀ τ : ℝ, τ ≠ 0 → ¬ (∀ t l, Int.fract (v l * (t + τ)) = Int.fract (v l * t)) := by
  intro v
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h2 : Real.sqrt 2 < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hpos : ∀ i, 0 < v i := by
    intro i
    simp only [v]
    split_ifs
    · linarith
    · positivity
  have hinc : ∀ q : ℚ, v 1 ≠ q * v 0 := by
    intro q hq
    simp only [v] at hq
    simp at hq
    exact irrational_sqrt_two ⟨q, by simpa using hq.symm⟩
  refine ⟨⟨hpos, ?_⟩, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [v] at hij ⊢ <;> linarith
  · intro ⟨t, ht, hr⟩
    have := (exists_grandReturn_iff v hpos).mp ⟨t, ht, hr⟩ 1 0
    obtain ⟨q, hq⟩ := this
    exact hinc q hq
  · intro τ hτ
    exact no_positions_period v 1 0 (hpos 0).ne' hinc τ hτ

#print axioms sqrt2_no_grandReturn

/-! ## Part 3: D_min between grids -- the exact displacement of every reading -/

/-- **Exact displacement of readings.**  Whatever two arrangements `v`, `v'`, the reading of runner `i` against
subject `k` at instant `t` moves by the difference of the two speed changes times `t`. -/
theorem reading_displacement (v v' : Fin 8 → ℝ) (k i : Fin 8) (t : ℝ) :
    (v' i - v' k) * t = (v i - v k) * t + ((v' i - v i) - (v' k - v k)) * t := by ring

#print axioms reading_displacement

/-- One speed changed, the rest frozen: the displacement of the reading of `i` against `k` is `δ t` if `i` is the
changed runner, `-δ t` if `k` is, `0` otherwise (and `0` if both).  So frozen pairs keep their readings exactly
(owner: freezing some runners and moving the others does not change the isolation point of the frozen ones). -/
theorem reading_update (v : Fin 8 → ℝ) (m : Fin 8) (δ : ℝ) (k i : Fin 8) (t : ℝ) :
    (Function.update v m (v m + δ) i - Function.update v m (v m + δ) k) * t
      = (v i - v k) * t + ((if i = m then δ else 0) - (if k = m then δ else 0)) * t := by
  by_cases hi : i = m <;> by_cases hk : k = m <;> simp [Function.update, hi, hk] <;> ring

#print axioms reading_update

/-- The same, in the subject's `d_min` unit: if `m ≠ 0` (a disparity of the subject, `d_min` in the cascade) then the
displacement `δ t` equals `(δ / m) · (m t)`; `m t` is the coordinate `u = d_min · t` of the cascade. -/
theorem displacement_dmin_units (δ t m : ℝ) (hm : m ≠ 0) : δ * t = (δ / m) * (m * t) := by
  field_simp

#print axioms displacement_dmin_units

/-- **Single-runner change, at the instant `a/(8d)` (exact; no grid hypothesis is needed for the identity).**  Runner `m` moves by `c`
grid steps (`c` any integer: `c = ±1` is the next grid speed).  At `t = a/(8d)` the reading of `i` against `k` is
displaced by exactly `([i = m] - [k = m]) · c · a` eighths of a lap. -/
theorem single_change_reading (v v' : Fin 8 → ℝ) (d : ℝ) (hd : 0 < d) (m : Fin 8) (c : ℤ)
    (hv' : ∀ j, v' j = v j + (if j = m then (c : ℝ) * d else 0)) (a : ℤ) (k i : Fin 8) :
    (v' i - v' k) * ((a : ℝ) / (8 * d))
      = (v i - v k) * ((a : ℝ) / (8 * d))
        + ((((if i = m then c else 0) - (if k = m then c else 0)) * a : ℤ) : ℝ) / 8 := by
  have hd0 : d ≠ 0 := hd.ne'
  rw [hv' i, hv' k]
  by_cases hi : i = m <;> by_cases hk : k = m <;> simp [hi, hk] <;> field_simp <;> ring

#print axioms single_change_reading

/-- Value of a grid reading at the grid instant: `(idx i - idx k) · a` eighths of a lap. -/
theorem grid_reading_value (v : Fin 8 → ℝ) (d v₀ : ℝ) (hd : 0 < d) (idx : Fin 8 → ℤ)
    (hv : ∀ j, v j = v₀ + (idx j : ℝ) * d) (a : ℤ) (k i : Fin 8) :
    (v i - v k) * ((a : ℝ) / (8 * d)) = (((idx i - idx k) * a : ℤ) : ℝ) / 8 := by
  have hd0 : d ≠ 0 := hd.ne'
  rw [hv i, hv k]; push_cast; field_simp; ring

#print axioms grid_reading_value

/-- **Grid to grid (any number of runners changed, same step `d`).**  If `v` has indices `idx` and `v'` has indices
`idx'`, then at `t = a/(8d)` every reading is displaced by exactly `((Δ i - Δ k) · a)/8` laps, `Δ = idx' - idx`.  A
reading is unchanged modulo laps iff `8 ∣ (Δ i - Δ k) a`. -/
theorem grid_reading_shift (v v' : Fin 8 → ℝ) (d v₀ v₀' : ℝ) (hd : 0 < d) (idx idx' : Fin 8 → ℤ)
    (hv : ∀ j, v j = v₀ + (idx j : ℝ) * d) (hv' : ∀ j, v' j = v₀' + (idx' j : ℝ) * d) (a : ℤ) (k i : Fin 8) :
    (v' i - v' k) * ((a : ℝ) / (8 * d))
      = (v i - v k) * ((a : ℝ) / (8 * d))
        + (((((idx' i - idx i) - (idx' k - idx k)) * a : ℤ)) : ℝ) / 8 := by
  rw [grid_reading_value v' d v₀' hd idx' hv', grid_reading_value v d v₀ hd idx hv]
  push_cast; ring

#print axioms grid_reading_shift

/-- A whole number of eighths times a unit is divisible by 8 exactly when the number is. -/
theorem eight_dvd_mul_unit {x a : ℤ} (ha : IsCoprime a 8) : (8 : ℤ) ∣ x * a ↔ (8 : ℤ) ∣ x :=
  ⟨fun h => ha.symm.dvd_of_dvd_mul_right h, fun h => dvd_mul_of_dvd_left h a⟩

#print axioms eight_dvd_mul_unit

/-- **Isolation criterion for a grid at its grid instant.**  Subject `k` of the arrangement `v j = v₀ + idx j · d`
(`idx` any integers) is isolated at `a/(8d)`, `a` a unit, iff no other index is congruent to `idx k` mod 8. -/
theorem isolatedAt_grid_iff (v : Fin 8 → ℝ) (d v₀ : ℝ) (hd : 0 < d) (idx : Fin 8 → ℤ)
    (hv : ∀ j, v j = v₀ + (idx j : ℝ) * d) (a : ℤ) (ha : IsCoprime a 8) (k : Fin 8) :
    IsolatedAt v k ((a : ℝ) / (8 * d)) ↔ ∀ i, i ≠ k → ¬ (8 : ℤ) ∣ idx i - idx k := by
  unfold IsolatedAt
  refine forall_congr' fun i => forall_congr' fun _ => ?_
  rw [grid_reading_value v d v₀ hd idx hv a k i]
  by_cases h : (8 : ℤ) ∣ idx i - idx k
  · have h8 : (8 : ℤ) ∣ (idx i - idx k) * a := dvd_mul_of_dvd_left h a
    rw [distInt_int_div_eight_of_dvd h8]
    simp [h]
  · have h8 : ¬ (8 : ℤ) ∣ (idx i - idx k) * a := fun h' => h ((eight_dvd_mul_unit ha).mp h')
    simp only [h, not_false_eq_true, iff_true]
    exact distInt_int_div_eight h8

#print axioms isolatedAt_grid_iff

/-- A complete residue system has pairwise non-congruent indices. -/
theorem complete_ne {idx : Fin 8 → ℤ} (h : CompleteResidues idx) {i j : Fin 8} (hij : i ≠ j) :
    ¬ (8 : ℤ) ∣ idx i - idx j := by
  intro hd
  apply hij
  apply h
  exact (Int.modEq_iff_dvd.mpr hd).symm

#print axioms complete_ne

/-- **[PROVISIONAL: counting tool]** supports `exists_index_congruent`: an injective map `Fin 8 → ZMod 8` is onto. -/
theorem exists_index_congruent {idx : Fin 8 → ℤ} (h : CompleteResidues idx) (r : ℤ) :
    ∃ j : Fin 8, (8 : ℤ) ∣ r - idx j := by
  let f : Fin 8 → ZMod 8 := fun j => (idx j : ZMod 8)
  have hinj : Function.Injective f := by
    intro j j' hjj
    apply h
    have := (ZMod.intCast_eq_intCast_iff (idx j) (idx j') 8).mp hjj
    exact this
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by simp⟩
  obtain ⟨j, hj⟩ := hbij.2 (r : ZMod 8)
  refine ⟨j, ?_⟩
  have := (ZMod.intCast_eq_intCast_iff (idx j) r 8).mp hj
  exact Int.modEq_iff_dvd.mp this

#print axioms exists_index_congruent


/-! ## Part 3b: what a one-step change does to each subject's isolation at the old instant -/

/-- The shifted indices when runner `m` moves `c` grid steps. -/
def shiftIdx (idx : Fin 8 → ℤ) (m : Fin 8) (c : ℤ) : Fin 8 → ℤ := fun j => idx j + (if j = m then c else 0)

/-- **Subject `k ≠ m` at the old instant after runner `m` moves `c` steps.**  Isolated iff the new residue of `m`
differs from the residue of `k`.  Every other subject-pair is frozen and keeps its reading exactly. -/
theorem single_change_other (v' : Fin 8 → ℝ) (d v₀ : ℝ) (hd : 0 < d) (idx : Fin 8 → ℤ)
    (hidx : CompleteResidues idx) (m : Fin 8) (c : ℤ)
    (hv' : ∀ j, v' j = v₀ + (shiftIdx idx m c j : ℝ) * d) (a : ℤ) (ha : IsCoprime a 8) (k : Fin 8) (hk : k ≠ m) :
    IsolatedAt v' k ((a : ℝ) / (8 * d)) ↔ ¬ (8 : ℤ) ∣ idx m + c - idx k := by
  rw [isolatedAt_grid_iff v' d v₀ hd (shiftIdx idx m c) hv' a ha k]
  constructor
  · intro h
    have := h m (Ne.symm hk)
    simpa [shiftIdx, hk] using this
  · intro h i hi
    by_cases him : i = m
    · subst him; simpa [shiftIdx, hk] using h
    · simpa [shiftIdx, him, hk] using complete_ne hidx hi

#print axioms single_change_other

/-- **The moved subject `m` at the old instant.**  Isolated iff its new residue differs from every other runner's. -/
theorem single_change_self (v' : Fin 8 → ℝ) (d v₀ : ℝ) (hd : 0 < d) (idx : Fin 8 → ℤ)
    (m : Fin 8) (c : ℤ)
    (hv' : ∀ j, v' j = v₀ + (shiftIdx idx m c j : ℝ) * d) (a : ℤ) (ha : IsCoprime a 8) :
    IsolatedAt v' m ((a : ℝ) / (8 * d)) ↔ ∀ i, i ≠ m → ¬ (8 : ℤ) ∣ idx i - (idx m + c) := by
  rw [isolatedAt_grid_iff v' d v₀ hd (shiftIdx idx m c) hv' a ha m]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  simp [shiftIdx, hi]

#print axioms single_change_self

/-- **Who loses the old instant (exact).**  Grid indices `idx` (complete residues), runner `m` moved `c` steps with
`8 ∤ c`.  Then there is exactly one other runner `j` whose residue the new index of `m` lands on
(**[PROVISIONAL: counting tool]**, `exists_index_congruent`: some index has the residue), and the subjects that are
NOT isolated at `a/(8d)` any more are exactly `m` and `j`.  The other six keep their isolation at the old instant.
No statement is made about where `m` and `j` are isolated instead. -/
theorem single_change_losers (v' : Fin 8 → ℝ) (d v₀ : ℝ) (hd : 0 < d) (idx : Fin 8 → ℤ)
    (hidx : CompleteResidues idx) (m : Fin 8) (c : ℤ) (hc : ¬ (8 : ℤ) ∣ c)
    (hv' : ∀ j, v' j = v₀ + (shiftIdx idx m c j : ℝ) * d) (a : ℤ) (ha : IsCoprime a 8) :
    ∃ j : Fin 8, j ≠ m ∧ (8 : ℤ) ∣ idx m + c - idx j ∧
      ∀ k, ¬ IsolatedAt v' k ((a : ℝ) / (8 * d)) ↔ (k = m ∨ k = j) := by
  obtain ⟨j, hj⟩ := exists_index_congruent hidx (idx m + c)
  have hjm : j ≠ m := by
    rintro rfl
    apply hc
    have e : idx j + c - idx j = c := by ring
    rwa [e] at hj
  refine ⟨j, hjm, hj, fun k => ?_⟩
  by_cases hk : k = m
  · subst hk
    simp only [true_or, iff_true]
    rw [single_change_self v' d v₀ hd idx k c hv' a ha]
    intro h
    apply h j hjm
    have e : idx j - (idx k + c) = -(idx k + c - idx j) := by ring
    rw [e]; exact (dvd_neg).mpr hj
  · rw [single_change_other v' d v₀ hd idx hidx m c hv' a ha k hk, not_not]
    constructor
    · intro h
      right
      by_contra hkj
      apply complete_ne hidx (Ne.symm hkj)
      have e : idx j - idx k = (idx m + c - idx k) - (idx m + c - idx j) := by ring
      rw [e]; exact dvd_sub h hj
    · rintro (h | rfl)
      · exact absurd h hk
      · exact hj

#print axioms single_change_losers

/-- **The D_max shift is the only single-runner change that keeps every isolation at the old instant.**  With
the same hypotheses and `c` any integer: every subject is isolated at `a/(8d)` iff `8 ∣ c`. -/
theorem single_change_all_iff (v' : Fin 8 → ℝ) (d v₀ : ℝ) (hd : 0 < d) (idx : Fin 8 → ℤ)
    (hidx : CompleteResidues idx) (m : Fin 8) (c : ℤ)
    (hv' : ∀ j, v' j = v₀ + (shiftIdx idx m c j : ℝ) * d) (a : ℤ) (ha : IsCoprime a 8) :
    (∀ k, IsolatedAt v' k ((a : ℝ) / (8 * d))) ↔ (8 : ℤ) ∣ c := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨j, hjm, -, hl⟩ := single_change_losers v' d v₀ hd idx hidx m c hc hv' a ha
    exact (hl m).mpr (Or.inl rfl) (h m)
  · intro hc k
    by_cases hk : k = m
    · subst hk
      rw [single_change_self v' d v₀ hd idx k c hv' a ha]
      intro i hi h
      apply complete_ne hidx hi
      have e : idx i - idx k = (idx i - (idx k + c)) + c := by ring
      rw [e]; exact dvd_add h hc
    · rw [single_change_other v' d v₀ hd idx hidx m c hv' a ha k hk]
      intro h
      apply complete_ne hidx (Ne.symm hk)
      have e : idx m - idx k = (idx m + c - idx k) - c := by ring
      rw [e]; exact dvd_sub h hc

#print axioms single_change_all_iff

/-- A single-runner change keeps the residues a complete system iff it is a D_max shift (`8 ∣ c`): grid to grid by
moving one speed is possible only as a multiple of 8 grid steps; any other single step leaves the grid, and the
isolation at the old instant is displaced (`single_change_losers`). -/
theorem shiftIdx_complete_iff (idx : Fin 8 → ℤ) (hidx : CompleteResidues idx) (m : Fin 8) (c : ℤ) :
    CompleteResidues (shiftIdx idx m c) ↔ (8 : ℤ) ∣ c := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨j, hjm, hj, -⟩ := single_change_losers (fun j => (shiftIdx idx m c j : ℝ)) 1 0 one_pos idx hidx m c hc
      (fun j => by simp) 1 isCoprime_one_left
    have := h (j := m) (j' := j) (by
      have e : shiftIdx idx m c m % 8 = shiftIdx idx m c j % 8 := by
        have h1 : shiftIdx idx m c m = idx m + c := by simp [shiftIdx]
        have h2 : shiftIdx idx m c j = idx j := by simp [shiftIdx, hjm]
        rw [h1, h2]
        exact (Int.modEq_iff_dvd.mpr hj).symm
      exact e)
    exact hjm this.symm
  · intro hc
    obtain ⟨b, hb⟩ := hc
    have := dmax_complete idx (fun j => if j = m then b else 0) hidx
    convert this using 1
    funext j
    by_cases hj : j = m <;> simp [shiftIdx, hj, hb]

#print axioms shiftIdx_complete_iff

end Cycle

end Fresh
