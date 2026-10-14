import LonelyRunner.LRC.Spec.CascadeTransportN

/-!
# Exact drift of a repeated captured pair

Extracted from exact boundary perturbations, not a global termination assertion.
At the lap-K opening of a, b is captured on lap L precisely when its depth is
strictly between zero and two eighths. Repeating lap advances (r,s) changes that
depth by the constant 8*(s-r*b/a). Nonzero drift permits only finitely many such
repetitions. Zero drift means commensurability a*s=b*r, NOT equal speeds.
The possibility of changing the pair or the lap-advance pattern remains open.
-/

namespace LRC.HandoffDrift

noncomputable def depth8 (a b : ℝ) (K L : ℤ) : ℝ :=
  8 * (L : ℝ) + 1 - (8 * (K : ℝ) + 1) * (b / a)

/-- A specified blocking lap at an opening is exactly the depth interval (0,2). -/
theorem captured_iff_depth {a b : ℝ} {K L : ℤ} :
    |b * (((K : ℝ) + (8 : ℝ)⁻¹) / a) - L| < (8 : ℝ)⁻¹ ↔
      0 < depth8 a b K L ∧ depth8 a b K L < 2 := by
  have he : depth8 a b K L =
      1 - 8 * (b * (((K : ℝ) + (8 : ℝ)⁻¹) / a) - L) := by
    unfold depth8
    norm_num
    ring
  rw [he, abs_lt]
  norm_num
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- All captured-pair boundaries are homogeneous linear equalities in the speeds. -/
theorem depth_mul {a b : ℝ} (ha : a ≠ 0) (K L : ℤ) :
    depth8 a b K L * a = (8 * (L : ℝ) + 1) * a - (8 * (K : ℝ) + 1) * b := by
  unfold depth8
  field_simp

/-- The strict linear inequalities used by the exact perturbation tracer. Equality is
clear, so the two boundary faces must be checked separately from their open cells. -/
theorem captured_iff_linear {a b : ℝ} (ha : 0 < a) (K L : ℤ) :
    |b * (((K : ℝ) + (8 : ℝ)⁻¹) / a) - L| < (8 : ℝ)⁻¹ ↔
      (8 * (L : ℝ) - 1) * a < (8 * (K : ℝ) + 1) * b ∧
      (8 * (K : ℝ) + 1) * b < (8 * (L : ℝ) + 1) * a := by
  rw [captured_iff_depth]
  have he := depth_mul (b := b) ha.ne' K L
  constructor
  · intro h
    have hp := mul_pos h.1 ha
    have hu := mul_lt_mul_of_pos_right h.2 ha
    constructor <;> nlinarith [he]
  · intro h
    have hp : 0 < depth8 a b K L * a := by nlinarith [he, h.2]
    have hu : depth8 a b K L * a < 2 * a := by nlinarith [he, h.1]
    exact ⟨(mul_pos_iff_of_pos_right ha).mp hp, lt_of_mul_lt_mul_right hu ha.le⟩

/-- Exact drift under an arbitrary number of repeats of the same lap-advance pattern. -/
theorem depth_repeat (a b : ℝ) (K L r s : ℤ) (q : ℕ) :
    depth8 a b (K + (q : ℤ) * r) (L + (q : ℤ) * s) =
      depth8 a b K L + (q : ℝ) * (8 * ((s : ℝ) - r * (b / a))) := by
  unfold depth8
  push_cast
  ring

/-- The exceptional zero-drift condition retains the lap advances as well as the speeds. -/
theorem zero_drift_iff {a b : ℝ} (ha : a ≠ 0) (r s : ℤ) :
    8 * ((s : ℝ) - r * (b / a)) = 0 ↔ (s : ℝ) * a = (r : ℝ) * b := by
  have he : (8 * ((s : ℝ) - r * (b / a))) * a =
      8 * ((s : ℝ) * a - (r : ℝ) * b) := by
    field_simp
  constructor
  · intro h
    rw [h, zero_mul] at he
    linarith
  · intro h
    rw [h, sub_self, mul_zero] at he
    exact (mul_eq_zero.mp he).resolve_right ha

/-- Two captures with the same repeated lap increment bound the total accumulated drift.
This excludes sufficiently many repetitions whenever the drift is nonzero. -/
theorem repeated_capture_bounds_drift {a b : ℝ} {K L r s : ℤ} {q : ℕ}
    (h0 : 0 < depth8 a b K L ∧ depth8 a b K L < 2)
    (hq : 0 < depth8 a b (K + (q : ℤ) * r) (L + (q : ℤ) * s) ∧
      depth8 a b (K + (q : ℤ) * r) (L + (q : ℤ) * s) < 2) :
    |(q : ℝ) * (8 * ((s : ℝ) - r * (b / a)))| < 2 := by
  rw [depth_repeat] at hq
  rw [abs_lt]
  constructor <;> linarith [h0.1, h0.2, hq.1, hq.2]

/-- Perpetual repetition of one lap-advance pattern forces zero drift. This conclusion
allows distinct commensurate speeds and must not be mistaken for global termination. -/
theorem perpetual_pattern_zero_drift {a b : ℝ} {K L r s : ℤ}
    (h : ∀ q : ℕ,
      0 < depth8 a b (K + (q : ℤ) * r) (L + (q : ℤ) * s) ∧
      depth8 a b (K + (q : ℤ) * r) (L + (q : ℤ) * s) < 2) :
    8 * ((s : ℝ) - r * (b / a)) = 0 := by
  let D := 8 * ((s : ℝ) - r * (b / a))
  have h0 : 0 < depth8 a b K L ∧ depth8 a b K L < 2 := by
    simpa using h 0
  have hb : ∀ q : ℕ, |(q : ℝ) * D| < 2 := fun q =>
    repeated_capture_bounds_drift h0 (h q)
  by_contra hn
  have hp : 0 < |D| := abs_pos.mpr hn
  obtain ⟨q, hq⟩ := exists_nat_gt (2 / |D|)
  have hg : 2 < (q : ℝ) * |D| := (div_lt_iff₀ hp).mp hq
  have hh := hb q
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg q)] at hh
  linarith

/-- Distinct speeds can have zero drift: these are recurring capture opportunities,
not an assertion that the cascade travels between them without stopping. -/
theorem distinct_pair_recurring_capture (q : ℕ) :
    0 < depth8 7 8 (6 + (q : ℤ) * 7) (7 + (q : ℤ) * 8) ∧
      depth8 7 8 (6 + (q : ℤ) * 7) (7 + (q : ℤ) * 8) < 2 := by
  rw [depth_repeat]
  norm_num [depth8]

end LRC.HandoffDrift
