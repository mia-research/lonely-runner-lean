import LonelyRunner.LRC.Spec.WindowPinchN

/-!
# Symbolic transport conditions at an AP-deformation pinch

A fixed lap vector gives affine slacks along an ordered speed deformation.
At the zero of an old slack, the sign of a new slack is decided by a linear
expression in the target slacks. This eliminates the deformation parameter.
It does NOT assert that a suitable new lap vector always exists.
-/

namespace LRC.SymbolicWindowTransport

variable {ι : Type*}

/-- A slack positive at the AP and negative at the target pinches strictly
inside the deformation interval. -/
theorem pinch_interior {A E : ℝ} (hA : 0 < A) (hE : E < 0) :
    0 < A / (A - E) ∧ A / (A - E) < 1 := by
  have hD : 0 < A - E := by linarith
  constructor
  · exact div_pos hA hD
  · rw [div_lt_one hD]
    linarith

/-- Clearing the positive pinch denominator cancels the product of AP slacks.
Since A and C are fixed by lap labels and the AP, A*G-C*E is linear in target
speeds, not a quadratic or a sampled condition. -/
theorem slack_at_pinch {A E C G : ℝ} (hD : A - E ≠ 0) :
    (A - E) * ((1 - A / (A - E)) * C + (A / (A - E)) * G) =
      A * G - C * E := by
  field_simp
  <;> ring

/-- Exact, inclusive boundary test for a replacement slack. -/
theorem slack_at_pinch_iff {A E C G : ℝ} (hD : 0 < A - E) :
    0 ≤ (1 - A / (A - E)) * C + (A / (A - E)) * G ↔
      0 ≤ A * G - C * E := by
  rw [← slack_at_pinch (ne_of_gt hD)]
  exact (mul_nonneg_iff_of_pos_left hD).symm

/-- Positive overlap margin, with the same linear target-speed test. -/
theorem slack_at_pinch_pos_iff {A E C G : ℝ} (hD : 0 < A - E) :
    0 < (1 - A / (A - E)) * C + (A / (A - E)) * G ↔
      0 < A * G - C * E := by
  rw [← slack_at_pinch (ne_of_gt hD)]
  exact (mul_pos_iff_of_pos_left hD).symm

/-- Comparing two pinch locations also remains linear in target slacks. -/
theorem pinch_order_iff {A E C G : ℝ}
    (hD : 0 < A - E) (hF : 0 < C - G) :
    A / (A - E) ≤ C / (C - G) ↔ 0 ≤ A * G - C * E := by
  rw [div_le_div_iff₀ hD hF]
  constructor <;> intro h <;> nlinarith

/-- Two endpoint inequalities establish every intermediate real parameter.
No mesh or continuity heuristic is involved. -/
theorem affine_nonneg_between {C G l r s : ℝ} (hls : l ≤ s) (hsr : s ≤ r)
    (hl : 0 ≤ (1 - l) * C + l * G)
    (hr : 0 ≤ (1 - r) * C + r * G) :
    0 ≤ (1 - s) * C + s * G := by
  by_cases h : 0 ≤ G - C
  · nlinarith [mul_nonneg (sub_nonneg.mpr hls) h]
  · have h' : G - C ≤ 0 := le_of_lt (lt_of_not_ge h)
    nlinarith [mul_nonneg (sub_nonneg.mpr hsr) (neg_nonneg.mpr h')]

/-- The same two-endpoint principle applied to every lap-window constraint. -/
theorem lap_inequalities_between (S : Finset ι) (a d : ι → ℝ) (q : ι → ℤ)
    {l r s : ℝ} (hls : l ≤ s) (hsr : s ≤ r)
    (hl : ∀ i ∈ S, ∀ j ∈ S,
      (8 * (q i : ℝ) + 1) * ((1-l)*a j+l*d j) ≤
        (8 * (q j : ℝ) + 7) * ((1-l)*a i+l*d i))
    (hr : ∀ i ∈ S, ∀ j ∈ S,
      (8 * (q i : ℝ) + 1) * ((1-r)*a j+r*d j) ≤
        (8 * (q j : ℝ) + 7) * ((1-r)*a i+r*d i)) :
    ∀ i ∈ S, ∀ j ∈ S,
      (8 * (q i : ℝ) + 1) * ((1-s)*a j+s*d j) ≤
        (8 * (q j : ℝ) + 7) * ((1-s)*a i+s*d i) := by
  intro i hi j hj
  have h := affine_nonneg_between (C :=
    (8 * (q j : ℝ) + 7)*a i-(8 * (q i : ℝ) + 1)*a j)
    (G := (8 * (q j : ℝ) + 7)*d i-(8 * (q i : ℝ) + 1)*d j)
    hls hsr (by nlinarith [hl i hi j hj]) (by nlinarith [hr i hi j hj])
  nlinarith

/-- Linear conditions on target speeds give a real common isolation band at
the old pinch. q is an arbitrary proposed replacement, not assumed to be clear.
The unproved global obligation is selecting such a q for arbitrary targets. -/
theorem replacement_window_at_pinch (S : Finset ι) (hS : S.Nonempty)
    (a d : ι → ℝ) (q : ι → ℤ)
    (ha : ∀ i ∈ S, 0 < a i) (hd : ∀ i ∈ S, 0 < d i)
    {A E : ℝ} (hA : 0 < A) (hE : E < 0)
    (htransport : ∀ i ∈ S, ∀ j ∈ S,
      0 ≤ A * ((8 * (q j : ℝ) + 7)*d i-(8 * (q i : ℝ) + 1)*d j) -
        ((8 * (q j : ℝ) + 7)*a i-(8 * (q i : ℝ) + 1)*a j)*E) :
    ∃ t : ℝ, ∀ i ∈ S,
      (q i : ℝ) + 1/8 ≤ ((1-A/(A-E))*a i+(A/(A-E))*d i)*t ∧
      ((1-A/(A-E))*a i+(A/(A-E))*d i)*t ≤ q i+7/8 := by
  have htau := pinch_interior hA hE
  have hD : 0 < A-E := by linarith
  apply (WindowPinch.lap_windows_iff S hS _ q (fun i hi =>
    add_pos (mul_pos (sub_pos.mpr htau.2) (ha i hi))
      (mul_pos htau.1 (hd i hi)))).mpr
  intro i hi j hj
  have h := (slack_at_pinch_iff (C :=
    (8 * (q j : ℝ) + 7)*a i-(8 * (q i : ℝ) + 1)*a j)
    (G := (8 * (q j : ℝ) + 7)*d i-(8 * (q i : ℝ) + 1)*d j) hD).mpr
      (htransport i hi j hj)
  nlinarith

/-- A fixed natural lap assignment verified at two parameters supplies a
positive isolation-band time at every intervening parameter. -/
theorem positive_windows_between (S : Finset ι) (hS : S.Nonempty)
    (a d : ι → ℝ) (q : ι → ℕ)
    (ha : ∀ i ∈ S, 0 < a i) (hd : ∀ i ∈ S, 0 < d i)
    {l r s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hls : l ≤ s) (hsr : s ≤ r)
    (hl : ∀ i ∈ S, ∀ j ∈ S,
      (8 * (q i : ℝ) + 1) * ((1-l)*a j+l*d j) ≤
        (8 * (q j : ℝ) + 7) * ((1-l)*a i+l*d i))
    (hr : ∀ i ∈ S, ∀ j ∈ S,
      (8 * (q i : ℝ) + 1) * ((1-r)*a j+r*d j) ≤
        (8 * (q j : ℝ) + 7) * ((1-r)*a i+r*d i)) :
    ∃ t : ℝ, 0 < t ∧ ∀ i ∈ S,
      (q i : ℝ) + 1/8 ≤ ((1-s)*a i+s*d i)*t ∧
      ((1-s)*a i+s*d i)*t ≤ q i+7/8 := by
  have hpos : ∀ i ∈ S, 0 < (1-s)*a i+s*d i := by
    intro i hi
    by_cases hzero : s = 0
    · simpa [hzero] using ha i hi
    · have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hzero)
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr hs1) (ha i hi).le) (mul_pos hsp (hd i hi))
  have hlin := lap_inequalities_between S a d (fun i => (q i : ℤ)) hls hsr
    (by simpa using hl) (by simpa using hr)
  obtain ⟨t, ht⟩ := (WindowPinch.lap_windows_iff S hS _ (fun i => (q i : ℤ)) hpos).mpr hlin
  have ht' : ∀ i ∈ S, (q i : ℝ) + 1/8 ≤ ((1-s)*a i+s*d i)*t ∧
      ((1-s)*a i+s*d i)*t ≤ q i+7/8 := by simpa using ht
  obtain ⟨i, hi⟩ := hS
  have hq : 0 ≤ (q i : ℝ) := Nat.cast_nonneg _
  have hb := (ht' i hi).1
  have hprod : 0 < ((1-s)*a i+s*d i)*t := by linarith
  exact ⟨t, pos_of_mul_pos_right hprod (hpos i hi).le, ht'⟩

end LRC.SymbolicWindowTransport
