import Mathlib

/-!
# Every 2-torus through a tight vector (v3: v2 plus the lift), other than its own circle, meets the open cube (n6_native, E25)

`u` is `(1,2,3,4,5)` or `(1,3,4,5,9)` (first coordinate `1`). Replacing `v` by `v - v₀·u` does not change
the torus `{s u + t v}`, so the finite core takes `v₀ = 0`: for `(b,c,d,e) ∈ (ℤ/11)^4` not zero, some
`i, j < 11` put every coordinate of `i·u + j·(0,b,c,d,e)` in `{2,…,9}` modulo 11 (`check_grid`,
`check_other`, kernel computations). `torus_witness` lifts this to every integer `v` that is not
congruent to a multiple of `u` modulo 11, with the witness `i·u + j·v` (`i, j` integers). Its
coordinates read in `[2/11, 9/11]` at the instant `1/11`, strictly inside `(1/6, 5/6)`
(`witness_lonely`).
-/

namespace N6Native

def inBand (x : ℕ) : Bool := 2 ≤ x % 11 && x % 11 ≤ 9

def wit (u1 u2 u3 u4 b c d e : ℕ) : Bool :=
  (List.range 11).any fun i => (List.range 11).any fun j =>
    inBand i && inBand (i*u1 + j*b) && inBand (i*u2 + j*c) && inBand (i*u3 + j*d) &&
      inBand (i*u4 + j*e)

def check (u1 u2 u3 u4 : ℕ) : Bool :=
  (List.range 11).all fun b => (List.range 11).all fun c =>
    (List.range 11).all fun d => (List.range 11).all fun e =>
      (b == 0 && c == 0 && d == 0 && e == 0) || wit u1 u2 u3 u4 b c d e

set_option maxHeartbeats 0 in
theorem check_grid : check 2 3 4 5 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem check_other : check 3 4 5 9 = true := by decide +kernel

/-- An integer reads strictly inside the band at `1/11`: residue in `{2,…,9}`. -/
def Band (z : ℤ) : Prop := 2 ≤ z % 11 ∧ z % 11 ≤ 9

theorem band_of_modEq {z : ℤ} {n : ℕ} (h : z ≡ (n : ℤ) [ZMOD 11]) (hn : inBand n = true) : Band z := by
  simp only [inBand, Bool.and_eq_true, decide_eq_true_eq] at hn
  unfold Band
  rw [h]
  omega

theorem lift {u1 u2 u3 u4 : ℕ} (hc : check u1 u2 u3 u4 = true) (v0 v1 v2 v3 v4 : ℤ)
    (h : ¬ ∃ l : ℤ, (11 : ℤ) ∣ v1 - l * u1 ∧ (11 : ℤ) ∣ v2 - l * u2 ∧ (11 : ℤ) ∣ v3 - l * u3 ∧
      (11 : ℤ) ∣ v4 - l * u4 ∧ (11 : ℤ) ∣ v0 - l) :
    ∃ I J : ℤ, Band (I + J * v0) ∧ Band (I * u1 + J * v1) ∧ Band (I * u2 + J * v2) ∧
      Band (I * u3 + J * v3) ∧ Band (I * u4 + J * v4) := by
  set w1 := v1 - v0 * u1 with hw1
  set w2 := v2 - v0 * u2 with hw2
  set w3 := v3 - v0 * u3 with hw3
  set w4 := v4 - v0 * u4 with hw4
  have hr : ∀ w : ℤ, w ≡ ((w % 11).toNat : ℤ) [ZMOD 11] := fun w => by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg w (by norm_num))]
    exact (Int.mod_modEq w 11).symm
  have hlt : ∀ w : ℤ, (w % 11).toNat < 11 := fun w => by
    have := Int.emod_lt_of_pos w (by norm_num : (0:ℤ) < 11)
    have := Int.emod_nonneg w (by norm_num : (11:ℤ) ≠ 0)
    omega
  simp only [check, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at hc
  rcases hc _ (hlt w1) _ (hlt w2) _ (hlt w3) _ (hlt w4) with hz | hw
  · exfalso; apply h
    obtain ⟨⟨⟨z1, z2⟩, z3⟩, z4⟩ := hz
    clear_value w1 w2 w3 w4
    have n1 := Int.emod_nonneg w1 (by norm_num : (11:ℤ) ≠ 0)
    have n2 := Int.emod_nonneg w2 (by norm_num : (11:ℤ) ≠ 0)
    have n3 := Int.emod_nonneg w3 (by norm_num : (11:ℤ) ≠ 0)
    have n4 := Int.emod_nonneg w4 (by norm_num : (11:ℤ) ≠ 0)
    refine ⟨v0, ?_, ?_, ?_, ?_, by simp⟩
    · rw [← hw1]; exact Int.dvd_of_emod_eq_zero (by omega)
    · rw [← hw2]; exact Int.dvd_of_emod_eq_zero (by omega)
    · rw [← hw3]; exact Int.dvd_of_emod_eq_zero (by omega)
    · rw [← hw4]; exact Int.dvd_of_emod_eq_zero (by omega)
  · simp only [wit, List.any_eq_true, List.mem_range, Bool.and_eq_true] at hw
    obtain ⟨i, -, j, -, ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩⟩ := hw
    refine ⟨(i : ℤ) - j * v0, j, ?_, ?_, ?_, ?_, ?_⟩
    · exact band_of_modEq (n := i) (by ring_nf; rfl) h0
    · apply band_of_modEq _ h1
      push_cast
      have : (i - j * v0) * (u1 : ℤ) + j * v1 = i * u1 + j * w1 := by simp only [w1]; ring
      rw [this]; exact Int.ModEq.add_left _ (Int.ModEq.mul_left _ (hr w1))
    · apply band_of_modEq _ h2
      push_cast
      have : (i - j * v0) * (u2 : ℤ) + j * v2 = i * u2 + j * w2 := by simp only [w2]; ring
      rw [this]; exact Int.ModEq.add_left _ (Int.ModEq.mul_left _ (hr w2))
    · apply band_of_modEq _ h3
      push_cast
      have : (i - j * v0) * (u3 : ℤ) + j * v3 = i * u3 + j * w3 := by simp only [w3]; ring
      rw [this]; exact Int.ModEq.add_left _ (Int.ModEq.mul_left _ (hr w3))
    · apply band_of_modEq _ h4
      push_cast
      have : (i - j * v0) * (u4 : ℤ) + j * v4 = i * u4 + j * w4 := by simp only [w4]; ring
      rw [this]; exact Int.ModEq.add_left _ (Int.ModEq.mul_left _ (hr w4))

/-- A coordinate in `Band` reads in `[2/11, 9/11]` at `1/11`, so its distance to the nearest integer is
at least `2/11 > 1/6`. -/
theorem witness_lonely {z : ℤ} (h : Band z) : (6 : ℝ)⁻¹ < min (Int.fract ((z : ℝ) / 11)) (1 - Int.fract ((z : ℝ) / 11)) := by
  have hf : Int.fract ((z : ℝ) / 11) = ((z % 11 : ℤ) : ℝ) / 11 := by
    rw [Int.fract_eq_iff]
    refine ⟨by have := h.1; positivity, ?_, z / 11, ?_⟩
    · rw [div_lt_one (by norm_num)]; have := h.2; exact_mod_cast (by omega : z % 11 < 11)
    · have := Int.emod_add_mul_ediv z 11
      have h' : (z : ℝ) = ((z % 11 : ℤ) : ℝ) + 11 * ((z / 11 : ℤ) : ℝ) := by exact_mod_cast this.symm
      rw [h']; ring
  rw [hf]
  have h1 : (2 : ℝ) ≤ ((z % 11 : ℤ) : ℝ) := by exact_mod_cast h.1
  have h2 : ((z % 11 : ℤ) : ℝ) ≤ 9 := by exact_mod_cast h.2
  apply lt_min <;> linarith [show (0:ℝ) < 11 by norm_num]


/-- **Through the grid.** For any integer `v` not congruent to a multiple of `(1,2,3,4,5)` modulo 11,
the integer vector `I·(1,2,3,4,5) + J·v` is in `Band` in every coordinate for some integers `I, J`. -/
theorem torus_witness_grid (v0 v1 v2 v3 v4 : ℤ)
    (h : ¬ ∃ l : ℤ, (11 : ℤ) ∣ v1 - l * (2:ℕ) ∧ (11 : ℤ) ∣ v2 - l * (3:ℕ) ∧ (11 : ℤ) ∣ v3 - l * (4:ℕ) ∧
      (11 : ℤ) ∣ v4 - l * (5:ℕ) ∧ (11 : ℤ) ∣ v0 - l) :
    ∃ I J : ℤ, Band (I + J * v0) ∧ Band (I * (2:ℕ) + J * v1) ∧ Band (I * (3:ℕ) + J * v2) ∧
      Band (I * (4:ℕ) + J * v3) ∧ Band (I * (5:ℕ) + J * v4) :=
  lift check_grid v0 v1 v2 v3 v4 h

/-- **Through `(1,3,4,5,9)`.** -/
theorem torus_witness_other (v0 v1 v2 v3 v4 : ℤ)
    (h : ¬ ∃ l : ℤ, (11 : ℤ) ∣ v1 - l * (3:ℕ) ∧ (11 : ℤ) ∣ v2 - l * (4:ℕ) ∧ (11 : ℤ) ∣ v3 - l * (5:ℕ) ∧
      (11 : ℤ) ∣ v4 - l * (9:ℕ) ∧ (11 : ℤ) ∣ v0 - l) :
    ∃ I J : ℤ, Band (I + J * v0) ∧ Band (I * (3:ℕ) + J * v1) ∧ Band (I * (4:ℕ) + J * v2) ∧
      Band (I * (5:ℕ) + J * v3) ∧ Band (I * (9:ℕ) + J * v4) :=
  lift check_other v0 v1 v2 v3 v4 h

end N6Native

#print axioms N6Native.check_grid
#print axioms N6Native.check_other
#print axioms N6Native.lift
#print axioms N6Native.witness_lonely
#print axioms N6Native.torus_witness_grid
#print axioms N6Native.torus_witness_other
