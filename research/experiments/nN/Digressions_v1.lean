import Mathlib

/-! # Checks from the 2026-09-23 digressions.  Core fact, then three corollaries. -/

noncomputable def circDist (x : ℝ) : ℝ := min (Int.fract x) (1 - Int.fract x)

/-- **Core.** On a rational `A/M` the circle distance is `min(A % M, M − A % M)/M`. -/
theorem circDist_intCast_div (A : ℤ) (M : ℕ) :
    circDist ((A : ℝ) / (M : ℝ))
      = min (((A % (M:ℤ) : ℤ) : ℝ) / (M:ℝ)) (1 - ((A % (M:ℤ) : ℤ) : ℝ) / (M:ℝ)) := by
  unfold circDist
  rw [Int.fract_div_intCast_eq_div_intCast_mod]

/-- **Threshold form.**  With threshold `p/Q`, clearance at `A/M` is a pair of integer
inequalities on `A % M`.  Taking `p = 1`, `Q = n`, `M = n*b` recovers the existing criterion. -/
theorem clear_at_threshold (A : ℤ) (M : ℕ) (hM : 0 < M) (p Q : ℕ) (hQ : 0 < Q) :
    ((p:ℝ)/(Q:ℝ) ≤ circDist ((A : ℝ) / (M : ℝ)))
      ↔ ((p:ℤ) * (M:ℤ) ≤ (A % (M:ℤ)) * (Q:ℤ)
          ∧ (A % (M:ℤ)) * (Q:ℤ) ≤ (M:ℤ) * (Q:ℤ) - (p:ℤ) * (M:ℤ)) := by
  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hQ0 : (0:ℝ) < (Q:ℝ) := by exact_mod_cast hQ
  set r : ℤ := A % (M:ℤ) with hr
  rw [circDist_intCast_div, le_min_iff]
  have e1 : ((p:ℝ)/(Q:ℝ) ≤ (r:ℝ)/(M:ℝ)) ↔ (p:ℤ) * (M:ℤ) ≤ r * (Q:ℤ) := by
    rw [div_le_div_iff₀ hQ0 hM0]; exact_mod_cast Iff.rfl
  have e2 : ((p:ℝ)/(Q:ℝ) ≤ 1 - (r:ℝ)/(M:ℝ)) ↔ r * (Q:ℤ) ≤ (M:ℤ)*(Q:ℤ) - (p:ℤ)*(M:ℤ) := by
    rw [le_sub_iff_add_le, div_add_div _ _ (ne_of_gt hQ0) (ne_of_gt hM0),
        div_le_one (by positivity)]
    constructor
    · intro h; exact_mod_cast (by nlinarith : (r:ℝ)*(Q:ℝ) ≤ (M:ℝ)*(Q:ℝ) - (p:ℝ)*(M:ℝ))
    · intro h
      have : (r:ℝ)*(Q:ℝ) ≤ (M:ℝ)*(Q:ℝ) - (p:ℝ)*(M:ℝ) := by exact_mod_cast h
      nlinarith
  rw [e1, e2]

/-- **Discrete circle.**  Loneliness on `ℤ/M` at time `t` is loneliness of the real problem
at time `t/M`: the discrete version samples the continuum on the grid `(1/M)ℤ`. -/
theorem discrete_iff_real (A : ℤ) (M n : ℕ) (hM : 0 < M) (hn : 0 < n) :
    ((M:ℤ) ≤ (n:ℤ) * min (A % (M:ℤ)) ((M:ℤ) - A % (M:ℤ)))
      ↔ ((n:ℝ)⁻¹ ≤ circDist ((A:ℝ)/(M:ℝ))) := by
  have h := clear_at_threshold A M hM 1 n hn
  rw [Nat.cast_one, one_div] at h
  rw [h]
  have hn' : (0:ℤ) ≤ (n:ℤ) := Int.natCast_nonneg n
  rw [mul_min_of_nonneg _ _ hn', le_min_iff]
  push_cast
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- **Cylinder bound.**  For complex speeds with real time, a disparity whose imaginary part
reaches the threshold never obstructs. -/
theorem cyl_clear_of_im (z : ℂ) (g : ℝ) (h : g ≤ |z.im|) :
    g ≤ Real.sqrt ((circDist z.re)^2 + z.im^2) := by
  have h1 : |z.im| ≤ Real.sqrt ((circDist z.re)^2 + z.im^2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (circDist z.re)])
  linarith

/-- **The existing criterion is the instance `p = 1`, `Q = n`, `M = n·b`.**
At the opening `(k + 1/n)/b` of the flank `b`, clearance at threshold `1/n` is exactly
`b ≤ a(nk+1) mod nb ≤ nb − b`. -/
theorem clear_at_threshold_recovers (a : ℤ) (b n k : ℕ) (hb : 0 < b) (hn : 0 < n) :
    ((n:ℝ)⁻¹ ≤ circDist ((a : ℝ) * (((k:ℝ) + (n:ℝ)⁻¹) / (b:ℝ))))
      ↔ ((b:ℤ) ≤ (a * ((n:ℤ)*(k:ℤ) + 1)) % ((n:ℤ)*(b:ℤ))
          ∧ (a * ((n:ℤ)*(k:ℤ) + 1)) % ((n:ℤ)*(b:ℤ)) ≤ (n:ℤ)*(b:ℤ) - (b:ℤ)) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hb0 : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hkey : (a : ℝ) * (((k:ℝ) + (n:ℝ)⁻¹) / (b:ℝ))
      = ((a * ((n:ℤ)*(k:ℤ) + 1) : ℤ) : ℝ) / (((n*b : ℕ)) : ℝ) := by
    push_cast; field_simp; try ring
  rw [hkey]
  have h := clear_at_threshold (a * ((n:ℤ)*(k:ℤ) + 1)) (n*b) (Nat.mul_pos hn hb) 1 n hn
  rw [Nat.cast_one, one_div] at h
  rw [h]
  push_cast
  have hnZ : (0:ℤ) < (n:ℤ) := by exact_mod_cast hn
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith [h1, h2, hnZ]
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith [h1, h2, hnZ]

#print axioms circDist_intCast_div
#print axioms clear_at_threshold
#print axioms discrete_iff_real
#print axioms cyl_clear_of_im
#print axioms clear_at_threshold_recovers
