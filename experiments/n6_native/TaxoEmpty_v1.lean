import Mathlib

/-!
# The two empty outcome classes, at every order (n6_native, E78; order-8 E325, E333)

Cascade in R-units at order `n`: readings `ρ > 0` (speeds over the slowest), zone `(y, j)` = the open interval
`((n j − 1)/ρ_y, (n j + 1)/ρ_y)`, `j ≥ 1`; the cascade starts at `R = 1`, jumps to the largest exit among the zones
containing the current point, and stops at the landing `R*`; the opener is a zone with exit `R*`; the closer is the
least entry `≥ R*`. The facts used about a run are its monotonicity: the first jump goes to `R₂`, the largest exit of
a zone containing `1`; a run with two or more jumps lands at `R* > R₂ ≥ 1`.

* **K2a is empty** (`k2a_empty`): with two or more jumps, an opener on lap 1 is never a strip reading
  (`|ρ_s − n j'| < 1` for some `j' ≥ 1`).
* **K2s1 is empty**: the closer is the opener's own reading only if no faster reading is clear at `R*`
  (`closer_same_forces_fastest`); and a fastest opener on lap 1 cannot follow an earlier setter, so its run has one
  jump (`fastest_lap_one_first_jump`).
-/

namespace N6Native

/-- **K2a.** Let `R₂` bound every exit of a zone containing `1`. A lap-1 zone of `s` whose exit `(n+1)/ρ_s` exceeds
`R₂` and is at least `1` belongs to a reading within no unit distance of a positive multiple of `n`. -/
theorem k2a_empty {n ρ R₂ : ℝ} (hn : 2 ≤ n) (hρ : 0 < ρ)
    (hR₂ : ∀ j : ℕ, 1 ≤ j → (n * j - 1) / ρ < 1 → 1 < (n * j + 1) / ρ → (n * j + 1) / ρ ≤ R₂)
    (hE : R₂ < (n + 1) / ρ) (h1 : 1 ≤ (n + 1) / ρ) :
    ∀ j' : ℕ, 1 ≤ j' → ¬ (|ρ - n * j'| < 1) := by
  intro j' hj' habs
  rw [abs_lt] at habs
  have hj'R : (1 : ℝ) ≤ j' := by exact_mod_cast hj'
  rcases eq_or_lt_of_le hj' with h | h
  · subst h
    simp only [Nat.cast_one, mul_one] at habs
    have e1 : (n * ((1 : ℕ) : ℝ) - 1) / ρ < 1 := by rw [div_lt_one hρ]; push_cast; linarith
    have e2 : 1 < (n * ((1 : ℕ) : ℝ) + 1) / ρ := by rw [one_lt_div hρ]; push_cast; linarith
    have := hR₂ 1 le_rfl e1 e2
    simp only [Nat.cast_one, mul_one] at this; linarith
  · have h2 : (2 : ℝ) ≤ j' := by exact_mod_cast h
    have : n + 1 < ρ := by nlinarith
    rw [le_div_iff₀ hρ] at h1; linarith

/-- **K2s1, first half (closer = opener forces fastest).** The opener `s` on lap `j` lands at `R* = (n j + 1)/ρ_s`;
its own next entry is `(n (j+1) − 1)/ρ_s`. A faster reading `y`, clear at `R*` on lap `m` (`n m + 1 ≤ R* ρ_y`), has its
next entry `(n (m+1) − 1)/ρ_y` strictly earlier. -/
theorem closer_same_forces_fastest {n ρs ρy : ℝ} {j m : ℕ} (hn : 2 < n) (hs : 0 < ρs) (hsy : ρs < ρy)
    (hclear : n * m + 1 ≤ (n * j + 1) / ρs * ρy) :
    (n * (m + 1) - 1) / ρy < (n * (j + 1) - 1) / ρs := by
  have hy : 0 < ρy := lt_trans hs hsy
  set R := (n * j + 1) / ρs with hR
  have hR' : R * ρs = n * j + 1 := by rw [hR]; field_simp
  -- y's next entry ≤ R + (n-2)/ρy < R + (n-2)/ρs = s's next entry
  have a : (n * (m + 1) - 1) / ρy ≤ R + (n - 2) / ρy := by
    rw [div_le_iff₀ hy, add_mul, div_mul_cancel₀ _ hy.ne']; nlinarith
  have b : (n - 2) / ρy < (n - 2) / ρs := div_lt_div_of_pos_left (by linarith) hs hsy
  have c : R + (n - 2) / ρs = (n * (j + 1) - 1) / ρs := by
    rw [hR]; field_simp; ring
  linarith

/-- **K2s1, second half (a fastest lap-1 opener is the first jump).** If `s` is the fastest reading and the opener on
lap 1, `R* = (n+1)/ρ_s`, then every exit `(n k + 1)/ρ_y` of another, slower reading on a lap `k ≥ 1` lies beyond `R*`:
no earlier setter can bring the run into `s`'s lap-1 zone below `R*`, so the run reaches `R*` by its first jump. -/
theorem fastest_lap_one_first_jump {n ρs ρy : ℝ} {k : ℕ} (hn : 0 < n) (hy : 0 < ρy) (hys : ρy < ρs) (hk : 1 ≤ k) :
    (n + 1) / ρs < (n * k + 1) / ρy := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : 0 < ρs := lt_trans hy hys
  rw [div_lt_div_iff₀ hs hy]
  have a := mul_lt_mul_of_pos_left hys (by linarith : (0 : ℝ) < n + 1)
  have b := mul_le_mul_of_nonneg_right (by nlinarith : n + 1 ≤ n * k + 1) hs.le
  linarith

end N6Native

#print axioms N6Native.k2a_empty
#print axioms N6Native.closer_same_forces_fastest
#print axioms N6Native.fastest_lap_one_first_jump
