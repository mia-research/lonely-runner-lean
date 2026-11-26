import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.SelfMoverCommon

/-!
# The subject outside the AP, far enough that the cascade lands at once

Written 2026-10-22.  New file.  The subject `k` is at `x = c - δ` (below the runner at `c`) or `x = c + 7 + δ` (above the runner at `c + 7`),
the other seven runners on the AP.  Every other runner's disparity is `b + m` with `b` the least disparity and `0 ≤ m`.
At `T = 1/(8 b)` the least reading is `1/8` and the others are `1/8 + m/(8 b)`, so all are clear while `m ≤ 6 b`; before `T` the least
reading is in the way.  Hence `T` is the first isolation instant, with no move.  Statements (all with the cascade-free `FirstIso`):
* subject `k ≠ 0` below the AP, `b = δ`, `m = i` (`i ≤ 7`): needs `δ ≥ 7/6`;
* subject `k = 0` below the AP (the extreme runner moves outward), `b = 1 + δ`, `m = i - 1 ≤ 6`: every `δ > 0`;
* the two mirror statements above the AP.
Grades: [L].  Not claimed: `δ < 7/6` for `k ≠ 0` (finite window, observed in `s3_outside_probe_v1.out` to need up to 11 moves for `k = 7`).
-/

open Classical

namespace Fresh.OneMover

open Fresh

theorem clear_outside {b m : ℝ} (hb : 0 < b) (hm0 : 0 ≤ m) (hm : m ≤ 6 * b) :
    (1 / 8 : ℝ) ≤ distInt ((b + m) * (1 / (8 * b))) := by
  have e : (b + m) * (1 / (8 * b)) = 1 / 8 + m / (8 * b) := by field_simp
  have h0 : 0 ≤ m / (8 * b) := div_nonneg hm0 (by positivity)
  have h1 : m / (8 * b) ≤ 3 / 4 := by rw [div_le_iff₀ (by positivity)]; linarith
  have := Fresh.Localisation.clear_of_window 0 (y :=(b + m) * (1 / (8 * b))) (by push_cast; rw [e]; linarith) (by push_cast; rw [e]; linarith)
  exact this

/-- Below the AP, `k ≠ 0`, `δ ≥ 7/6`. -/
theorem outside_below_k_ne0 (c δ : ℝ) (k : Fin 8) (hk : (k : ℕ) ≠ 0) (hδ : (7 : ℝ) / 6 ≤ δ) :
    FirstIso (selfV c 0 (-1 : ℝ) δ k) k (1 / (8 * δ)) := by
  have hδp : 0 < δ := by linarith
  refine ⟨?_, ?_⟩
  · rw [iso_iff_nat]
    intro i hi hik
    have e : ((i : ℝ) - ((0 : ℕ) : ℝ) - (-1 : ℝ) * δ) = (1 : ℝ) * (δ + i) := by push_cast; ring
    have hi7 : (i : ℝ) ≤ 7 := by exact_mod_cast (by omega : i ≤ 7)
    rw [e]
    exact clear_of_abs (D := (1 : ℝ) * (δ + i)) (d := δ + i) (ε := 1) (by ring) (by norm_num)
      (by have := clear_outside hδp (Nat.cast_nonneg i) (by linarith); simpa [mul_comm] using this)
  · intro s hs0 hs
    by_contra hlt
    push Not at hlt
    have h0 := (iso_iff_nat c 0 (-1 : ℝ) δ k s).1 hs 0 (by norm_num) (fun h => hk h.symm)
    have e : (((0 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) - (-1 : ℝ) * δ) * s = δ * s := by push_cast; ring
    rw [e] at h0
    exact absurd h0 (not_le.2 (inway_before hδp hs0 hlt))

/-- Below the AP, the extreme runner `k = 0` moves outward: every `δ > 0`. -/
theorem outside_below_k0 (c δ : ℝ) (hδp : 0 < δ) :
    FirstIso (selfV c 0 (-1 : ℝ) δ (⟨0, by norm_num⟩ : Fin 8)) (⟨0, by norm_num⟩ : Fin 8) (1 / (8 * (1 + δ))) := by
  have hb : 0 < 1 + δ := by linarith
  refine ⟨?_, ?_⟩
  · rw [iso_iff_nat]
    intro i hi hik
    have hi1 : 1 ≤ i := by simp at hik; omega
    have hi7 : (i : ℝ) ≤ 7 := by exact_mod_cast (by omega : i ≤ 7)
    have hi1' : (1 : ℝ) ≤ i := by exact_mod_cast hi1
    have e : ((i : ℝ) - ((0 : ℕ) : ℝ) - (-1 : ℝ) * δ) = (1 : ℝ) * ((1 + δ) + ((i : ℝ) - 1)) := by push_cast; ring
    rw [e]
    exact clear_of_abs (D := (1 : ℝ) * ((1 + δ) + ((i : ℝ) - 1))) (d := (1 + δ) + ((i : ℝ) - 1)) (ε := 1) (by ring) (by norm_num)
      (clear_outside hb (by linarith) (by linarith))
  · intro s hs0 hs
    by_contra hlt
    push Not at hlt
    have h1 := (iso_iff_nat c 0 (-1 : ℝ) δ (⟨0, by norm_num⟩ : Fin 8) s).1 hs 1 (by norm_num) (by norm_num)
    have e : (((1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) - (-1 : ℝ) * δ) * s = (1 + δ) * s := by push_cast; ring
    rw [e] at h1
    exact absurd h1 (not_le.2 (inway_before hb hs0 hlt))

/-- Above the AP, `k ≠ 7`, `δ ≥ 7/6` (runner `7` is the nearest). -/
theorem outside_above_k_ne7 (c δ : ℝ) (k : Fin 8) (hk : (k : ℕ) ≠ 7) (hδ : (7 : ℝ) / 6 ≤ δ) :
    FirstIso (selfV c 7 (1 : ℝ) δ k) k (1 / (8 * δ)) := by
  have hδp : 0 < δ := by linarith
  refine ⟨?_, ?_⟩
  · rw [iso_iff_nat]
    intro i hi hik
    have e : ((i : ℝ) - ((7 : ℕ) : ℝ) - (1 : ℝ) * δ) = (-1 : ℝ) * (δ + ((7 : ℝ) - i)) := by push_cast; ring
    have hi7 : (i : ℝ) ≤ 7 := by exact_mod_cast (by omega : i ≤ 7)
    rw [e]
    exact clear_of_abs (D := (-1 : ℝ) * (δ + ((7 : ℝ) - i))) (d := δ + ((7 : ℝ) - i)) (ε := -1) (by ring) (by norm_num)
      (by have := clear_outside hδp (by linarith : (0 : ℝ) ≤ 7 - i) (by have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith); simpa [mul_comm] using this)
  · intro s hs0 hs
    by_contra hlt
    push Not at hlt
    have h0 := (iso_iff_nat c 7 (1 : ℝ) δ k s).1 hs 7 (by norm_num) (fun h => hk h.symm)
    have e : (((7 : ℕ) : ℝ) - ((7 : ℕ) : ℝ) - (1 : ℝ) * δ) * s = -(δ * s) := by push_cast; ring
    rw [e, Fresh.Localisation.distInt_neg] at h0
    exact absurd h0 (not_le.2 (inway_before hδp hs0 hlt))

/-- Above the AP, the extreme runner `k = 7` moves outward: every `δ > 0`. -/
theorem outside_above_k7 (c δ : ℝ) (hδp : 0 < δ) :
    FirstIso (selfV c 7 (1 : ℝ) δ (⟨7, by norm_num⟩ : Fin 8)) (⟨7, by norm_num⟩ : Fin 8) (1 / (8 * (1 + δ))) := by
  have hb : 0 < 1 + δ := by linarith
  refine ⟨?_, ?_⟩
  · rw [iso_iff_nat]
    intro i hi hik
    have hi6 : i ≤ 6 := by simp at hik; omega
    have hi6' : (i : ℝ) ≤ 6 := by exact_mod_cast hi6
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have e : ((i : ℝ) - ((7 : ℕ) : ℝ) - (1 : ℝ) * δ) = (-1 : ℝ) * ((1 + δ) + ((6 : ℝ) - i)) := by push_cast; ring
    rw [e]
    exact clear_of_abs (D := (-1 : ℝ) * ((1 + δ) + ((6 : ℝ) - i))) (d := (1 + δ) + ((6 : ℝ) - i)) (ε := -1) (by ring) (by norm_num)
      (clear_outside hb (by linarith) (by linarith))
  · intro s hs0 hs
    by_contra hlt
    push Not at hlt
    have h1 := (iso_iff_nat c 7 (1 : ℝ) δ (⟨7, by norm_num⟩ : Fin 8) s).1 hs 6 (by norm_num) (by norm_num)
    have e : (((6 : ℕ) : ℝ) - ((7 : ℕ) : ℝ) - (1 : ℝ) * δ) * s = -((1 + δ) * s) := by push_cast; ring
    rw [e, Fresh.Localisation.distInt_neg] at h1
    exact absurd h1 (not_le.2 (inway_before hb hs0 hlt))

#print axioms outside_below_k_ne0
#print axioms outside_below_k0
#print axioms outside_above_k_ne7
#print axioms outside_above_k7

end Fresh.OneMover
