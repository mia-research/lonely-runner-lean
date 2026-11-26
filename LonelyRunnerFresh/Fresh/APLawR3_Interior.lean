import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.SelfMoverCommon
import Fresh.SelfMoverAllCommon
import Fresh.RatioLanding

/-!
# The ratio condition for interior subjects: the largest radius

Written 2026-10-23.  New file.  Interior subject `k` (1 to 6) with neighbours `a`, `b` at integer distance 1 and all other runners at integer distance 2 to 6.
Relative deviation radius `rho` (each reading within `rho` of its AP integer).  The ratio condition `m <= |reading| <= 7 m` (`m` the nearer neighbour's reading) holds for every
deviation vector exactly when `6 + rho <= 7 (1 - rho)`, i.e. `rho <= 1/8` (the far end `6 + rho` against `7 (1 - rho)`; the other inequalities allow `rho <= 1/2` and `rho <= 3/4`).  Speeds within `1/16` of `c + i` give relative `rho = 1/8` (two deviations).
`interior_firstIso_max`: `FirstIso v k (1/(8 m))` for speeds within `1/16`.  Grades: [L] for the theorem; the sharpness remark is arithmetic (the constraint `6 + rho <= 7 (1 - rho)` is tight at `rho = 1/8`).
-/

open Classical

namespace Fresh.OneMover

open Fresh

theorem rel_bound_max (c : ℝ) (v : Fin 8 → ℝ) (hv : ∀ i : Fin 8, |v i - (c + ((i : ℕ) : ℝ))| ≤ 1 / 16) (i k : Fin 8) :
    -(1 / 8 : ℝ) ≤ (v i - v k) - (((i : ℕ) : ℝ) - ((k : ℕ) : ℝ)) ∧ (v i - v k) - (((i : ℕ) : ℝ) - ((k : ℕ) : ℝ)) ≤ 1 / 8 := by
  have h1 := abs_le.1 (hv i); have h2 := abs_le.1 (hv k)
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem interior_firstIso_max (c : ℝ) (v : Fin 8 → ℝ) (hv : ∀ i : Fin 8, |v i - (c + ((i : ℕ) : ℝ))| ≤ 1 / 16) (k a b : Fin 8)
    (hak : a ≠ k) (hbk : b ≠ k) (hab : a ≠ b) (ha1 : |((a : ℕ) : ℝ) - ((k : ℕ) : ℝ)| = 1) (hb1 : |((b : ℕ) : ℝ) - ((k : ℕ) : ℝ)| = 1)
    (hothers : ∀ i : Fin 8, i ≠ k → i ≠ a → i ≠ b → 2 ≤ |((i : ℕ) : ℝ) - ((k : ℕ) : ℝ)| ∧ |((i : ℕ) : ℝ) - ((k : ℕ) : ℝ)| ≤ 6) :
    ∃ m : ℝ, 0 < m ∧ (∃ i, i ≠ k ∧ |v i - v k| = m) ∧ (∀ i, i ≠ k → m ≤ |v i - v k| ∧ |v i - v k| ≤ 7 * m) ∧ FirstIso v k (1 / (8 * m)) := by
  have rb := rel_bound_max c v hv
  have hab_bd : ∀ i : Fin 8, i ≠ k → |((i : ℕ) : ℝ) - ((k : ℕ) : ℝ)| - 1 / 8 ≤ |v i - v k| ∧ |v i - v k| ≤ |((i : ℕ) : ℝ) - ((k : ℕ) : ℝ)| + 1 / 8 := by
    intro i _
    obtain ⟨l, u⟩ := rb i k
    have h2 : |(v i - v k) - (((i : ℕ) : ℝ) - ((k : ℕ) : ℝ))| ≤ 1 / 8 := abs_le.2 ⟨l, u⟩
    have h3 := abs_sub_abs_le_abs_sub (((i : ℕ) : ℝ) - ((k : ℕ) : ℝ)) (v i - v k)
    have h3' : |(v i - v k) - (((i : ℕ) : ℝ) - ((k : ℕ) : ℝ))| = |(((i : ℕ) : ℝ) - ((k : ℕ) : ℝ)) - (v i - v k)| := abs_sub_comm _ _
    have h4 := abs_sub_abs_le_abs_sub (v i - v k) (((i : ℕ) : ℝ) - ((k : ℕ) : ℝ))
    constructor <;> linarith
  set ra := |v a - v k| with hra
  set rb' := |v b - v k| with hrb
  obtain ⟨la, ua⟩ := hab_bd a hak
  obtain ⟨lb, ub⟩ := hab_bd b hbk
  rw [ha1] at la ua; rw [hb1] at lb ub
  set m := min ra rb' with hm
  have hmpos : 0 < m := lt_min (by linarith) (by linarith)
  have hmem : ∃ i, i ≠ k ∧ |v i - v k| = m := by
    rcases min_choice ra rb' with h | h
    · exact ⟨a, hak, by rw [hm, h]⟩
    · exact ⟨b, hbk, by rw [hm, h]⟩
  have hmle : m ≤ 1 + 1 / 8 := le_trans (min_le_left _ _) (by linarith)
  have hmge : 1 - 1 / 8 ≤ m := le_min (by linarith) (by linarith)
  have hr : ∀ i, i ≠ k → m ≤ |v i - v k| ∧ |v i - v k| ≤ 7 * m := by
    intro i hik
    by_cases hia : i = a
    · subst hia; exact ⟨min_le_left _ _, by linarith⟩
    by_cases hib : i = b
    · subst hib; exact ⟨min_le_right _ _, by linarith⟩
    obtain ⟨h2, h6⟩ := hothers i hik hia hib
    obtain ⟨l, u⟩ := hab_bd i hik
    exact ⟨by linarith, by linarith⟩
  exact ⟨m, hmpos, hmem, hr, ratio_firstIso v k m hmpos hmem hr⟩

/-- Every interior subject (1 to 6): `FirstIso` at `1/(8 m)`, speeds within `1/16` of `c + i`. -/
theorem ap_interior_firstIso_max (c : ℝ) (v : Fin 8 → ℝ) (hv : ∀ i : Fin 8, |v i - (c + ((i : ℕ) : ℝ))| ≤ 1 / 16) (k : Fin 8)
    (hk0 : k ≠ 0) (hk7 : k ≠ 7) :
    ∃ m : ℝ, 0 < m ∧ (∃ i, i ≠ k ∧ |v i - v k| = m) ∧ (∀ i, i ≠ k → m ≤ |v i - v k| ∧ |v i - v k| ≤ 7 * m) ∧ FirstIso v k (1 / (8 * m)) := by
  fin_cases k
  · exact absurd rfl hk0
  · exact interior_firstIso_max c v hv (⟨1, by norm_num⟩ : Fin 8) ⟨2, by norm_num⟩ ⟨0, by norm_num⟩ (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by intro i h1 h2 h3; fin_cases i <;> simp_all <;> norm_num [abs_of_nonneg, abs_of_nonpos])
  · exact interior_firstIso_max c v hv (⟨2, by norm_num⟩ : Fin 8) ⟨3, by norm_num⟩ ⟨1, by norm_num⟩ (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by intro i h1 h2 h3; fin_cases i <;> simp_all <;> norm_num [abs_of_nonneg, abs_of_nonpos])
  · exact interior_firstIso_max c v hv (⟨3, by norm_num⟩ : Fin 8) ⟨4, by norm_num⟩ ⟨2, by norm_num⟩ (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by intro i h1 h2 h3; fin_cases i <;> simp_all <;> norm_num [abs_of_nonneg, abs_of_nonpos])
  · exact interior_firstIso_max c v hv (⟨4, by norm_num⟩ : Fin 8) ⟨5, by norm_num⟩ ⟨3, by norm_num⟩ (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by intro i h1 h2 h3; fin_cases i <;> simp_all <;> norm_num [abs_of_nonneg, abs_of_nonpos])
  · exact interior_firstIso_max c v hv (⟨5, by norm_num⟩ : Fin 8) ⟨6, by norm_num⟩ ⟨4, by norm_num⟩ (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by intro i h1 h2 h3; fin_cases i <;> simp_all <;> norm_num [abs_of_nonneg, abs_of_nonpos])
  · exact interior_firstIso_max c v hv (⟨6, by norm_num⟩ : Fin 8) ⟨7, by norm_num⟩ ⟨5, by norm_num⟩ (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by intro i h1 h2 h3; fin_cases i <;> simp_all <;> norm_num [abs_of_nonneg, abs_of_nonpos])
  · exact absurd rfl hk7

/-- The `Lands` form for an interior subject at the maximal radius: `Lands v k m` with `m` the nearer neighbour's reading. -/
theorem ap_interior_lands_max (c : ℝ) (v : Fin 8 → ℝ) (hv : ∀ i : Fin 8, |v i - (c + ((i : ℕ) : ℝ))| ≤ 1 / 16) (k : Fin 8)
    (hk0 : k ≠ 0) (hk7 : k ≠ 7) :
    ∃ m : ℝ, 0 < m ∧ (∃ i, i ≠ k ∧ |v i - v k| = m) ∧ Lands v k m := by
  obtain ⟨m, hm, hmem, hr, _⟩ := ap_interior_firstIso_max c v hv k hk0 hk7
  exact ⟨m, hm, hmem, ratio_lands v k m hm hmem hr⟩

#print axioms interior_firstIso_max
#print axioms ap_interior_firstIso_max
#print axioms ap_interior_lands_max

end Fresh.OneMover
