import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.SelfMoverCommon
import Fresh.SelfMoverAllCommon
import Fresh.RatioLanding

/-!
# The ratio condition for the interior subjects 2 to 5 at speeds within `δ ≤ 1/8`

Written 2026-10-23.  New file.  Interior subject `k` in `{2,3,4,5}`: two neighbours at integer distance 1, the other five at integer distance 2 to 5 (the farthest runner is at distance
`max (k, 7 - k) ≤ 5`).  Speeds within `δ` of `c + i` give relative deviations within `2δ`.  The ratio condition `m ≤ reading ≤ 7 m` (`m` the nearer neighbour's reading) then reads
`5 + 2δ ≤ 7 (1 - 2δ)`, i.e. `δ ≤ 1/8` (arithmetic; tight at `δ = 1/8`).  `interior_firstIso_d`: `FirstIso v k (1/(8m))`; `ap_interior_lands_d`: `Lands v k m`.
For `k = 1, 6` the farthest runner is at distance 6 and the condition holds only up to `δ = 1/16` (`APLawR3_Interior`); beyond that the chamber route of `APLawR4_I1_*` applies.
Grades: [L].
-/

open Classical

namespace Fresh.OneMover

open Fresh

theorem interior_firstIso_d (c δ : ℝ) (hδ : δ ≤ 1 / 8) (v : Fin 8 → ℝ) (hv : ∀ i : Fin 8, |v i - (c + ((i : ℕ) : ℝ))| ≤ δ) (k a b : Fin 8)
    (hak : a ≠ k) (hbk : b ≠ k) (hab : a ≠ b) (ha1 : |((a : ℕ) : ℝ) - ((k : ℕ) : ℝ)| = 1) (hb1 : |((b : ℕ) : ℝ) - ((k : ℕ) : ℝ)| = 1)
    (hothers : ∀ i : Fin 8, i ≠ k → i ≠ a → i ≠ b → 2 ≤ |((i : ℕ) : ℝ) - ((k : ℕ) : ℝ)| ∧ |((i : ℕ) : ℝ) - ((k : ℕ) : ℝ)| ≤ 5) :
    ∃ m : ℝ, 0 < m ∧ (∃ i, i ≠ k ∧ |v i - v k| = m) ∧ (∀ i, i ≠ k → m ≤ |v i - v k| ∧ |v i - v k| ≤ 7 * m) ∧ FirstIso v k (1 / (8 * m)) := by
  have rb : ∀ i k : Fin 8, -(2 * δ) ≤ (v i - v k) - (((i : ℕ) : ℝ) - ((k : ℕ) : ℝ)) ∧ (v i - v k) - (((i : ℕ) : ℝ) - ((k : ℕ) : ℝ)) ≤ 2 * δ := by
    intro i k
    have h1 := abs_le.1 (hv i); have h2 := abs_le.1 (hv k)
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hd0 : 0 ≤ δ := le_trans (abs_nonneg _) (hv 0)
  have hab_bd : ∀ i : Fin 8, i ≠ k → |((i : ℕ) : ℝ) - ((k : ℕ) : ℝ)| - 2 * δ ≤ |v i - v k| ∧ |v i - v k| ≤ |((i : ℕ) : ℝ) - ((k : ℕ) : ℝ)| + 2 * δ := by
    intro i _
    obtain ⟨l, u⟩ := rb i k
    have h2 : |(v i - v k) - (((i : ℕ) : ℝ) - ((k : ℕ) : ℝ))| ≤ 2 * δ := abs_le.2 ⟨l, u⟩
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
  have hmle : m ≤ 1 + 2 * δ := le_trans (min_le_left _ _) (by linarith)
  have hmge : 1 - 2 * δ ≤ m := le_min (by linarith) (by linarith)
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

/-- Interior subjects 2 to 5: `FirstIso` at `1/(8 m)`, speeds within `δ ≤ 1/8` of `c + i`. -/
theorem ap_interior_firstIso_d (c δ : ℝ) (hδ : δ ≤ 1 / 8) (v : Fin 8 → ℝ) (hv : ∀ i : Fin 8, |v i - (c + ((i : ℕ) : ℝ))| ≤ δ) (k : Fin 8)
    (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hk6 : k ≠ 6) (hk7 : k ≠ 7) :
    ∃ m : ℝ, 0 < m ∧ (∃ i, i ≠ k ∧ |v i - v k| = m) ∧ (∀ i, i ≠ k → m ≤ |v i - v k| ∧ |v i - v k| ≤ 7 * m) ∧ FirstIso v k (1 / (8 * m)) := by
  fin_cases k
  · exact absurd rfl hk0
  · exact absurd rfl hk1
  · exact interior_firstIso_d c δ hδ v hv (⟨2, by norm_num⟩ : Fin 8) ⟨3, by norm_num⟩ ⟨1, by norm_num⟩ (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by intro i h1 h2 h3; fin_cases i <;> simp_all <;> norm_num [abs_of_nonneg, abs_of_nonpos])
  · exact interior_firstIso_d c δ hδ v hv (⟨3, by norm_num⟩ : Fin 8) ⟨4, by norm_num⟩ ⟨2, by norm_num⟩ (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by intro i h1 h2 h3; fin_cases i <;> simp_all <;> norm_num [abs_of_nonneg, abs_of_nonpos])
  · exact interior_firstIso_d c δ hδ v hv (⟨4, by norm_num⟩ : Fin 8) ⟨5, by norm_num⟩ ⟨3, by norm_num⟩ (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by intro i h1 h2 h3; fin_cases i <;> simp_all <;> norm_num [abs_of_nonneg, abs_of_nonpos])
  · exact interior_firstIso_d c δ hδ v hv (⟨5, by norm_num⟩ : Fin 8) ⟨6, by norm_num⟩ ⟨4, by norm_num⟩ (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by intro i h1 h2 h3; fin_cases i <;> simp_all <;> norm_num [abs_of_nonneg, abs_of_nonpos])
  · exact absurd rfl hk6
  · exact absurd rfl hk7

/-- The `Lands` form for the interior subjects 2 to 5 at speeds within `δ ≤ 1/8`. -/
theorem ap_interior_lands_d (c δ : ℝ) (hδ : δ ≤ 1 / 8) (v : Fin 8 → ℝ) (hv : ∀ i : Fin 8, |v i - (c + ((i : ℕ) : ℝ))| ≤ δ) (k : Fin 8)
    (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hk6 : k ≠ 6) (hk7 : k ≠ 7) :
    ∃ m : ℝ, 0 < m ∧ (∃ i, i ≠ k ∧ |v i - v k| = m) ∧ Lands v k m := by
  obtain ⟨m, hm, hmem, hr, _⟩ := ap_interior_firstIso_d c δ hδ v hv k hk0 hk1 hk6 hk7
  exact ⟨m, hm, hmem, ratio_lands v k m hm hmem hr⟩

#print axioms interior_firstIso_d
#print axioms ap_interior_firstIso_d
#print axioms ap_interior_lands_d

end Fresh.OneMover
