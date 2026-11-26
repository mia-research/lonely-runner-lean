import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.AdmissibleFlank

/-!
# One retained reading and a translated six-reading AP block

Worklist G04/G12/A04. Unit reading set `{1,a,a+1,...,a+5}`.
The actual boundary examples expose one recurring flank: `(a+3)` on lap n.
The first three block readings retain lap n-1; the last three retain lap n.
Its parameter interval is `3n-21/8 <= a <= 4n-5/2`.
No first-isolation claim or global arrangement time bound is used.
-/

namespace Fresh.TranslatedSix

open Fresh

noncomputable def train (a : ℝ) : Finset ℝ :=
  {1, a, a + 1, a + 2, a + 3, a + 4, a + 5}

theorem clear_ratio {d den U : ℝ} (hden : 0 < den) (N : ℤ)
    (hlo : (8 * (N : ℝ) + 1) * den ≤ d * U)
    (hhi : d * U ≤ (8 * (N : ℝ) + 7) * den) :
    (1 / 8 : ℝ) ≤ distInt (d * (U / (8 * den))) := by
  apply Fresh.Localisation.clear_of_window N
  · rw [show d * (U / (8 * den)) = d * U / (8 * den) by ring,
      le_div_iff₀ (by positivity)]
    nlinarith
  · rw [show d * (U / (8 * den)) = d * U / (8 * den) by ring,
      div_le_iff₀ (by positivity)]
    nlinarith

theorem repeated_flank (n : ℤ) (hn : 3 ≤ n) (a : ℝ)
    (ha : 3 * (n : ℝ) - 21 / 8 ≤ a) (hb : a ≤ 4 * (n : ℝ) - 5 / 2) :
    0 < (8 * (n : ℝ) + 1) / (8 * (a + 3)) ∧
      ∀ d ∈ train a, (1 / 8 : ℝ) ≤ distInt (d * ((8 * (n : ℝ) + 1) / (8 * (a + 3)))) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < a + 3 := by linarith
  refine ⟨by positivity, fun d hmem => ?_⟩
  simp only [train, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply clear_ratio hd (0 : ℤ) <;> norm_num <;> nlinarith
  · apply clear_ratio hd (n - 1) <;> push_cast <;> nlinarith
  · apply clear_ratio hd (n - 1) <;> push_cast <;> nlinarith
  · apply clear_ratio hd (n - 1) <;> push_cast <;> nlinarith
  · apply clear_ratio hd n <;> nlinarith
  · apply clear_ratio hd n <;> nlinarith
  · apply clear_ratio hd n <;> nlinarith

/-- [PROVISIONAL: counting tool] the floor selects the recurring flank
interval. This supports the explicit isolation for every `a >= 51/8`. -/
theorem repeated_tail (a : ℝ) (ha : 51 / 8 ≤ a) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ train a, (1 / 8 : ℝ) ≤ distInt (d * t) := by
  let n : ℤ := ⌊(a + 21 / 8) / 3⌋
  have hn : (3 : ℤ) ≤ n := by
    apply Int.le_floor.mpr
    norm_num
    linarith
  have h1 : (n : ℝ) ≤ (a + 21 / 8) / 3 := Int.floor_le _
  have h2 : (a + 21 / 8) / 3 < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨ht, hclear⟩ := repeated_flank n hn a (by linarith) (by linarith)
  exact ⟨_, ht, hclear⟩

#print axioms clear_ratio
#print axioms repeated_flank
#print axioms repeated_tail

end Fresh.TranslatedSix
