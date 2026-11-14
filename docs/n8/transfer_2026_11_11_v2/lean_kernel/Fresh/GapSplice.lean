import Fresh.SymbolicWindow

namespace Fresh.SymbolicWindow

open Fresh.Certs

/-- Splice two stationary gap cells across one reading. The first cell can
lose clearance at its upper phase edge, and the second cell restores it
once the moving reading reaches its next lower phase edge. -/
theorem twoGapSplice (g : Fin 7 → ℝ) (i : Fin 7) (j k : ℤ)
    {a b L₀ U₀ L₁ U₁ : ℝ}
    (h₀a : a ≤ L₀) (h₀ : L₀ ≤ U₀) (h₀b : U₀ ≤ b)
    (h₁a : a ≤ L₁) (h₁ : L₁ ≤ U₁) (h₁b : U₁ ≤ b)
    (hg : 0 < g i) (hL₀ : 0 < L₀)
    (clear₀ : ∀ r, r ≠ i → ∀ R ∈ Set.Icc L₀ U₀,
      (1 / 8 : ℝ) ≤ distInt (g r * (R / 8)))
    (clear₁ : ∀ r, r ≠ i → ∀ R ∈ Set.Icc L₁ U₁,
      (1 / 8 : ℝ) ≤ distInt (g r * (R / 8)))
    (firstLower : (gapLo j : ℝ) ≤ L₀ * g i)
    (secondUpper : U₁ * g i ≤ (gapHi k : ℝ))
    (overlap : (gapLo k : ℝ) * L₀ ≤ (gapHi j : ℝ) * U₁)
    (hU₁ : 0 ≤ U₁) :
    let R := if L₀ * g i ≤ (gapHi j : ℝ) then L₀ else max L₁ ((gapLo k : ℝ) / g i)
    R ∈ Set.Icc a b ∧ ∀ r, (1 / 8 : ℝ) ≤ distInt (g r * (R / 8)) := by
  dsimp only
  split_ifs with h
  · refine ⟨⟨h₀a, h₀.trans h₀b⟩, fun r => ?_⟩
    by_cases hr : r = i
    · subst r
      rw [clearAt_R_iff]
      exact ⟨j, by simpa [gapLo, gapHi, mul_comm] using And.intro firstLower h⟩
    · exact clear₀ r hr L₀ ⟨le_rfl, h₀⟩
  · have hnext : (gapLo k : ℝ) ≤ U₁ * g i := by
      apply le_of_mul_le_mul_right _ hL₀
      calc
        (gapLo k : ℝ) * L₀ ≤ (gapHi j : ℝ) * U₁ := overlap
        _ ≤ (L₀ * g i) * U₁ := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge h)) hU₁
        _ = (U₁ * g i) * L₀ := by ring
    have hR : max L₁ ((gapLo k : ℝ) / g i) ∈ Set.Icc L₁ U₁ :=
      ⟨le_max_left _ _, max_le h₁ ((div_le_iff₀ hg).2 hnext)⟩
    refine ⟨⟨h₁a.trans hR.1, hR.2.trans h₁b⟩, fun r => ?_⟩
    by_cases hr : r = i
    · subst r
      rw [clearAt_R_iff]
      have hl := (div_le_iff₀ hg).1 (le_max_right L₁ ((gapLo k : ℝ) / g i))
      have hu := (mul_le_mul_of_nonneg_right hR.2 hg.le).trans secondUpper
      exact ⟨k, by simpa [gapLo, gapHi, mul_comm] using And.intro hl hu⟩
    · exact clear₁ r hr _ hR

#print axioms twoGapSplice

end Fresh.SymbolicWindow
