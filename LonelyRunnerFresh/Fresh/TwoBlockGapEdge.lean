import Fresh.UnequalAPArrangement

/-! The gap edge of the two-block template, exact reduction (log E664; derivation E663).
Speeds `UnequalAPArrangement.speeds c A 1 b p` with `A = (p-1) + G`: block `c, …, c+p-1` and block `c+A+i b`.
Subject `p-1`, the end of the first block at the gap. Its readings are the whole numbers `j` (`1 ≤ j ≤ p-1`)
and `G + i b` (`i ≤ 7-p`). With `G (N + τ0) = 1/8` and `b = P/Q`, `N = r + Q m`, at the instant `N + T`:
* `own_phase`: `distInt (j (N + T)) = distInt (j T)`;
* `other_phase`: `distInt ((G + i b)(N + T)) = distInt (1/8 + G (T - τ0) + i b (r + T))`.
`gapEdge_isolatedAt` turns clearness of those readings into `IsolatedAt` for the subject. No covering step.
-/
namespace Fresh.TwoBlockGapEdge
open Fresh

theorem own_phase (j N : ℕ) (T : ℝ) : distInt ((j : ℝ) * ((N : ℝ) + T)) = distInt ((j : ℝ) * T) := by
  have : (j : ℝ) * ((N : ℝ) + T) = (j : ℝ) * T + ((j * N : ℕ) : ℤ) := by push_cast; ring
  rw [this, Fresh.Localisation.distInt_add_int]

theorem other_phase {G T τ0 : ℝ} (P Q r m i : ℕ) (hQ : 0 < Q) (N : ℕ) (hN : N = r + Q * m)
    (hG : G * ((N : ℝ) + τ0) = 1/8) :
    distInt ((G + (i : ℝ) * ((P : ℝ) / Q)) * ((N : ℝ) + T)) =
      distInt (1/8 + G * (T - τ0) + (i : ℝ) * ((P : ℝ) / Q) * ((r : ℝ) + T)) := by
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have key : (G + (i : ℝ) * ((P : ℝ) / Q)) * ((N : ℝ) + T) =
      (1/8 + G * (T - τ0) + (i : ℝ) * ((P : ℝ) / Q) * ((r : ℝ) + T)) + ((i * P * m : ℕ) : ℤ) := by
    rw [hN]; push_cast
    have : G * ((r : ℝ) + Q * m + τ0) = 1/8 := by rw [hN] at hG; push_cast at hG; linarith
    field_simp
    nlinarith [this]
  rw [key, Fresh.Localisation.distInt_add_int]

theorem gapEdge_isolatedAt (c b G t : ℝ) (p : ℕ) (hp1 : 1 ≤ p) (hp7 : p ≤ 7)
    (hown : ∀ j : ℕ, 1 ≤ j → j ≤ p - 1 → (1/8 : ℝ) ≤ distInt ((j : ℝ) * t))
    (hoth : ∀ i : ℕ, i ≤ 7 - p → (1/8 : ℝ) ≤ distInt ((G + (i : ℝ) * b) * t)) :
    IsolatedAt (Fresh.UnequalAPArrangement.speeds c (((p - 1 : ℕ) : ℝ) + G) 1 b p) ⟨p - 1, by omega⟩ t := by
  intro i hik
  have hkv : Fresh.UnequalAPArrangement.speeds c (((p - 1 : ℕ) : ℝ) + G) 1 b p ⟨p - 1, by omega⟩
      = c + ((p - 1 : ℕ) : ℝ) := by
    simp [Fresh.UnequalAPArrangement.speeds, show p - 1 < p by omega]
  rw [hkv]
  have hne : (i : ℕ) ≠ p - 1 := fun e => hik (Fin.ext e)
  by_cases hi : (i : ℕ) < p
  · have hiv : Fresh.UnequalAPArrangement.speeds c (((p - 1 : ℕ) : ℝ) + G) 1 b p i = c + ((i : ℕ) : ℝ) := by
      simp [Fresh.UnequalAPArrangement.speeds, hi]
    rw [hiv]
    have hlt : (i : ℕ) < p - 1 := by omega
    have e : (c + ((i : ℕ) : ℝ) - (c + ((p - 1 : ℕ) : ℝ))) * t = -((((p - 1 - (i : ℕ)) : ℕ) : ℝ) * t) := by
      rw [Nat.cast_sub (by omega : (i : ℕ) ≤ p - 1)]; ring
    rw [e, Fresh.Localisation.distInt_neg]
    exact hown _ (by omega) (by omega)
  · have hiv : Fresh.UnequalAPArrangement.speeds c (((p - 1 : ℕ) : ℝ) + G) 1 b p i
        = c + (((p - 1 : ℕ) : ℝ) + G) + b * (((i : ℕ) - p : ℕ) : ℝ) := by
      simp [Fresh.UnequalAPArrangement.speeds, hi]
    rw [hiv]
    have e : (c + (((p - 1 : ℕ) : ℝ) + G) + b * (((i : ℕ) - p : ℕ) : ℝ) - (c + ((p - 1 : ℕ) : ℝ))) * t
        = (G + ((((i : ℕ) - p) : ℕ) : ℝ) * b) * t := by ring
    rw [e]
    exact hoth _ (by omega)

#print axioms own_phase
#print axioms other_phase
#print axioms gapEdge_isolatedAt
end Fresh.TwoBlockGapEdge
