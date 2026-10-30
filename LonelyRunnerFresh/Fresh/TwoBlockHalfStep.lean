import Fresh.Localisation

/-! The two-block own window and the half-step instant (log E649).
Seen from a subject inside one AP block of step `u`, its own-block readings are `j u` (`1 ≤ j ≤ J`, `J ≤ 7`); they are
1/8-clear at every instant of `W = [1/(8u), 7/(8 J u)]` (`own_window_clear`). The other block is an AP
`x + j s` (`j < q`). At a half-step instant `t = (2n+1)/(2s)` its readings take only two phases mod 1, `x t` and
`x t + 1/2` (`halfstep_phase`); if both are in the clear band, every reading of the other block is clear
(`halfstep_clear`). `two_block_halfstep` combines the two: such a `t` inside `W` clears every reading of the subject.
No covering or counting step is used; the instant is named from the readings (`s`, `n`) and checked.
-/
namespace Fresh.TwoBlockHalfStep
open Fresh

theorem own_window_clear {u t : ℝ} {J j : ℕ} (hu : 0 < u) (hj1 : 1 ≤ j) (hjJ : j ≤ J)
    (hlo : 1/(8*u) ≤ t) (hhi : t ≤ 7/(8*(J*u))) : 1/8 ≤ distInt ((j*u)*t) := by
  have hJ : (1 : ℝ) ≤ J := by exact_mod_cast (le_trans hj1 hjJ)
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hjJR : (j : ℝ) ≤ J := by exact_mod_cast hjJ
  have h1 : (1 : ℝ)/8 ≤ j*u*t := by
    have : u*t ≥ 1/8 := by
      have := (div_le_iff₀ (by positivity : (0:ℝ) < 8*u)).1 hlo; nlinarith
    nlinarith
  have h2 : j*u*t ≤ 7/8 := by
    have hut : J*u*t ≤ 7/8 := by
      have := (le_div_iff₀ (by positivity : (0:ℝ) < 8*(J*u))).1 hhi; nlinarith
    have ht : 0 ≤ u*t := by
      have : (0:ℝ) < 1/(8*u) := by positivity
      nlinarith
    nlinarith
  exact Fresh.Localisation.clear_of_window 0 (by simpa using h1) (by simpa using h2)

theorem halfstep_phase (x s : ℝ) (hs : s ≠ 0) (n j : ℕ) :
    (x + j*s) * (((2*n+1 : ℝ)/2)/s) = x*(((2*n+1 : ℝ)/2)/s) + (j : ℝ)*((2*n+1 : ℝ)/2) := by
  field_simp

theorem halfstep_clear {x s : ℝ} (hs : s ≠ 0) (n j : ℕ)
    (h0 : 1/8 ≤ distInt (x*(((2*n+1 : ℝ)/2)/s)))
    (h1 : 1/8 ≤ distInt (x*(((2*n+1 : ℝ)/2)/s) + 1/2)) :
    1/8 ≤ distInt ((x + j*s) * (((2*n+1 : ℝ)/2)/s)) := by
  rw [halfstep_phase x s hs n j]
  set y := x*(((2*n+1 : ℝ)/2)/s)
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' j
  · have he : (j : ℝ)*((2*n+1 : ℝ)/2) = ((m*(2*n+1) : ℕ) : ℤ) := by
      subst hm; push_cast; ring
    rw [he, Fresh.Localisation.distInt_add_int]; exact h0
  · have he : y + (j : ℝ)*((2*n+1 : ℝ)/2) = (y + 1/2) + ((m*(2*n+1) + n : ℕ) : ℤ) := by
      subst hm; push_cast; ring
    rw [he, Fresh.Localisation.distInt_add_int]; exact h1

/-- A subject in an AP block of step `u` (own readings `j u`, `1 ≤ j ≤ J`) and another block `x + j s`
(`j < q`): at a half-step instant of the other block inside the own window, with both phases clear, every
reading is clear. -/
theorem two_block_halfstep {u x s : ℝ} {J : ℕ} (hu : 0 < u) (hs : s ≠ 0) (n : ℕ)
    (hlo : 1/(8*u) ≤ ((2*n+1 : ℝ)/2)/s) (hhi : ((2*n+1 : ℝ)/2)/s ≤ 7/(8*(J*u)))
    (h0 : 1/8 ≤ distInt (x*(((2*n+1 : ℝ)/2)/s)))
    (h1 : 1/8 ≤ distInt (x*(((2*n+1 : ℝ)/2)/s) + 1/2)) :
    (∀ j : ℕ, 1 ≤ j → j ≤ J → 1/8 ≤ distInt ((j*u)*(((2*n+1 : ℝ)/2)/s))) ∧
    (∀ j : ℕ, 1/8 ≤ distInt ((x + j*s)*(((2*n+1 : ℝ)/2)/s))) :=
  ⟨fun j hj1 hjJ => own_window_clear hu hj1 hjJ hlo hhi, fun j => halfstep_clear hs n j h0 h1⟩

#print axioms own_window_clear
#print axioms halfstep_clear
#print axioms two_block_halfstep
end Fresh.TwoBlockHalfStep
