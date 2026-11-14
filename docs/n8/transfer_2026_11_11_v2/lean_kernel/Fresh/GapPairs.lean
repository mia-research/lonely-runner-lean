import Fresh.SymbolicWindow

namespace Fresh.SymbolicWindow

/-- An open bad phase of the moving reading contains the entire closed cell. -/
def BlocksCell (x L U : ℝ) : Prop :=
  ∃ j : ℤ, (8 * (j : ℝ) - 1) / L < x ∧ x < (8 * (j : ℝ) + 1) / U

/-- The point version of exact cell restoration. -/
theorem clear_of_not_blocksCell (g : Fin 7 → ℝ) (i : Fin 7)
    {L U : ℝ} (hL : 0 < L) (hLU : L ≤ U) (hg : 0 < g i)
    (slow : ∀ j, j ≠ i → ∀ R ∈ Set.Icc L U, (1 / 8 : ℝ) ≤ distInt (g j * (R / 8)))
    (available : ¬ BlocksCell (g i) L U) :
    ∃ R ∈ Set.Icc L U, ∀ j, (1 / 8 : ℝ) ≤ distInt (g j * (R / 8)) := by
  refine oneMovingReading_clear g i hL hLU hg ⟨le_rfl, le_rfl⟩ slow ?_
  intro j hj
  exact available ⟨j, by simpa [mul_comm] using hj.2.1, by simpa [mul_comm] using hj.2.2⟩

/-- Two slow cells with no shared blocker give a clear time for every reading
satisfying the no-shared-blocker condition. The two cells may be in different windows. -/
theorem clear_of_two_cells (g : Fin 7 → ℝ) (i : Fin 7)
    {L₀ U₀ L₁ U₁ : ℝ}
    (hL₀ : 0 < L₀) (h₀ : L₀ ≤ U₀) (hL₁ : 0 < L₁) (h₁ : L₁ ≤ U₁)
    (hg : 0 < g i)
    (slow₀ : ∀ j, j ≠ i → ∀ R ∈ Set.Icc L₀ U₀, (1 / 8 : ℝ) ≤ distInt (g j * (R / 8)))
    (slow₁ : ∀ j, j ≠ i → ∀ R ∈ Set.Icc L₁ U₁, (1 / 8 : ℝ) ≤ distInt (g j * (R / 8)))
    (disjoint : ¬ (BlocksCell (g i) L₀ U₀ ∧ BlocksCell (g i) L₁ U₁)) :
    ∃ R, (R ∈ Set.Icc L₀ U₀ ∨ R ∈ Set.Icc L₁ U₁) ∧
      ∀ j, (1 / 8 : ℝ) ≤ distInt (g j * (R / 8)) := by
  by_cases blocked : BlocksCell (g i) L₀ U₀
  · obtain ⟨R, hR, clear⟩ :=
      clear_of_not_blocksCell g i hL₁ h₁ hg slow₁ (fun h => disjoint ⟨blocked, h⟩)
    exact ⟨R, Or.inr hR, clear⟩
  · obtain ⟨R, hR, clear⟩ := clear_of_not_blocksCell g i hL₀ h₀ hg slow₀ blocked
    exact ⟨R, Or.inl hR, clear⟩

/-- A closed cell contained in one of the two normalized cascade windows. -/
def InBandCell (L U : ℝ) : Prop :=
  1 ≤ L ∧ L ≤ U ∧ U ≤ 15 ∧ (U ≤ 7 ∨ 9 ≤ L)

theorem bandClearPoint_of_two_cells (g : Fin 7 → ℝ) (i : Fin 7)
    {L₀ U₀ L₁ U₁ : ℝ} (h₀ : InBandCell L₀ U₀) (h₁ : InBandCell L₁ U₁)
    (hg : 0 < g i)
    (slow₀ : ∀ j, j ≠ i → ∀ R ∈ Set.Icc L₀ U₀, (1 / 8 : ℝ) ≤ distInt (g j * (R / 8)))
    (slow₁ : ∀ j, j ≠ i → ∀ R ∈ Set.Icc L₁ U₁, (1 / 8 : ℝ) ≤ distInt (g j * (R / 8)))
    (disjoint : ¬ (BlocksCell (g i) L₀ U₀ ∧ BlocksCell (g i) L₁ U₁)) :
    Fresh.BandNoCarve.BandClearPoint g := by
  obtain ⟨R, hR, clear⟩ := clear_of_two_cells g i
    (by have := h₀.1; linarith) h₀.2.1 (by have := h₁.1; linarith) h₁.2.1 hg
    slow₀ slow₁ disjoint
  have inWindow {L U : ℝ} (h : InBandCell L U) (hr : R ∈ Set.Icc L U) :
      1 ≤ R ∧ R ≤ 15 ∧ (R ≤ 7 ∨ 9 ≤ R) :=
    ⟨h.1.trans hr.1, hr.2.trans h.2.2.1,
      h.2.2.2.imp (fun hu => hr.2.trans hu) (fun hl => hl.trans hr.1)⟩
  obtain ⟨ha, hb, hw⟩ := hR.elim (inWindow h₀) (inWindow h₁)
  exact ⟨R, ha, hb, hw, clear⟩

#print axioms clear_of_not_blocksCell
#print axioms clear_of_two_cells
#print axioms bandClearPoint_of_two_cells

end Fresh.SymbolicWindow
