import Fresh.UnitAPPacketFourLift

/-! Reversing the original AP packet replaces its unit residual theta by
1-theta and pairs the outer and inner opening roles. All faces are closed. -/
namespace Fresh.UnitAPPacketFourSymmetry
open Fresh.UnitAPPacketFourCells Fresh.UnitAPPacketFourLift

theorem outer_reflection (theta : ℝ) : Cell3 theta ↔ Cell0 (1-theta) := by
  constructor
  · intro hc
    rcases hc with h|h|h|h|h
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩))
    · exact Or.inr (Or.inl ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩)
    · exact Or.inl ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩
  · intro hc
    rcases hc with h|h|h|h|h
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩))
    · exact Or.inr (Or.inl ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩)
    · exact Or.inl ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩

theorem inner_reflection (theta : ℝ) : Cell2 theta ↔ Cell1 (1-theta) := by
  constructor
  · intro hc
    rcases hc with h|h|h|h
    · exact Or.inr (Or.inr (Or.inr ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩))
    · exact Or.inr (Or.inl ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩)
    · exact Or.inl ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩
  · intro hc
    rcases hc with h|h|h|h
    · exact Or.inr (Or.inr (Or.inr ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩))
    · exact Or.inr (Or.inl ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩)
    · exact Or.inl ⟨by linarith [h.1,h.2],by linarith [h.1,h.2]⟩

theorem canonical_roles (a : Fin 4) (theta : ℝ) : Cell a theta ↔
    (a=0 ∧ Cell0 theta) ∨ (a=1 ∧ Cell1 theta) ∨
    (a=2 ∧ Cell1 (1-theta)) ∨ (a=3 ∧ Cell0 (1-theta)) := by
  fin_cases a <;> simp [Cell,outer_reflection,inner_reflection]

#print axioms outer_reflection
#print axioms inner_reflection
#print axioms canonical_roles
end Fresh.UnitAPPacketFourSymmetry
