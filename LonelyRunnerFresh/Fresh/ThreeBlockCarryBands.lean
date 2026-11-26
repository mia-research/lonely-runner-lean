import Fresh.ThreeBlockCarry

/-! Rules:1–4,8–18. Enlarged G09/H06 physical carry family from original
boundary faces, with no assumption that the comparison output was visited.
The left boundary is forced by its farthest retained middle reading; the
right boundary by the third middle reading at the returned-pair opening.
The other original readings follow from these two inequalities and ordering. -/
set_option maxHeartbeats 2000000
open Classical
namespace Fresh.ThreeBlockCarryBands
open Fresh Fresh.OneMover Fresh.ThreeBlockCarry

theorem band_all_subjects (c g h : ℝ)
    (hg : 1≤g) (hh : 1≤h) (hsum : g+h≤3)
    (hleft : 2*g+8≤7*h) (hright : 17*g≤8*h+7) :
    ∀k : Fin 8, Isolation (speeds c g h) k := by
  have hD : 0<8*(4+g+h) := by linarith
  intro k
  fin_cases k
  · refine ⟨(9 : ℝ)/(8*(4+g+h)), by positivity, ?_⟩
    intro i hik
    fin_cases i
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals try rw [← mul_div_assoc]
      all_goals first
      | (apply (le_div_iff₀ hD).2; nlinarith)
      | (apply (div_le_iff₀ hD).2; nlinarith)
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals try rw [← mul_div_assoc]
      all_goals first
      | (apply (le_div_iff₀ hD).2; nlinarith)
      | (apply (div_le_iff₀ hD).2; nlinarith)
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals try rw [← mul_div_assoc]
      all_goals first
      | (apply (le_div_iff₀ hD).2; nlinarith)
      | (apply (div_le_iff₀ hD).2; nlinarith)
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals try rw [← mul_div_assoc]
      all_goals first
      | (apply (le_div_iff₀ hD).2; nlinarith)
      | (apply (div_le_iff₀ hD).2; nlinarith)
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals try rw [← mul_div_assoc]
      all_goals first
      | (apply (le_div_iff₀ hD).2; nlinarith)
      | (apply (div_le_iff₀ hD).2; nlinarith)
    · apply Fresh.Localisation.clear_of_window (1 : ℤ)
      all_goals norm_num [speeds]
      all_goals try rw [← mul_div_assoc]
      all_goals first
      | (apply (le_div_iff₀ hD).2; nlinarith)
      | (apply (div_le_iff₀ hD).2; nlinarith)
    · apply Fresh.Localisation.clear_of_window (1 : ℤ)
      all_goals norm_num [speeds]
      all_goals try rw [← mul_div_assoc]
      all_goals first
      | (apply (le_div_iff₀ hD).2; nlinarith)
      | (apply (div_le_iff₀ hD).2; nlinarith)
  · refine ⟨(1/8 : ℝ), by positivity, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
  · refine ⟨(1/8 : ℝ), by positivity, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
  · refine ⟨(1/8 : ℝ), by positivity, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
  · refine ⟨(1/8 : ℝ), by positivity, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
  · refine ⟨(1/8 : ℝ), by positivity, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
  · refine ⟨(1/8 : ℝ), by positivity, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
  · refine ⟨(25 : ℝ)/(8*(4+g+h)), by positivity, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-4 : ℤ)
      all_goals norm_num [speeds]
      all_goals try rw [← mul_div_assoc]
      all_goals first
      | (apply (le_div_iff₀ hD).2; nlinarith)
      | (apply (div_le_iff₀ hD).2; nlinarith)
    · apply Fresh.Localisation.clear_of_window (-4 : ℤ)
      all_goals norm_num [speeds]
      all_goals try rw [← mul_div_assoc]
      all_goals first
      | (apply (le_div_iff₀ hD).2; nlinarith)
      | (apply (div_le_iff₀ hD).2; nlinarith)
    · apply Fresh.Localisation.clear_of_window (-3 : ℤ)
      all_goals norm_num [speeds]
      all_goals try rw [← mul_div_assoc]
      all_goals first
      | (apply (le_div_iff₀ hD).2; nlinarith)
      | (apply (div_le_iff₀ hD).2; nlinarith)
    · apply Fresh.Localisation.clear_of_window (-3 : ℤ)
      all_goals norm_num [speeds]
      all_goals try rw [← mul_div_assoc]
      all_goals first
      | (apply (le_div_iff₀ hD).2; nlinarith)
      | (apply (div_le_iff₀ hD).2; nlinarith)
    · apply Fresh.Localisation.clear_of_window (-2 : ℤ)
      all_goals norm_num [speeds]
      all_goals try rw [← mul_div_assoc]
      all_goals first
      | (apply (le_div_iff₀ hD).2; nlinarith)
      | (apply (div_le_iff₀ hD).2; nlinarith)
    · apply Fresh.Localisation.clear_of_window (-2 : ℤ)
      all_goals norm_num [speeds]
      all_goals try rw [← mul_div_assoc]
      all_goals first
      | (apply (le_div_iff₀ hD).2; nlinarith)
      | (apply (div_le_iff₀ hD).2; nlinarith)
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals try rw [← mul_div_assoc]
      all_goals first
      | (apply (le_div_iff₀ hD).2; nlinarith)
      | (apply (div_le_iff₀ hD).2; nlinarith)
    · exact (hik rfl).elim


-- STANDING: DEFINITION
def ThreeBlockCarryBandsClass (V : Fin 8 → ℝ) : Prop :=
  (∀i,0<V i) ∧ Function.Injective V ∧
  ∃(c g h B a : ℝ)(σ : Equiv.Perm (Fin 8)),
    1≤g ∧ 1≤h ∧ g+h≤3 ∧ 2*g+8≤7*h ∧ 17*g≤8*h+7 ∧ a≠0 ∧
    V=(fun i => B+a*speeds c g h (σ i))

theorem threeBlockCarryBands_isolation {V : Fin 8 → ℝ}
    (h : ThreeBlockCarryBandsClass V)(k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,h,B,a,σ,hg,hh,hsum,hleft,hright,ha,hV⟩ := h
  rw [hV]
  have hi := band_all_subjects c g h hg hh hsum hleft hright (σ k)
  have hi' := subject_isolation_affine B a ha hi
  exact (Fresh.isolation_comp_perm _ σ k).2 hi'

#print axioms band_all_subjects
#print axioms threeBlockCarryBands_isolation
end Fresh.ThreeBlockCarryBands
