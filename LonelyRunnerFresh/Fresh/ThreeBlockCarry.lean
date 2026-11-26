import Fresh.FullThreeFiveArrangement

/-!
Rules:1–4,8–18. G09/H06 two independent gap departures in physical2+4+2.
The exact original-cascade map found a far-left pair resumption followed by
middle captures and a final return to the opposite pair member. Its derived
opening clears every reading on the whole real triangle below. Some boundary
inputs isolate earlier; the computed opening is not asserted to be visited.
No finite-control count supplies the universal statement.
-/
set_option maxHeartbeats 2000000
open Classical
namespace Fresh.ThreeBlockCarry
open Fresh Fresh.OneMover

-- STANDING: DEFINITION
def speeds (c g h : ℝ) (i : Fin 8) : ℝ :=
  c + if (i : ℕ)<2 then 1+(i : ℝ)
      else if (i : ℕ)<6 then g+(i : ℝ)
      else g+h+(i : ℝ)-1

theorem all_subjects (c g h : ℝ)
    (hg1 : 1≤g) (hg2 : g≤9/8)
    (hh1 : 15/8≤h) (hh2 : h≤2) (hsum : g+h≤3) :
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
def ThreeBlockCarryClass (V : Fin 8 → ℝ) : Prop :=
  (∀i,0<V i) ∧ Function.Injective V ∧
  ∃(c g h B a : ℝ)(σ : Equiv.Perm (Fin 8)),
    1≤g ∧ g≤9/8 ∧ 15/8≤h ∧ h≤2 ∧ g+h≤3 ∧ a≠0 ∧
    V=(fun i => B+a*speeds c g h (σ i))

theorem threeBlockCarry_isolation {V : Fin 8 → ℝ}
    (h : ThreeBlockCarryClass V)(k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,h,B,a,σ,hg1,hg2,hh1,hh2,hsum,ha,hV⟩ := h
  rw [hV]
  have hi := all_subjects c g h hg1 hg2 hh1 hh2 hsum (σ k)
  have hi' := subject_isolation_affine B a ha hi
  exact (Fresh.isolation_comp_perm _ σ k).2 hi'

#print axioms all_subjects
#print axioms threeBlockCarry_isolation
end Fresh.ThreeBlockCarry
