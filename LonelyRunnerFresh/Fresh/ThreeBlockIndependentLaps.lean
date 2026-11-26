import Fresh.ThreeBlockCarry

/-! Rules:1–4,8–18. Original two independently moving near-coalescent gaps,
with separate unbounded integer packet laps at the native AP reference
q=8m+1. Original band inequalities derive all clearance; the computed
comparison need not be visited by the original full cascade. No existence
of lap indices for arbitrary gaps, no global continuation bound, and no
full exclusion from earlier proved classes is claimed. -/
set_option maxHeartbeats 2000000
open Classical
namespace Fresh.ThreeBlockIndependentLaps
open Fresh Fresh.OneMover Fresh.ThreeBlockCarry

theorem independent_laps_all_subjects (c g h : ℝ) (m a b : ℤ)
    (hm : 1  ≤  m) (hgpos : 0 < g) (hhpos : 0 < h) (hsmall : g+h ≤ 1/3)
    (hg : 8*(a : ℝ)+1  ≤  (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1  ≤  (8*(m : ℝ)+1)*h)
    (hsum : (8*(m : ℝ)+1)*(g+h)  ≤  8*((a : ℝ)+(b : ℝ))+3) :
    ∀k : Fin 8, Isolation (speeds c g h) k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hT : 0 < (m : ℝ)+1/8 := by linarith
  have hu1 : (1/8 : ℝ)  ≤  g*((m : ℝ)+1/8)-(a : ℝ) := by nlinarith
  have hv1 : (1/8 : ℝ)  ≤  h*((m : ℝ)+1/8)-(b : ℝ) := by nlinarith
  have huv : (g+h)*((m : ℝ)+1/8)-((a : ℝ)+(b : ℝ))  ≤  3/8 := by nlinarith
  intro k
  fin_cases k
  · refine ⟨(1/8 : ℝ), by linarith, ?_⟩
    intro i hik
    fin_cases i
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
    · apply Fresh.Localisation.clear_of_window (0 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
  · refine ⟨((m : ℝ)+1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0*m+1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+1*a+1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (4*m+1*a+1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)+1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-1*m+-1*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (0*m+-1*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+0*a+1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (4*m+0*a+1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨(1/8 : ℝ), by linarith, ?_⟩
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
  · refine ⟨(1/8 : ℝ), by linarith, ?_⟩
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
  · refine ⟨((m : ℝ)+1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-4*m+-1*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-3*m+-1*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-3*m+0*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+0*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0*m+0*a+1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)+1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-4*m+-1*a+-1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-3*m+-1*a+-1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-3*m+0*a+-1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+0*a+-1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+-1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (0*m+0*a+-1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨(1/8 : ℝ), by linarith, ?_⟩
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
    · apply Fresh.Localisation.clear_of_window (-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals linarith
    · exact (hik rfl).elim

-- STANDING: DEFINITION
def ThreeBlockIndependentLapsClass (V : Fin 8 → ℝ) : Prop :=
  (∀i,0 < V i) ∧ Function.Injective V ∧
  ∃(c g h B z : ℝ)(m a b : ℤ)(σ : Equiv.Perm (Fin 8)),
    1  ≤  m ∧ 0 < g ∧ 0 < h ∧ g+h ≤ 1/3 ∧
    8*(a : ℝ)+1  ≤  (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1  ≤  (8*(m : ℝ)+1)*h ∧
    (8*(m : ℝ)+1)*(g+h)  ≤  8*((a : ℝ)+(b : ℝ))+3 ∧ z≠0 ∧
    V=(fun i => B+z*speeds c g h (σ i))

theorem threeBlockIndependentLaps_isolation {V : Fin 8 → ℝ}
    (h : ThreeBlockIndependentLapsClass V)(k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,h,B,z,m,a,b,σ,hm,hgpos,hhpos,hsmall,hg,hh,hsum,hz,hV⟩ := h
  rw [hV]
  have hi := independent_laps_all_subjects c g h m a b hm hgpos hhpos hsmall hg hh hsum (σ k)
  have hi' := subject_isolation_affine B z hz hi
  exact (Fresh.isolation_comp_perm _ σ k).2 hi'

#print axioms independent_laps_all_subjects
#print axioms threeBlockIndependentLaps_isolation
end Fresh.ThreeBlockIndependentLaps
