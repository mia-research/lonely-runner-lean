import Fresh.ThreeBlockPartitions

/-! Left endpoint singleton stays at the direct AP instant when its original
first gap is at least one. Other gap-adjacent subjects use the same displaced
reference. Original cascade controls precede proof: singleton_map and
singleton_large scripts, including every excluded case. -/
set_option maxHeartbeats 2000000
namespace Fresh.ThreeBlockEndpointSingleton
open Fresh Fresh.OneMover Fresh.ThreeBlockPartitions

theorem endpoint_1 (c g h : ℝ) (m a b : ℤ)
    (hm : 1 ≤ m) (hgpos : 1 ≤ g) (hhpos : 0 < h) (hsmall : g+h ≤ 2)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hsum : (8*(m : ℝ)+1)*(g+h) ≤ 8*((a : ℝ)+(b : ℝ))+3) :
    ∀ k : Fin 8, Isolation (speeds c g h 1 1) k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hT : 0 < (m : ℝ)+1/8 := by linarith
  have hu : (1/8 : ℝ) ≤ g*((m : ℝ)+1/8)-(a : ℝ) := by nlinarith
  have hv : (1/8 : ℝ) ≤ h*((m : ℝ)+1/8)-(b : ℝ) := by nlinarith
  have huv : (g+h)*((m : ℝ)+1/8)-((a : ℝ)+(b : ℝ)) ≤ 3/8 := by nlinarith
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
    · apply Fresh.Localisation.clear_of_window (0*m+-1*a+0*b+-1 : ℤ)
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
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+1*b+0 : ℤ)
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
    · apply Fresh.Localisation.clear_of_window (5*m+0*a+1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)+1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (0*m+-1*a+-1*b+-1 : ℤ)
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
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (4*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (5*m+0*a+0*b+0 : ℤ)
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
    · exact (hik rfl).elim
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

theorem endpoint_2 (c g h : ℝ) (m a b : ℤ)
    (hm : 1 ≤ m) (hgpos : 1 ≤ g) (hhpos : 0 < h) (hsmall : g+h ≤ 2)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hsum : (8*(m : ℝ)+1)*(g+h) ≤ 8*((a : ℝ)+(b : ℝ))+3) :
    ∀ k : Fin 8, Isolation (speeds c g h 1 2) k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hT : 0 < (m : ℝ)+1/8 := by linarith
  have hu : (1/8 : ℝ) ≤ g*((m : ℝ)+1/8)-(a : ℝ) := by nlinarith
  have hv : (1/8 : ℝ) ≤ h*((m : ℝ)+1/8)-(b : ℝ) := by nlinarith
  have huv : (g+h)*((m : ℝ)+1/8)-((a : ℝ)+(b : ℝ)) ≤ 3/8 := by nlinarith
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
    · apply Fresh.Localisation.clear_of_window (0*m+-1*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+1*b+0 : ℤ)
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
    · apply Fresh.Localisation.clear_of_window (5*m+0*a+1*b+0 : ℤ)
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
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+1*b+0 : ℤ)
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
  · refine ⟨((m : ℝ)+1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-1*m+-1*a+-1*b+-1 : ℤ)
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
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (4*m+0*a+0*b+0 : ℤ)
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
    · exact (hik rfl).elim
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

theorem endpoint_3 (c g h : ℝ) (m a b : ℤ)
    (hm : 1 ≤ m) (hgpos : 1 ≤ g) (hhpos : 0 < h) (hsmall : g+h ≤ 2)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hsum : (8*(m : ℝ)+1)*(g+h) ≤ 8*((a : ℝ)+(b : ℝ))+3) :
    ∀ k : Fin 8, Isolation (speeds c g h 1 3) k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hT : 0 < (m : ℝ)+1/8 := by linarith
  have hu : (1/8 : ℝ) ≤ g*((m : ℝ)+1/8)-(a : ℝ) := by nlinarith
  have hv : (1/8 : ℝ) ≤ h*((m : ℝ)+1/8)-(b : ℝ) := by nlinarith
  have huv : (g+h)*((m : ℝ)+1/8)-((a : ℝ)+(b : ℝ)) ≤ 3/8 := by nlinarith
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
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+1*b+0 : ℤ)
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
    · apply Fresh.Localisation.clear_of_window (5*m+0*a+1*b+0 : ℤ)
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
  · refine ⟨((m : ℝ)+1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-2*m+-1*a+0*b+-1 : ℤ)
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
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+0*a+1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)+1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-2*m+-1*a+-1*b+-1 : ℤ)
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
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+0*a+0*b+0 : ℤ)
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
    · exact (hik rfl).elim
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

theorem endpoint_4 (c g h : ℝ) (m a b : ℤ)
    (hm : 1 ≤ m) (hgpos : 1 ≤ g) (hhpos : 0 < h) (hsmall : g+h ≤ 2)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hsum : (8*(m : ℝ)+1)*(g+h) ≤ 8*((a : ℝ)+(b : ℝ))+3) :
    ∀ k : Fin 8, Isolation (speeds c g h 1 4) k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hT : 0 < (m : ℝ)+1/8 := by linarith
  have hu : (1/8 : ℝ) ≤ g*((m : ℝ)+1/8)-(a : ℝ) := by nlinarith
  have hv : (1/8 : ℝ) ≤ h*((m : ℝ)+1/8)-(b : ℝ) := by nlinarith
  have huv : (g+h)*((m : ℝ)+1/8)-((a : ℝ)+(b : ℝ)) ≤ 3/8 := by nlinarith
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
    · apply Fresh.Localisation.clear_of_window (5*m+0*a+1*b+0 : ℤ)
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
  · refine ⟨((m : ℝ)+1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
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
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)+1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
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
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+0*b+0 : ℤ)
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
    · exact (hik rfl).elim
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

theorem endpoint_5 (c g h : ℝ) (m a b : ℤ)
    (hm : 1 ≤ m) (hgpos : 1 ≤ g) (hhpos : 0 < h) (hsmall : g+h ≤ 2)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hsum : (8*(m : ℝ)+1)*(g+h) ≤ 8*((a : ℝ)+(b : ℝ))+3) :
    ∀ k : Fin 8, Isolation (speeds c g h 1 5) k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hT : 0 < (m : ℝ)+1/8 := by linarith
  have hu : (1/8 : ℝ) ≤ g*((m : ℝ)+1/8)-(a : ℝ) := by nlinarith
  have hv : (1/8 : ℝ) ≤ h*((m : ℝ)+1/8)-(b : ℝ) := by nlinarith
  have huv : (g+h)*((m : ℝ)+1/8)-((a : ℝ)+(b : ℝ)) ≤ 3/8 := by nlinarith
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
    · apply Fresh.Localisation.clear_of_window (4*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (4*m+0*a+1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (5*m+0*a+1*b+0 : ℤ)
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
    · apply Fresh.Localisation.clear_of_window (-4*m+0*a+0*b+-1 : ℤ)
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
    · apply Fresh.Localisation.clear_of_window (-4*m+0*a+-1*b+-1 : ℤ)
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

theorem endpoint_all_subjects (c g h : ℝ) (q : ℕ) (hq1 : 1 ≤ q) (hq5 : q ≤ 5)
    (m a b : ℤ) (hm : 1 ≤ m) (hgpos : 1 ≤ g) (hhpos : 0 < h) (hsmall : g+h ≤ 2)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hsum : (8*(m : ℝ)+1)*(g+h) ≤ 8*((a : ℝ)+(b : ℝ))+3) :
    ∀ k : Fin 8, Isolation (speeds c g h 1 q) k := by
  interval_cases q
  · exact endpoint_1 c g h m a b hm hgpos hhpos hsmall hg hh hsum
  · exact endpoint_2 c g h m a b hm hgpos hhpos hsmall hg hh hsum
  · exact endpoint_3 c g h m a b hm hgpos hhpos hsmall hg hh hsum
  · exact endpoint_4 c g h m a b hm hgpos hhpos hsmall hg hh hsum
  · exact endpoint_5 c g h m a b hm hgpos hhpos hsmall hg hh hsum

-- STANDING: DEFINITION
def EndpointSingletonClass (V : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < V i) ∧ Function.Injective V ∧
  ∃ (c g h B z : ℝ) (q : ℕ) (m a b : ℤ) (σ : Equiv.Perm (Fin 8)),
    1 ≤ q ∧ q ≤ 5 ∧ 1 ≤ m ∧ 1 ≤ g ∧ 0 < h ∧ g+h ≤ 2 ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    (8*(m : ℝ)+1)*(g+h) ≤ 8*((a : ℝ)+(b : ℝ))+3 ∧ z ≠ 0 ∧
    V=(fun i => B+z*speeds c g h 1 q (σ i))

theorem endpointSingleton_isolation {V : Fin 8 → ℝ}
    (h : EndpointSingletonClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,h,B,z,q,m,a,b,σ,hq1,hq5,hm,hgpos,hhpos,hsmall,hg,hh,hsum,hz,hV⟩ := h
  rw [hV]
  have hi := endpoint_all_subjects c g h q hq1 hq5 m a b hm hgpos hhpos hsmall hg hh hsum (σ k)
  have hi' := subject_isolation_affine B z hz hi
  exact (Fresh.isolation_comp_perm _ σ k).2 hi'
#print axioms endpoint_1
#print axioms endpoint_2
#print axioms endpoint_3
#print axioms endpoint_4
#print axioms endpoint_5
#print axioms endpoint_all_subjects
#print axioms endpointSingleton_isolation
end Fresh.ThreeBlockEndpointSingleton
