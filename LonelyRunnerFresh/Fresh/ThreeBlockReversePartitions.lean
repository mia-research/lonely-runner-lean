import Fresh.ThreeBlockPartitions

/-! Rules: 1–4, 8–18. Six ordered three-block partitions, all block sizes
at least2, using the reflected native residual triangle with independent gap laps.
The original exact full-history map preceded this proof (6960 controls).
No finite controls are proof premises. No universal existence of lap labels
is assumed. [PROVISIONAL: counting tool; covering] native AP lap placement.
-/
set_option maxHeartbeats 2000000
open Classical
namespace Fresh.ThreeBlockReversePartitions
open Fresh Fresh.OneMover Fresh.ThreeBlockPartitions

theorem partition_224 (c g h : ℝ) (m a b : ℤ)
    (hm : 1≤ m) (hgpos : 0<g) (hhpos : 0<h) (hsmall : g+h≤2)
    (hg : (8*(m : ℝ)-1)*g≤8*(a : ℝ)-1)
    (hh : (8*(m : ℝ)-1)*h≤8*(b : ℝ)-1)
    (hsum : 8*((a : ℝ)+(b : ℝ))-3≤(8*(m : ℝ)-1)*(g+h)) :
    ∀k : Fin 8, Isolation (speeds c g h 2 2) k := by
  have hmR : (1 : ℝ)≤ m := by exact_mod_cast hm
  have hT : 0<(m : ℝ)-1/8 := by linarith
  have hu : (1/8 : ℝ)≤(a : ℝ)-g*((m : ℝ)-1/8) := by nlinarith
  have hv : (1/8 : ℝ)≤(b : ℝ)-h*((m : ℝ)-1/8) := by nlinarith
  have huv : ((a : ℝ)+(b : ℝ))-(g+h)*((m : ℝ)-1/8)≤3/8 := by nlinarith
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
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0*m+1*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+1*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+1*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+1*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+1*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (4*m+1*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-1*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (0*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (4*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-2*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-2*m+-1*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+-1*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (0*m+0*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+0*a+0*b+-1 : ℤ)
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

theorem partition_233 (c g h : ℝ) (m a b : ℤ)
    (hm : 1≤ m) (hgpos : 0<g) (hhpos : 0<h) (hsmall : g+h≤2)
    (hg : (8*(m : ℝ)-1)*g≤8*(a : ℝ)-1)
    (hh : (8*(m : ℝ)-1)*h≤8*(b : ℝ)-1)
    (hsum : 8*((a : ℝ)+(b : ℝ))-3≤(8*(m : ℝ)-1)*(g+h)) :
    ∀k : Fin 8, Isolation (speeds c g h 2 3) k := by
  have hmR : (1 : ℝ)≤ m := by exact_mod_cast hm
  have hT : 0<(m : ℝ)-1/8 := by linarith
  have hu : (1/8 : ℝ)≤(a : ℝ)-g*((m : ℝ)-1/8) := by nlinarith
  have hv : (1/8 : ℝ)≤(b : ℝ)-h*((m : ℝ)-1/8) := by nlinarith
  have huv : ((a : ℝ)+(b : ℝ))-(g+h)*((m : ℝ)-1/8)≤3/8 := by nlinarith
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
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0*m+1*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+1*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+1*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+1*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+1*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (4*m+1*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-1*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (0*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (4*m+0*a+1*b+-1 : ℤ)
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
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-3*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-3*m+-1*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+-1*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+0*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (0*m+0*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+0*b+-1 : ℤ)
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

theorem partition_242 (c g h : ℝ) (m a b : ℤ)
    (hm : 1≤ m) (hgpos : 0<g) (hhpos : 0<h) (hsmall : g+h≤2)
    (hg : (8*(m : ℝ)-1)*g≤8*(a : ℝ)-1)
    (hh : (8*(m : ℝ)-1)*h≤8*(b : ℝ)-1)
    (hsum : 8*((a : ℝ)+(b : ℝ))-3≤(8*(m : ℝ)-1)*(g+h)) :
    ∀k : Fin 8, Isolation (speeds c g h 2 4) k := by
  have hmR : (1 : ℝ)≤ m := by exact_mod_cast hm
  have hT : 0<(m : ℝ)-1/8 := by linarith
  have hu : (1/8 : ℝ)≤(a : ℝ)-g*((m : ℝ)-1/8) := by nlinarith
  have hv : (1/8 : ℝ)≤(b : ℝ)-h*((m : ℝ)-1/8) := by nlinarith
  have huv : ((a : ℝ)+(b : ℝ))-(g+h)*((m : ℝ)-1/8)≤3/8 := by nlinarith
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
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0*m+1*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+1*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+1*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+1*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+1*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (4*m+1*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-1*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (0*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+0*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (4*m+0*a+1*b+-1 : ℤ)
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
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-4*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-3*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-3*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-4*m+-1*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-3*m+-1*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-3*m+0*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+0*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (0*m+0*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+0*b+-1 : ℤ)
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

theorem partition_323 (c g h : ℝ) (m a b : ℤ)
    (hm : 1≤ m) (hgpos : 0<g) (hhpos : 0<h) (hsmall : g+h≤2)
    (hg : (8*(m : ℝ)-1)*g≤8*(a : ℝ)-1)
    (hh : (8*(m : ℝ)-1)*h≤8*(b : ℝ)-1)
    (hsum : 8*((a : ℝ)+(b : ℝ))-3≤(8*(m : ℝ)-1)*(g+h)) :
    ∀k : Fin 8, Isolation (speeds c g h 3 2) k := by
  have hmR : (1 : ℝ)≤ m := by exact_mod_cast hm
  have hT : 0<(m : ℝ)-1/8 := by linarith
  have hu : (1/8 : ℝ)≤(a : ℝ)-g*((m : ℝ)-1/8) := by nlinarith
  have hv : (1/8 : ℝ)≤(b : ℝ)-h*((m : ℝ)-1/8) := by nlinarith
  have huv : ((a : ℝ)+(b : ℝ))-(g+h)*((m : ℝ)-1/8)≤3/8 := by nlinarith
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
  · refine ⟨(1/8 : ℝ), by linarith, ?_⟩
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
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-2*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0*m+1*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+1*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+1*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+1*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+1*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-2*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (0*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-3*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-3*m+-1*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+-1*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+-1*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (0*m+0*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+0*b+-1 : ℤ)
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

theorem partition_332 (c g h : ℝ) (m a b : ℤ)
    (hm : 1≤ m) (hgpos : 0<g) (hhpos : 0<h) (hsmall : g+h≤2)
    (hg : (8*(m : ℝ)-1)*g≤8*(a : ℝ)-1)
    (hh : (8*(m : ℝ)-1)*h≤8*(b : ℝ)-1)
    (hsum : 8*((a : ℝ)+(b : ℝ))-3≤(8*(m : ℝ)-1)*(g+h)) :
    ∀k : Fin 8, Isolation (speeds c g h 3 3) k := by
  have hmR : (1 : ℝ)≤ m := by exact_mod_cast hm
  have hT : 0<(m : ℝ)-1/8 := by linarith
  have hu : (1/8 : ℝ)≤(a : ℝ)-g*((m : ℝ)-1/8) := by nlinarith
  have hv : (1/8 : ℝ)≤(b : ℝ)-h*((m : ℝ)-1/8) := by nlinarith
  have huv : ((a : ℝ)+(b : ℝ))-(g+h)*((m : ℝ)-1/8)≤3/8 := by nlinarith
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
  · refine ⟨(1/8 : ℝ), by linarith, ?_⟩
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
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-2*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0*m+1*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+1*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+1*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+1*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+1*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-2*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (0*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+0*a+1*b+-1 : ℤ)
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
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-4*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-3*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-4*m+-1*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-3*m+-1*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+-1*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+0*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (0*m+0*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+0*b+-1 : ℤ)
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

theorem partition_422 (c g h : ℝ) (m a b : ℤ)
    (hm : 1≤ m) (hgpos : 0<g) (hhpos : 0<h) (hsmall : g+h≤2)
    (hg : (8*(m : ℝ)-1)*g≤8*(a : ℝ)-1)
    (hh : (8*(m : ℝ)-1)*h≤8*(b : ℝ)-1)
    (hsum : 8*((a : ℝ)+(b : ℝ))-3≤(8*(m : ℝ)-1)*(g+h)) :
    ∀k : Fin 8, Isolation (speeds c g h 4 2) k := by
  have hmR : (1 : ℝ)≤ m := by exact_mod_cast hm
  have hT : 0<(m : ℝ)-1/8 := by linarith
  have hu : (1/8 : ℝ)≤(a : ℝ)-g*((m : ℝ)-1/8) := by nlinarith
  have hv : (1/8 : ℝ)≤(b : ℝ)-h*((m : ℝ)-1/8) := by nlinarith
  have huv : ((a : ℝ)+(b : ℝ))-(g+h)*((m : ℝ)-1/8)≤3/8 := by nlinarith
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
  · refine ⟨(1/8 : ℝ), by linarith, ?_⟩
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
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-3*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0*m+1*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+1*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+1*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+1*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-3*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (0*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+0*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-4*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-3*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+-1*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+0*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+1*b+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)-1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-4*m+-1*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-3*m+-1*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+-1*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+-1*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (0*m+0*a+-1*b+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+0*b+-1 : ℤ)
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

theorem reverse_partitions_all_subjects (c g h : ℝ) (p q : ℕ)
    (hp : 2≤p) (hq : 2≤q) (hpq : p+q≤6) (m a b : ℤ)
    (hm : 1≤ m) (hgpos : 0<g) (hhpos : 0<h) (hsmall : g+h≤2)
    (hg : (8*(m : ℝ)-1)*g≤8*(a : ℝ)-1)
    (hh : (8*(m : ℝ)-1)*h≤8*(b : ℝ)-1)
    (hsum : 8*((a : ℝ)+(b : ℝ))-3≤(8*(m : ℝ)-1)*(g+h)) :
    ∀k : Fin 8, Isolation (speeds c g h p q) k := by
  have hp4 : p≤4 := by omega
  have hq4 : q≤4 := by omega
  interval_cases p <;> interval_cases q
  · exact partition_224 c g h m a b hm hgpos hhpos hsmall hg hh hsum
  · exact partition_233 c g h m a b hm hgpos hhpos hsmall hg hh hsum
  · exact partition_242 c g h m a b hm hgpos hhpos hsmall hg hh hsum
  · exact partition_323 c g h m a b hm hgpos hhpos hsmall hg hh hsum
  · exact partition_332 c g h m a b hm hgpos hhpos hsmall hg hh hsum
  · omega
  · exact partition_422 c g h m a b hm hgpos hhpos hsmall hg hh hsum
  · omega
  · omega

/-- Positive distinct speeds, three nontrivial blocks, signed physical
scale/mirror, drift and arbitrary labels. -/
-- STANDING: DEFINITION
def ThreeBlockReversePartitionsClass (V : Fin 8→ℝ) : Prop :=
  (∀i,0<V i) ∧ Function.Injective V ∧
  ∃ (c g h B z : ℝ) (p q : ℕ) (m a b : ℤ) (σ : Equiv.Perm (Fin 8)),
    2≤p ∧ 2≤q ∧ p+q≤6 ∧ 1≤ m ∧ 0<g ∧ 0<h ∧ g+h≤2 ∧
    (8*(m : ℝ)-1)*g≤8*(a : ℝ)-1 ∧
    (8*(m : ℝ)-1)*h≤8*(b : ℝ)-1 ∧
    8*((a : ℝ)+(b : ℝ))-3≤(8*(m : ℝ)-1)*(g+h) ∧ z≠0 ∧
    V=(fun i=>B+z*speeds c g h p q (σ i))

theorem threeBlockReversePartitions_isolation {V : Fin 8→ℝ}
    (h : ThreeBlockReversePartitionsClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,h,B,z,p,q,m,a,b,σ,hp,hq,hpq,hm,hgpos,hhpos,hsmall,hg,hh,hsum,hz,hV⟩ := h
  rw [hV]
  have hi := reverse_partitions_all_subjects c g h p q hp hq hpq m a b hm hgpos hhpos hsmall hg hh hsum (σ k)
  have hi' := subject_isolation_affine B z hz hi
  exact (Fresh.isolation_comp_perm _ σ k).2 hi'

#print axioms partition_224
#print axioms partition_233
#print axioms partition_242
#print axioms partition_323
#print axioms partition_332
#print axioms partition_422
#print axioms reverse_partitions_all_subjects
#print axioms threeBlockReversePartitions_isolation
end Fresh.ThreeBlockReversePartitions
