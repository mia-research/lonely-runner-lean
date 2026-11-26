import Fresh.ThreeBlockPartitionBypassClass

/-! Rules:1–4,8–18. Four physical unit-step AP pairs and three independent
positive gaps. Separate integer gap laps at the native AP reference retain
a simplex of residuals: each≥1/8,total≤1/2. Six gap-adjacent subjects clear
there; the two endpoints retain1/8 under original gap total≤3. The exact
full cascade map preceded the proof and retains earlier isolations and
closed-face ties. No supplied clearance or arbitrary-gap index existence.
-/
set_option maxHeartbeats 4000000
open Classical
namespace Fresh.FourAPPairs
open Fresh Fresh.OneMover

-- STANDING: DEFINITION
def speeds (c g h j : ℝ) (i : Fin 8) : ℝ :=
  c + if (i : ℕ)<2 then 1+(i : ℝ)
      else if (i : ℕ)<4 then g+(i : ℝ)
      else if (i : ℕ)<6 then g+h+(i : ℝ)-1
      else g+h+j+(i : ℝ)-2

theorem four_pairs_all_subjects (c g h j : ℝ) (m a b e : ℤ)
    (hm : 1 ≤ m) (hg : 0<g) (hh : 0<h) (hj : 0<j)
    (hsmall : g+h+j ≤ 3)
    (hU : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hV : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hW : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hUVW : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4) :
    ∀k : Fin 8, Isolation (speeds c g h j) k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hT : 0<(m : ℝ)+1/8 := by linarith
  have hu : (1/8 : ℝ) ≤ g*((m : ℝ)+1/8)-(a : ℝ) := by nlinarith
  have hv : (1/8 : ℝ) ≤ h*((m : ℝ)+1/8)-(b : ℝ) := by nlinarith
  have hw : (1/8 : ℝ) ≤ j*((m : ℝ)+1/8)-(e : ℝ) := by nlinarith
  have huvw : (g+h+j)*((m : ℝ)+1/8)-((a : ℝ)+(b : ℝ)+(e : ℝ)) ≤ 1/2 := by nlinarith
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
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+0*b+0*e+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0*m+1*a+0*b+0*e+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+1*a+0*b+0*e+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+1*a+1*b+0*e+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+1*a+1*b+0*e+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+1*a+1*b+1*e+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+1*a+1*b+1*e+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)+1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-1*m+-1*a+0*b+0*e+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (0*m+-1*a+0*b+0*e+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+0*b+0*e+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+1*b+0*e+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+1*b+0*e+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+1*b+1*e+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (3*m+0*a+1*b+1*e+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)+1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-2*m+-1*a+0*b+0*e+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+-1*a+0*b+0*e+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+0*b+0*e+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0*m+0*a+1*b+0*e+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+1*b+0*e+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+1*b+1*e+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+1*b+1*e+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)+1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-2*m+-1*a+-1*b+0*e+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+-1*a+-1*b+0*e+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+-1*b+0*e+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (0*m+0*a+-1*b+0*e+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+0*b+0*e+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+0*b+1*e+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (2*m+0*a+0*b+1*e+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)+1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-3*m+-1*a+-1*b+0*e+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+-1*a+-1*b+0*e+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+0*a+-1*b+0*e+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+-1*b+0*e+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+0*b+0*e+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (0*m+0*a+0*b+1*e+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+0*b+1*e+0 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
  · refine ⟨((m : ℝ)+1/8), by linarith, ?_⟩
    intro i hik
    fin_cases i
    · apply Fresh.Localisation.clear_of_window (-3*m+-1*a+-1*b+-1*e+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+-1*a+-1*b+-1*e+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-2*m+0*a+-1*b+-1*e+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+-1*b+-1*e+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (-1*m+0*a+0*b+-1*e+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · apply Fresh.Localisation.clear_of_window (0*m+0*a+0*b+-1*e+-1 : ℤ)
      all_goals norm_num [speeds]
      all_goals push_cast
      all_goals nlinarith
    · exact (hik rfl).elim
    · apply Fresh.Localisation.clear_of_window (1*m+0*a+0*b+0*e+0 : ℤ)
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
def FourAPPairsClass (V : Fin 8 → ℝ) : Prop :=
  (∀i,0<V i) ∧ Function.Injective V ∧
  ∃(c g h j B z : ℝ)(m a b e : ℤ)(σ : Equiv.Perm (Fin 8)),
    0<g ∧ 0<h ∧ 0<j ∧ g+h+j ≤ 3 ∧ 1 ≤ m ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j ∧
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4 ∧ z≠0 ∧
    V=(fun i => B+z*speeds c g h j (σ i))

theorem fourAPPairs_isolation {V : Fin 8 → ℝ}
    (h : FourAPPairsClass V)(k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,σ,hg,hh,hj,hsmall,hm,hU,hV,hW,hUVW,hz,hEq⟩ := h
  rw [hEq]
  have hi := four_pairs_all_subjects c g h j m a b e hm hg hh hj hsmall hU hV hW hUVW (σ k)
  have hi' := subject_isolation_affine B z hz hi
  exact (Fresh.isolation_comp_perm _ σ k).2 hi'

#print axioms four_pairs_all_subjects
#print axioms fourAPPairs_isolation
end Fresh.FourAPPairs
