import Fresh.ThreeBlockIndependentLaps
import Fresh.Cascade

/-! Rules:1–4,8–18. Native shared resumption for the subject at the second
physical speed. The original tiny-gap gate equals m; its opposite partner1
sets the full move to m+1/8 even if both far-pair readings are captured too.
All seven readings' clearance is derived below from the original gap bands.
The independent far-pair continuation may be bypassed, with no visit assumed. -/
open Classical
namespace Fresh.ThreeBlockGridResumption
open Fresh Fresh.Cascade Fresh.Localisation

noncomputable def leftReadings (g h : ℝ) : Finset ℝ :=
  {g,1,1+g,2+g,3+g,3+g+h,4+g+h}

theorem left_grid_clear (g h : ℝ) (m b : ℤ) (hm : 1  ≤  m)
    (hg : 0 < g) (hh : 0 < h) (hgrid : 8*(m : ℝ)*g=1)
    (hlo : 8*(b : ℝ)+1  ≤  (8*(m : ℝ)+1)*h)
    (hhi : (8*(m : ℝ)+1)*(g+h)  ≤  8*(b : ℝ)+3) :
    LonelyAt (leftReadings g h) ((m : ℝ)+1/8) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hgmax : g ≤ 1/8 := by nlinarith
  intro d hd
  simp only [leftReadings,Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · apply clear_of_window 0  <;> push_cast  <;> nlinarith
  · apply clear_of_window m  <;> push_cast  <;> nlinarith
  · apply clear_of_window m  <;> push_cast  <;> nlinarith
  · apply clear_of_window (2*m)  <;> push_cast  <;> nlinarith
  · apply clear_of_window (3*m)  <;> push_cast  <;> nlinarith
  · apply clear_of_window (3*m+b)  <;> push_cast  <;> nlinarith
  · apply clear_of_window (4*m+b)  <;> push_cast  <;> nlinarith

theorem left_native_gate_move (g h : ℝ) (m b : ℤ) (hm : 1  ≤  m)
    (hg : 0 < g) (hh : 0 < h) (hgrid : 8*(m : ℝ)*g=1)
    (hlo : 8*(b : ℝ)+1  ≤  (8*(m : ℝ)+1)*h)
    (hhi : (8*(m : ℝ)+1)*(g+h)  ≤  8*(b : ℝ)+3) :
    IsLeast (leftReadings g h : Set ℝ) g ∧
    1/(8*g)=(m : ℝ) ∧
    IsMove (leftReadings g h) (1/(8*g)) ((m : ℝ)+1/8) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hgmax : g ≤ 1/8 := by nlinarith
  have hpos : ∀d∈leftReadings g h,0 < d := by
    intro d hd
    simp only [leftReadings,Finset.mem_insert,Finset.mem_singleton] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl  <;> linarith
  have hleast : IsLeast (leftReadings g h : Set ℝ) g := by
    refine ⟨by simp [leftReadings],?_⟩
    intro d hd
    simp only [Finset.mem_coe,leftReadings,Finset.mem_insert,Finset.mem_singleton] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl  <;> linarith
  have hentry : 1/(8*g)=(m : ℝ) := by
    apply (div_eq_iff (by positivity : (8*g : ℝ)≠0)).2
    nlinarith
  have hclear := left_grid_clear g h m b hm hg hh hgrid hlo hhi
  have hw : InWay 1 (m : ℝ) := by
    simp only [InWay,one_mul,Fresh.Localisation.distInt_intCast]
    norm_num
  have hop : nextOpening 1 (m : ℝ)=(m : ℝ)+1/8 := by
    simpa using (nextOpening_eq (d := (1 : ℝ)) (t := (m : ℝ)) (k := m) (by norm_num))
  refine ⟨hleast,hentry,?_⟩
  rw [hentry]
  refine Or.inr ⟨1,by simp [leftReadings],hw,hop.symm,?_⟩
  intro d hd hdw
  exact nextOpening_le_of_lonely hpos hclear (by linarith) hd hdw

#print axioms left_grid_clear
#print axioms left_native_gate_move
end Fresh.ThreeBlockGridResumption
