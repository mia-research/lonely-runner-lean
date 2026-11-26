import Fresh.FourAPPairs

/-! Rules:1–4,8–18. Native single full move for four AP pairs, with
independent cumulative gap laps and no bound on total original gap.
Both distant pairs may be captured and bypassed. Closed co-setter faces
are allowed; the original partner's entry faces remain strict. -/
open Classical
namespace Fresh.FourAPPairsNative
open Fresh Fresh.Cascade Fresh.Localisation

noncomputable def leftReadings (g h j : ℝ) : Finset ℝ :=
  {g,1,1+g,1+g+h,2+g+h,2+g+h+j,3+g+h+j}

theorem native_output_clear (g h j : ℝ) (m a b : ℤ) (hm : 1 ≤ m)
    (hg : 0<g) (hh : 0<h) (hj : 0<j)
    (he1 : 1<(8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g<1)
    (hS1 : 8*(a : ℝ) ≤ (8*(m : ℝ)+1)*(g+h))
    (hS2 : (8*(m : ℝ)+1)*(g+h) ≤ 8*(a : ℝ)+5)
    (hR1 : 8*(b : ℝ) ≤ (8*(m : ℝ)+1)*(g+h+j))
    (hR2 : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*(b : ℝ)+4) :
    LonelyAt (leftReadings g h j) ((m : ℝ)+1/8) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hgmax : g<1/7 := by nlinarith
  have hu1 : (1/8 : ℝ) ≤ g*((m : ℝ)+1/8) := by nlinarith
  have hu2 : g*((m : ℝ)+1/8) ≤ 3/8 := by nlinarith
  intro d hd
  simp only [leftReadings,Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · apply clear_of_window 0 <;> push_cast <;> nlinarith
  · apply clear_of_window m <;> push_cast <;> nlinarith
  · apply clear_of_window m <;> push_cast <;> nlinarith
  · apply clear_of_window (m+a) <;> push_cast <;> nlinarith
  · apply clear_of_window (2*m+a) <;> push_cast <;> nlinarith
  · apply clear_of_window (2*m+b) <;> push_cast <;> nlinarith
  · apply clear_of_window (3*m+b) <;> push_cast <;> nlinarith

theorem native_full_bypass (g h j : ℝ) (m a b : ℤ) (hm : 1 ≤ m)
    (hg : 0<g) (hh : 0<h) (hj : 0<j)
    (he1 : 1<(8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g<1)
    (hS1 : 8*(a : ℝ) ≤ (8*(m : ℝ)+1)*(g+h))
    (hS2 : (8*(m : ℝ)+1)*(g+h) ≤ 8*(a : ℝ)+5)
    (hR1 : 8*(b : ℝ) ≤ (8*(m : ℝ)+1)*(g+h+j))
    (hR2 : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*(b : ℝ)+4) :
    IsLeast (leftReadings g h j : Set ℝ) g ∧ InWay 1 (1/(8*g)) ∧
    IsMove (leftReadings g h j) (1/(8*g)) ((m : ℝ)+1/8) ∧
    LonelyAt (leftReadings g h j) ((m : ℝ)+1/8) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hgmax : g<1/7 := by nlinarith
  have hleast : IsLeast (leftReadings g h j : Set ℝ) g := by
    refine ⟨by simp [leftReadings],?_⟩
    intro d hd
    simp only [Finset.mem_coe,leftReadings,Finset.mem_insert,Finset.mem_singleton] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> linarith
  have hpos : ∀d∈leftReadings g h j,0<d := fun d hd => lt_of_lt_of_le hg (hleast.2 hd)
  have hden : (0 : ℝ)<8*g := by positivity
  have htl : (m : ℝ)-1/8<1/(8*g) := by
    apply (lt_div_iff₀ hden).2
    nlinarith
  have htu : 1/(8*g)<(m : ℝ)+1/8 := by
    apply (div_lt_iff₀ hden).2
    nlinarith
  have habs : |(1 : ℝ)*(1/(8*g))-(m : ℝ)|<1/8 := by rw [abs_lt]; constructor <;> nlinarith
  have hw : InWay 1 (1/(8*g)) := lt_of_le_of_lt (Fresh.Cascade.distInt_le _ m) habs
  have hop : nextOpening 1 (1/(8*g))=(m : ℝ)+1/8 := by simpa using (nextOpening_eq habs)
  have hclear := native_output_clear g h j m a b hm hg hh hj he1 he2 hS1 hS2 hR1 hR2
  refine ⟨hleast,hw,?_,hclear⟩
  refine Or.inr ⟨1,by simp [leftReadings],hw,hop.symm,?_⟩
  intro d hd hdw
  exact nextOpening_le_of_lonely hpos hclear htu.le hd hdw

#print axioms native_output_clear
#print axioms native_full_bypass
end Fresh.FourAPPairsNative
