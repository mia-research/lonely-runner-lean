import Fresh.ThreeBlockGridResumption

/-! Rules:1–4,8–18. Native opposite-pair bypass on an independently varying
real two-gap strip. Both eighth-boundary entry faces are deliberately strict:
on either face the designated partner is clear, so this setter claim need
not apply. The output clearance faces remain closed. The whole original
seven-reading input determines the actual first move; no output-clearance
assumption and no visit to the computed opposite-pair episode is used. -/
open Classical
namespace Fresh.ThreeBlockNativeBypass
open Fresh Fresh.Cascade Fresh.Localisation Fresh.ThreeBlockGridResumption

theorem bypass_output_clear (g h : ℝ) (m n : ℤ) (hm : 1 ≤ m)
    (hg : 0 < g) (hh : 0 < h)
    (hentry1 : 1 < (8*(m : ℝ)+1)*g)
    (hentry2 : (8*(m : ℝ)-1)*g < 1)
    (hlo : 8*(n : ℝ) ≤ (8*(m : ℝ)+1)*(g+h))
    (hhi : (8*(m : ℝ)+1)*(g+h) ≤ 8*(n : ℝ)+3) :
    LonelyAt (leftReadings g h) ((m : ℝ)+1/8) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hgmax : g < 1/7 := by nlinarith
  have hgl : (1/8 : ℝ) ≤ g*((m : ℝ)+1/8) := by nlinarith
  have hgu : g*((m : ℝ)+1/8) ≤ 1/2 := by nlinarith
  intro d hd
  simp only [leftReadings,Finset.mem_insert,Finset.mem_singleton] at hd
  rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · apply clear_of_window 0 <;> push_cast <;> nlinarith
  · apply clear_of_window m <;> push_cast <;> nlinarith
  · apply clear_of_window m <;> push_cast <;> nlinarith
  · apply clear_of_window (2*m) <;> push_cast <;> nlinarith
  · apply clear_of_window (3*m) <;> push_cast <;> nlinarith
  · apply clear_of_window (3*m+n) <;> push_cast <;> nlinarith
  · apply clear_of_window (4*m+n) <;> push_cast <;> nlinarith

theorem native_opposite_pair_bypass (g h : ℝ) (m n : ℤ) (hm : 1 ≤ m)
    (hg : 0 < g) (hh : 0 < h)
    (hentry1 : 1 < (8*(m : ℝ)+1)*g)
    (hentry2 : (8*(m : ℝ)-1)*g < 1)
    (hlo : 8*(n : ℝ) ≤ (8*(m : ℝ)+1)*(g+h))
    (hhi : (8*(m : ℝ)+1)*(g+h) ≤ 8*(n : ℝ)+3) :
    IsLeast (leftReadings g h : Set ℝ) g ∧
    InWay 1 (1/(8*g)) ∧
    IsMove (leftReadings g h) (1/(8*g)) ((m : ℝ)+1/8) ∧
    LonelyAt (leftReadings g h) ((m : ℝ)+1/8) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hgmax : g < 1/7 := by nlinarith
  have hpos : ∀d∈leftReadings g h,0 < d := by
    intro d hd
    simp only [leftReadings,Finset.mem_insert,Finset.mem_singleton] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> linarith
  have hleast : IsLeast (leftReadings g h : Set ℝ) g := by
    refine ⟨by simp [leftReadings],?_⟩
    intro d hd
    simp only [Finset.mem_coe,leftReadings,Finset.mem_insert,Finset.mem_singleton] at hd
    rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> linarith
  have hden : (0 : ℝ) < 8*g := by positivity
  have htl : (m : ℝ)-1/8 < 1/(8*g) := by
    apply (lt_div_iff₀ hden).2
    nlinarith
  have htu : 1/(8*g) < (m : ℝ)+1/8 := by
    apply (div_lt_iff₀ hden).2
    nlinarith
  have habs : |(1 : ℝ)*(1/(8*g))-(m : ℝ)| < 1/8 := by
    rw [abs_lt]
    constructor <;> nlinarith
  have hw : InWay 1 (1/(8*g)) :=
    lt_of_le_of_lt (Fresh.Cascade.distInt_le _ m) habs
  have hop : nextOpening 1 (1/(8*g))=(m : ℝ)+1/8 := by
    simpa using (nextOpening_eq habs)
  have hclear := bypass_output_clear g h m n hm hg hh hentry1 hentry2 hlo hhi
  refine ⟨hleast,hw,?_,hclear⟩
  refine Or.inr ⟨1,by simp [leftReadings],hw,hop.symm,?_⟩
  intro d hd hdw
  exact nextOpening_le_of_lonely hpos hclear htu.le hd hdw

#print axioms bypass_output_clear
#print axioms native_opposite_pair_bypass
end Fresh.ThreeBlockNativeBypass
