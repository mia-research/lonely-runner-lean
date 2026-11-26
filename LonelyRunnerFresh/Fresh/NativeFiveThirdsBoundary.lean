import Fresh.NativeReturnedOpeningGeometry

/-! Exact native 5/3 grid at a selected own opening, including its closed
upper-clear face. The integer label remains arbitrary and unbounded. -/
namespace Fresh.NativeFiveThirdsBoundary
open Fresh Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeOneReaderDeformation Fresh.FastestCaptureRetention Fresh.NativeOpeningReversal

theorem grid_clear (d s T : ℝ) (M : ℤ) (ho : d*T=(M : ℝ)+1/8)
    (hr : 3*s=5*d) : 1/8  ≤  distInt (s*T) := by
  have hm := congrArg (fun z : ℝ=>z*T) hr
  have he : 3*(s*T)=5*((M : ℝ)+1/8) := by nlinarith only [hm,ho]
  have hrem : M%3=0 ∨ M%3=1 ∨ M%3=2 := by omega
  rcases hrem with hrem|hrem|hrem
  · have hi : M=3*(M/3) := by omega
    have hic : (M : ℝ)=3*((M/3 : ℤ) : ℝ) := by exact_mod_cast hi
    apply clear_of_window (5*(M/3))  <;> push_cast  <;> linarith only [he,hic]
  · have hi : M=3*(M/3)+1 := by omega
    have hic : (M : ℝ)=3*((M/3 : ℤ) : ℝ)+1 := by exact_mod_cast hi
    apply clear_of_window (5*(M/3)+1)  <;> push_cast  <;> linarith only [he,hic]
  · have hi : M=3*(M/3)+2 := by omega
    have hic : (M : ℝ)=3*((M/3 : ℤ) : ℝ)+2 := by exact_mod_cast hi
    apply clear_of_window (5*(M/3)+3)  <;> push_cast  <;> linarith only [he,hic]

theorem captured_strict_face (d s U : ℝ) (hd : 0 < d)
    (hcap : InWay s (labelledOpening d U)) (hle : 3*s ≤ 5*d) : 3*s < 5*d := by
  apply lt_of_le_of_ne hle
  intro he
  have ho := labelled_opening_identity d U hd
  exact not_lt_of_ge (grid_clear d s _ _ ho he) hcap

-- At the other 5/3 face, simultaneous entry capture fixes the native
-- residue of the first setter; the next captured opening retains it.
theorem simultaneous_capture_residue (d s R : ℝ) (hr : 3*s=5*d)
    (hd : InWay d R) (hs : InWay s R) : label (d*R)%3=0 := by
  let M := label (d*R)
  have hc := capture_at_label d R hd
  have hm := congrArg (fun z : ℝ=>z*R) hr
  have hrem : M%3=0 ∨ M%3=1 ∨ M%3=2 := by omega
  rcases hrem with hh|hh|hh
  · exact hh
  · have hi : M=3*(M/3)+1 := by omega
    have hic : (M : ℝ)=3*((M/3 : ℤ) : ℝ)+1 := by exact_mod_cast hi
    have hclear : 1/8 ≤ distInt (s*R) := by
      apply clear_of_window (5*(M/3)+1) <;> push_cast <;>
        dsimp [M] at * <;> nlinarith only [hc.1,hc.2,hm,hic]
    exact (not_lt_of_ge hclear hs).elim
  · have hi : M=3*(M/3)+2 := by omega
    have hic : (M : ℝ)=3*((M/3 : ℤ) : ℝ)+2 := by exact_mod_cast hi
    have hclear : 1/8 ≤ distInt (s*R) := by
      apply clear_of_window (5*(M/3)+3) <;> push_cast <;>
        dsimp [M] at * <;> nlinarith only [hc.1,hc.2,hm,hic]
    exact (not_lt_of_ge hclear hs).elim

theorem first_grid_retained (d j s R : ℝ) (hd : 0<d) (hj : 0<j)
    (hr : 3*s=5*d) (hsj : 3*s≤5*j) (hwd : InWay d R) (hws : InWay s R)
    (hwj : InWay j (labelledOpening d R)) :
    1/8 ≤ distInt (s*labelledOpening j (labelledOpening d R)) := by
  have hres := simultaneous_capture_residue d s R hr hwd hws
  have hi : label (d*R)=3*(label (d*R)/3) := by omega
  have hic : (label (d*R) : ℝ)=3*((label (d*R)/3 : ℤ) : ℝ) := by exact_mod_cast hi
  have ho := labelled_opening_identity d R hd
  have hm := congrArg (fun z : ℝ=>z*labelledOpening d R) hr
  have hstep := Fresh.NativeThirdReaderRetention.captured_labelled_advance j (labelledOpening d R) hj hwj
  have hratio := mul_le_mul_of_nonneg_right hsj hstep.1.le
  have hspos : 0<s := by linarith only [hr,hd]
  have hmono := mul_pos hspos hstep.1
  apply clear_of_window (5*(label (d*R)/3)) <;> push_cast <;>
    nlinarith only [ho,hm,hic,hstep.2,hratio,hmono]

theorem recapture_strict_ratios (d j s R : ℝ) (hd : 0<d) (hj : 0<j)
    (hsg : 3*s≤5*d) (hsj : 3*s≤5*j) (hwd : InWay d R) (hws : InWay s R)
    (hwj : InWay j (labelledOpening d R))
    (hret : InWay s (labelledOpening j (labelledOpening d R))) :
    3*s<5*d ∧ 3*s<5*j := by
  refine ⟨lt_of_le_of_ne hsg ?_,captured_strict_face j s _ hj hret hsj⟩
  intro he
  exact not_lt_of_ge (first_grid_retained d j s R hd hj he hsj hwd hws hwj) hret

#print axioms recapture_strict_ratios

#print axioms simultaneous_capture_residue
#print axioms first_grid_retained

#print axioms grid_clear
#print axioms captured_strict_face
end Fresh.NativeFiveThirdsBoundary
