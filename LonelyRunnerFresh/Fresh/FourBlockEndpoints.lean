import Fresh.FourBlockNeighbourJoins

/-! Original endpoint geometry for every positive four-block partition.
Original totalgap≤3 and singleton-end guards retain direct1/8 isolation.
Endpoint controls include qualified passes and unqualified failures. -/
namespace Fresh.FourBlockEndpoints
open Fresh Fresh.FourBlockNeighbour

theorem adjacent_speed_gap (c g h j : ℝ) (p q r : ℕ)
    (hq : 1 ≤ q) (hr : 1 ≤ r) (i : Fin 7) :
    speeds c g h j p q r i.succ-speeds c g h j p q r i.castSucc =
      if (i : ℕ)+1=p then g else if (i : ℕ)+1=p+q then h
      else if (i : ℕ)+1=p+q+r then j else 1 := by
  have hd := adjacent_phase_gap c g h j p q r hq hr 0 0 0 0 i
  have hl := phase_identity c g h j p q r 0 0 0 0 i.castSucc
  have hu := phase_identity c g h j p q r 0 0 0 0 i.succ
  norm_num [wholeLap] at hd hl hu
  split_ifs at hd ⊢ <;> linarith

theorem speeds_monotone (c g h j : ℝ) (p q r : ℕ)
    (hq : 1 ≤ q) (hr : 1 ≤ r) (hg : 0<g) (hh : 0<h) (hj : 0<j) :
    Monotone (speeds c g h j p q r) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  have hd := adjacent_speed_gap c g h j p q r hq hr i
  split_ifs at hd <;> linarith

theorem speed_span (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 7) :
    speeds c g h j p q r 7-speeds c g h j p q r 0=4+g+h+j := by
  have hd := phase_span c g h j p q r hp hq hr hs 0 0 0 0
  have hl := phase_identity c g h j p q r 0 0 0 0 0
  have hu := phase_identity c g h j p q r 0 0 0 0 7
  norm_num [wholeLap] at hd hl hu
  linarith

theorem left_direct (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 7)
    (hg : 0<g) (hh : 0<h) (hj : 0<j) (hsmall : g+h+j ≤ 3)
    (hleft : p=1 → 1 ≤ g) : IsolatedAt (speeds c g h j p q r) 0 (1/8) := by
  have hmono := speeds_monotone c g h j p q r hq hr hg hh hj
  have hspan := speed_span c g h j p q r hp hq hr hs
  have hstep := adjacent_speed_gap c g h j p q r hq hr (0 : Fin 7)
  have hcut2 : (1 : ℕ)≠p+q := by omega
  have hcut3 : (1 : ℕ)≠p+q+r := by omega
  simp only [Fin.val_zero,zero_add,if_neg hcut2,if_neg hcut3] at hstep
  change speeds c g h j p q r 1-speeds c g h j p q r 0=(if (1 : ℕ)=p then g else 1) at hstep
  have hnear : 1 ≤ speeds c g h j p q r 1-speeds c g h j p q r 0 := by
    rw [hstep]
    split_ifs with h1
    · exact hleft h1.symm
    · norm_num
  intro i hi
  have hi1 : (1 : Fin 8) ≤ i := by
    have := Fin.val_ne_of_ne hi
    change (1 : ℕ) ≤ (i : ℕ)
    omega
  have hl := hmono hi1
  have hu := hmono (Fin.le_last i)
  change speeds c g h j p q r i ≤ speeds c g h j p q r 7 at hu
  apply Fresh.Localisation.clear_of_window 0 <;> push_cast <;> nlinarith

theorem right_direct (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 7)
    (hg : 0<g) (hh : 0<h) (hj : 0<j) (hsmall : g+h+j ≤ 3)
    (hright : p+q+r=7 → 1 ≤ j) : IsolatedAt (speeds c g h j p q r) 7 (1/8) := by
  have hmono := speeds_monotone c g h j p q r hq hr hg hh hj
  have hspan := speed_span c g h j p q r hp hq hr hs
  have hstep := adjacent_speed_gap c g h j p q r hq hr (6 : Fin 7)
  have hcut1 : (7 : ℕ)≠p := by omega
  have hcut2 : (7 : ℕ)≠p+q := by omega
  change speeds c g h j p q r 7-speeds c g h j p q r 6=
    (if (7 : ℕ)=p then g else if (7 : ℕ)=p+q then h else if (7 : ℕ)=p+q+r then j else 1) at hstep
  simp only [if_neg hcut1,if_neg hcut2] at hstep
  have hnear : 1 ≤ speeds c g h j p q r 7-speeds c g h j p q r 6 := by
    rw [hstep]
    split_ifs with h7
    · exact hright h7.symm
    · norm_num
  intro i hi
  have hi6 : i ≤ (6 : Fin 8) := by
    have := Fin.val_ne_of_ne hi
    have := i.isLt
    change (i : ℕ) ≤ (6 : ℕ)
    omega
  have hl := hmono (Fin.zero_le i)
  change speeds c g h j p q r 0 ≤ speeds c g h j p q r i at hl
  have hu := hmono hi6
  apply Fresh.Localisation.clear_of_window (-1) <;> push_cast <;> nlinarith

#print axioms adjacent_speed_gap
#print axioms speeds_monotone
#print axioms speed_span
#print axioms left_direct
#print axioms right_direct
end Fresh.FourBlockEndpoints
