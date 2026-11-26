import Fresh.FourBlockLongTailThirdMove

/-! The closed third-opening face either isolates the original subject or
forces the next original unit partner to take over. The strict complement
is retained as an actual continuation, not discarded as an exception. -/
namespace Fresh.FourBlockLongTailExit
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailBounds Fresh.FourBlockLongTailPhase

theorem exit_or_continue (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j) (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4) :
    (g+h+j+8*remainder g h j m a b e ≤ 9 →
      LonelyAt (disparitySet (speeds c g h j p q r) 0) (packetOpening g h j m a b e 2)) ∧
    (¬g+h+j+8*remainder g h j m a b e ≤ 9 →
      IsMove (disparitySet (speeds c g h j p q r) 0)
        (packetOpening g h j m a b e 2) (packetOpening g h j m a b e 3)) := by
  obtain ⟨hRlo,hRhi⟩ := native_remainder_band g h j m a b e hg hh hj hsum
  obtain ⟨hT2,hP2⟩ := second_partner_bounds g h j hgpos hhpos hjpos m a b e hRlo hRhi
  have hf4 := packet_phase c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e 2 (by norm_num) (4 : Fin 8) (by norm_num)
  have hf5 := packet_phase c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e 2 (by norm_num) (5 : Fin 8) (by norm_num)
  have hf6 := packet_phase c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e 2 (by norm_num) (6 : Fin 8) (by norm_num)
  have hf7 := packet_phase c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e 2 (by norm_num) (7 : Fin 8) (by norm_num)
  norm_num at hf4 hf5 hf6 hf7
  have hpartner : (speeds c g h j p q r 4-speeds c g h j p q r 0)*packetOpening g h j m a b e 2-
      ((wholeLap m a b e p q r 4-wholeLap m a b e p q r 0 : ℤ) : ℝ) ≤ 1 := by
    push_cast
    linarith
  have hmono := FourBlockEndpoints.speeds_monotone c g h j p q r hq hr hgpos hhpos hjpos
  have hgap := native_phase_gaps c g h j p q r hq hr m a b e hg hh hj
  have hprefix : ∀i : Fin 8,0 < (i : ℕ) → i < (4 : Fin 8) →
      (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r i-speeds c g h j p q r 0)*packetOpening g h j m a b e 2) := by
    intro i hi0 hi4
    exact Fresh.EndpointRetainedSegment.earlier_readings_clear _ _ _ _ _
      (phase_identity c g h j p q r m a b e) hgap hmono hT2.le 4 hpartner i hi0 hi4
  have hc5 : (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r 5-speeds c g h j p q r 0)*packetOpening g h j m a b e 2) := by
    apply clear_of_window (wholeLap m a b e p q r 5-wholeLap m a b e p q r 0+1)
    all_goals push_cast at hf5 ⊢; linarith
  have hc6 : (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r 6-speeds c g h j p q r 0)*packetOpening g h j m a b e 2) := by
    apply clear_of_window (wholeLap m a b e p q r 6-wholeLap m a b e p q r 0+1)
    all_goals push_cast at hf6 ⊢; linarith
  have hc7 : (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r 7-speeds c g h j p q r 0)*packetOpening g h j m a b e 2) := by
    apply clear_of_window (wholeLap m a b e p q r 7-wholeLap m a b e p q r 0+1)
    all_goals push_cast at hf7 ⊢; linarith
  have hothers : ∀i : Fin 8,i≠0 → i≠4 →
      (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r i-speeds c g h j p q r 0)*packetOpening g h j m a b e 2) := by
    intro i hi0 hi4
    by_cases hi5 : i=5
    · subst i; exact hc5
    · by_cases hi6 : i=6
      · subst i; exact hc6
      · by_cases hi7 : i=7
        · subst i; exact hc7
        · apply hprefix i
          · have := Fin.val_ne_of_ne hi0; omega
          · have := Fin.val_ne_of_ne hi4
            have := Fin.val_ne_of_ne hi5
            have := Fin.val_ne_of_ne hi6
            have := Fin.val_ne_of_ne hi7
            have := i.isLt
            change (i : ℕ) < 4
            omega
  constructor
  · intro hface
    have hlow := (exit_face g h j hgpos hhpos hjpos m a b e).2 hface
    have hc4 : (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r 4-speeds c g h j p q r 0)*packetOpening g h j m a b e 2) := by
      apply clear_of_window (wholeLap m a b e p q r 4-wholeLap m a b e p q r 0)
      all_goals push_cast at hf4 ⊢; linarith
    intro d hd
    obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
    rw [Fresh.Localisation.distInt_abs_mul]
    by_cases hi4 : i=4
    · subst i; exact hc4
    · exact hothers i hi0 hi4
  · intro hface
    have hhigh : packetOpening g h j m a b e 2 < (m : ℝ)+1/4 :=
      lt_of_not_ge (fun hbound => hface ((exit_face g h j hgpos hhpos hjpos m a b e).1 hbound))
    have hD4 : speeds c g h j p q r 4-speeds c g h j p q r 0=1+g+h+j := by
      have hd := tail_reading c g h j p q r hp hq hr hs (4 : Fin 8) (by norm_num)
      norm_num at hd
      exact hd
    have hpos4 : 0 < speeds c g h j p q r 4-speeds c g h j p q r 0 := by rw [hD4]; positivity
    have hN4 : wholeLap m a b e p q r 4-wholeLap m a b e p q r 0=spanLap m a b e-3*m := by
      rw [tail_lap p q r hp hq hr hs m a b e (4 : Fin 8) (by norm_num)]
      norm_num [spanLap]
      ring
    have hnear : |(speeds c g h j p q r 4-speeds c g h j p q r 0)*packetOpening g h j m a b e 2-
        ((wholeLap m a b e p q r 4-wholeLap m a b e p q r 0+1 : ℤ) : ℝ)| < 1/8 := by
      rw [abs_lt]
      push_cast at hf4 ⊢
      constructor <;> linarith
    have hw4 : InWay |speeds c g h j p q r 4-speeds c g h j p q r 0| (packetOpening g h j m a b e 2) := by
      rw [abs_of_pos hpos4]
      exact lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (wholeLap m a b e p q r 4-wholeLap m a b e p q r 0+1)) hnear
    have hop4 : nextOpening |speeds c g h j p q r 4-speeds c g h j p q r 0| (packetOpening g h j m a b e 2)=
        packetOpening g h j m a b e 3 := by
      rw [abs_of_pos hpos4,nextOpening_eq hnear,hD4,hN4]
      dsimp [packetOpening]
      push_cast
      congr 1 <;> ring
    refine Or.inr ⟨|speeds c g h j p q r 4-speeds c g h j p q r 0|,
      mem_disparitySet.mpr ⟨4,by decide,rfl⟩,hw4,hop4.symm,?_⟩
    intro d hd hwD
    obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
    by_cases hi4 : i=4
    · subst i; exact hop4.le
    · change distInt (|speeds c g h j p q r i-speeds c g h j p q r 0| * packetOpening g h j m a b e 2) < 1/8 at hwD
      rw [Fresh.Localisation.distInt_abs_mul] at hwD
      exact False.elim ((not_lt_of_ge (hothers i hi0 hi4)) hwD)

#print axioms exit_or_continue
end Fresh.FourBlockLongTailExit
