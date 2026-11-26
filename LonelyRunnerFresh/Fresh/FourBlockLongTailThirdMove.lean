import Fresh.FourBlockLongTailPhase

/-! The second unit partner is the next actual setter. All earlier readings
and the already opened far readings are retained at this same opening. -/
namespace Fresh.FourBlockLongTailThirdMove
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailBounds Fresh.FourBlockLongTailPhase

theorem first_partner_eq (g h j : ℝ) (m a b e : ℤ) :
    packetOpening g h j m a b e 1=
      (((spanLap m a b e-m : ℤ) : ℝ)+9/8)/(3+g+h+j) := by
  dsimp [packetOpening]
  norm_num
  congr 1 <;> ring

theorem third_move (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j) (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4) :
    IsMove (disparitySet (speeds c g h j p q r) 0)
      (packetOpening g h j m a b e 1) (packetOpening g h j m a b e 2) := by
  obtain ⟨hRlo,hRhi⟩ := native_remainder_band g h j m a b e hg hh hj hsum
  obtain ⟨hT1,hP1⟩ := first_partner_bounds g h j hgpos hhpos hjpos m a b e hRlo hRhi
  have hf5 := packet_phase c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e 1 (by norm_num) (5 : Fin 8) (by norm_num)
  have hf6 := packet_phase c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e 1 (by norm_num) (6 : Fin 8) (by norm_num)
  have hf7 := packet_phase c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e 1 (by norm_num) (7 : Fin 8) (by norm_num)
  norm_num at hf5 hf6 hf7
  have hD5 : speeds c g h j p q r 5-speeds c g h j p q r 0=2+g+h+j := by
    have hd := tail_reading c g h j p q r hp hq hr hs (5 : Fin 8) (by norm_num)
    norm_num at hd
    exact hd
  have hpos5 : 0 < speeds c g h j p q r 5-speeds c g h j p q r 0 := by rw [hD5]; positivity
  have hN5 : wholeLap m a b e p q r 5-wholeLap m a b e p q r 0=spanLap m a b e-2*m := by
    rw [tail_lap p q r hp hq hr hs m a b e (5 : Fin 8) (by norm_num)]
    norm_num [spanLap]
    ring
  have hnear : |(speeds c g h j p q r 5-speeds c g h j p q r 0)*packetOpening g h j m a b e 1-
      ((wholeLap m a b e p q r 5-wholeLap m a b e p q r 0+1 : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt]
    push_cast at hf5 ⊢
    constructor <;> linarith
  have hw5 : InWay |speeds c g h j p q r 5-speeds c g h j p q r 0| (packetOpening g h j m a b e 1) := by
    rw [abs_of_pos hpos5]
    exact lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (wholeLap m a b e p q r 5-wholeLap m a b e p q r 0+1)) hnear
  have hop5 : nextOpening |speeds c g h j p q r 5-speeds c g h j p q r 0| (packetOpening g h j m a b e 1)=
      packetOpening g h j m a b e 2 := by
    rw [abs_of_pos hpos5,nextOpening_eq hnear,hD5,hN5]
    dsimp [packetOpening]
    push_cast
    congr 1 <;> ring
  have hc6 : (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r 6-speeds c g h j p q r 0)*packetOpening g h j m a b e 1) := by
    apply clear_of_window (wholeLap m a b e p q r 6-wholeLap m a b e p q r 0+1)
    all_goals push_cast at hf6 ⊢; linarith
  have hc7 : (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r 7-speeds c g h j p q r 0)*packetOpening g h j m a b e 1) := by
    apply clear_of_window (wholeLap m a b e p q r 7-wholeLap m a b e p q r 0+1)
    all_goals push_cast at hf7 ⊢; linarith
  have hpartner : (speeds c g h j p q r 5-speeds c g h j p q r 0)*packetOpening g h j m a b e 1-
      ((wholeLap m a b e p q r 5-wholeLap m a b e p q r 0 : ℤ) : ℝ) ≤ 1 := by
    push_cast
    linarith
  have hmono := FourBlockEndpoints.speeds_monotone c g h j p q r hq hr hgpos hhpos hjpos
  have hgap := native_phase_gaps c g h j p q r hq hr m a b e hg hh hj
  have hprefix : ∀i : Fin 8,0 < (i : ℕ) → i < (5 : Fin 8) →
      (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r i-speeds c g h j p q r 0)*packetOpening g h j m a b e 1) := by
    intro i hi0 hi5
    exact Fresh.EndpointRetainedSegment.earlier_readings_clear _ _ _ _ _
      (phase_identity c g h j p q r m a b e) hgap hmono hT1.le 5 hpartner i hi0 hi5
  refine Or.inr ⟨|speeds c g h j p q r 5-speeds c g h j p q r 0|,
    mem_disparitySet.mpr ⟨5,by decide,rfl⟩,hw5,hop5.symm,?_⟩
  intro d hd hwD
  obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
  by_cases hi5 : i=5
  · subst i
    exact hop5.le
  · have hclear : (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r i-speeds c g h j p q r 0)*packetOpening g h j m a b e 1) := by
      by_cases hi6 : i=6
      · subst i; exact hc6
      · by_cases hi7 : i=7
        · subst i; exact hc7
        · apply hprefix i
          · have := Fin.val_ne_of_ne hi0; omega
          · have := Fin.val_ne_of_ne hi5
            have := Fin.val_ne_of_ne hi6
            have := Fin.val_ne_of_ne hi7
            have := i.isLt
            change (i : ℕ) < 5
            omega
    change distInt (|speeds c g h j p q r i-speeds c g h j p q r 0| * packetOpening g h j m a b e 1) < 1/8 at hwD
    rw [Fresh.Localisation.distInt_abs_mul] at hwD
    exact False.elim ((not_lt_of_ge hclear) hwD)

#print axioms first_partner_eq
#print axioms third_move
end Fresh.FourBlockLongTailThirdMove
