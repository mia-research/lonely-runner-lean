import Fresh.FourBlockOutsideRebase

/-! Original outside2→outside3 handoffs. The third outside cut is carried
from one exact entry closing face, and both moves retain original runners. -/
namespace Fresh.FourBlockTwoOutside
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour Fresh.FourBlockAPAnchor
  Fresh.FourBlockLeftOpening Fresh.FourBlockLeftPacketLift Fresh.FourBlockLeftPacketCharts
  Fresh.FourBlockOutsideTransport Fresh.FourBlockOutsideRebase Fresh.UnitAPPacketChartMotion

noncomputable def firstOpening (c g h j : ℝ) (p q r : ℕ) (m a b e : ℤ) (L : Fin 3 → ℤ) : ℝ :=
  leftOpening c g h j p q r m a b e 1 (L 1)

theorem third_cut_at_first (c g h j : ℝ) (p q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e : ℤ) (Q : ℝ) (L : Fin 3 → ℤ)
    (hcaplo : (L 1 : ℝ)-1/8 < leftReading c g h j p q r 1*Q-(leftLap m a b e p q r 1 : ℝ))
    (hcaphi : leftReading c g h j p q r 1*Q-(leftLap m a b e p q r 1 : ℝ) < (L 1 : ℝ)+1/8)
    (hlo : ((leftLap m a b e p q r 0+L 0 : ℤ) : ℝ)+1/8 ≤ leftReading c g h j p q r 0*Q)
    (hclose : leftReading c g h j p q r 0*
      (((leftLap m a b e p q r 1+L 1 : ℤ) : ℝ)+1/8-leftReading c g h j p q r 1*Q) ≤
      leftReading c g h j p q r 1*(((leftLap m a b e p q r 0+L 0 : ℤ) : ℝ)+5/8-leftReading c g h j p q r 0*Q)) :
    ((leftLap m a b e p q r 0+L 0 : ℤ) : ℝ)+1/8 ≤ leftReading c g h j p q r 0*firstOpening c g h j p q r m a b e L ∧
    leftReading c g h j p q r 0*firstOpening c g h j p q r m a b e L ≤ ((leftLap m a b e p q r 0+L 0 : ℤ) : ℝ)+5/8 := by
  have ht := (capture_opening c g h j p q r hq hr hg hh hj m a b e 1 (L 1) Q hcaplo hcaphi).2.2
  exact Fresh.NativeOpeningRetention.weighted_upper _ _ Q _ _ _ (5/8)
    (reading_pos c g h j p q r hq hr hg hh hj 1) (reading_pos c g h j p q r hq hr hg hh hj 0).le ht.le
    (Fresh.FourBlockLeftOpening.opening_identity c g h j p q r hq hr hg hh hj m a b e 1 (L 1)) hlo hclose

theorem middle_cuts_at_first (c g h j : ℝ) (p q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e : ℤ) (L : Fin 3 → ℤ)
    (hb : ((leftLap m a b e p q r 0+L 0 : ℤ) : ℝ)+1/8 ≤ leftReading c g h j p q r 0*firstOpening c g h j p q r m a b e L ∧
      leftReading c g h j p q r 0*firstOpening c g h j p q r m a b e L ≤ ((leftLap m a b e p q r 0+L 0 : ℤ) : ℝ)+5/8) :
    EntryMiddleCuts c g h j p q r m a b e (firstOpening c g h j p q r m a b e L) L := by
  intro v hv
  fin_cases v
  · exact hb
  · have ho := Fresh.FourBlockLeftOpening.opening_identity c g h j p q r hq hr hg hh hj m a b e 1 (L 1)
    exact ⟨ho.ge,by dsimp [firstOpening]; linarith only [ho]⟩
  · exact (hv rfl).elim

theorem sole_capture_move {ds : Finset ℝ} {d Q P : ℝ} (hd : d∈ds) (hw : InWay d Q)
    (hop : nextOpening d Q=P) (hsole : ∀ e∈ds, InWay e Q → e=d) : IsMove ds Q P := by
  refine Or.inr ⟨d,hd,hw,hop.symm,?_⟩
  intro e he hwe
  rw [hsole e he hwe,hop]

theorem first_move (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e unitLap window : ℤ) (role : Fin 14)
    (Q : ℝ) (L : Fin 3 → ℤ) (initialThird : ℤ)
    (hcaplo : (L 1 : ℝ)-1/8 < leftReading c g h j p q r 1*Q-(leftLap m a b e p q r 1 : ℝ))
    (hcaphi : leftReading c g h j p q r 1*Q-(leftLap m a b e p q r 1 : ℝ) < (L 1 : ℝ)+1/8)
    (hpacket : ChartBands c g h j p q r m a b e unitLap window role Q)
    (hleft : ((leftLap m a b e p q r 0+L 0 : ℤ) : ℝ)+1/8 ≤ leftReading c g h j p q r 0*Q ∧
      leftReading c g h j p q r 0*Q ≤ ((leftLap m a b e p q r 0+L 0 : ℤ) : ℝ)+7/8)
    (hright : ((leftLap m a b e p q r 2+initialThird : ℤ) : ℝ)+1/8 ≤ leftReading c g h j p q r 2*Q ∧
      leftReading c g h j p q r 2*Q ≤ ((leftLap m a b e p q r 2+initialThird : ℤ) : ℝ)+7/8) :
    IsMove (disparitySet (speeds c g h j p q r) 0) Q (firstOpening c g h j p q r m a b e L) := by
  obtain ⟨hw,hop,ht⟩ := capture_opening c g h j p q r hq hr hg hh hj m a b e 1 (L 1) Q hcaplo hcaphi
  have htail := packet_clear c g h j p q r hp hq hr hs m a b e unitLap window role Q hpacket
  have h0 := clear_of_window _ hleft.1 hleft.2
  have h2 := clear_of_window _ hright.1 hright.2
  apply sole_capture_move (mem_disparitySet.mpr ⟨2,by decide,rfl⟩) hw hop
  intro d hd hway
  obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hd
  have hbad : ¬ (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r i-speeds c g h j p q r 0)*Q) := by
    rw [←Fresh.Localisation.distInt_abs_mul]
    exact not_le.mpr hway
  fin_cases i
  · exact (hi rfl).elim
  · exact (hbad h0).elim
  · rfl
  · exact (hbad h2).elim
  · exact (hbad (htail 0)).elim
  · exact (hbad (htail 1)).elim
  · exact (hbad (htail 2)).elim
  · exact (hbad (htail 3)).elim

theorem two_moves (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e unitLap window : ℤ) (role middle finalRole : Fin 14) (middleUnit finalUnit : ℤ)
    (Q : ℝ) (L : Fin 3 → ℤ) (initialThird : ℤ)
    (hcaplo : (L 1 : ℝ)-1/8 < leftReading c g h j p q r 1*Q-(leftLap m a b e p q r 1 : ℝ))
    (hcaphi : leftReading c g h j p q r 1*Q-(leftLap m a b e p q r 1 : ℝ) < (L 1 : ℝ)+1/8)
    (hpacket : ChartBands c g h j p q r m a b e unitLap window role Q)
    (hleft : ((leftLap m a b e p q r 0+L 0 : ℤ) : ℝ)+1/8 ≤ leftReading c g h j p q r 0*Q ∧
      leftReading c g h j p q r 0*Q ≤ ((leftLap m a b e p q r 0+L 0 : ℤ) : ℝ)+7/8)
    (hright : ((leftLap m a b e p q r 2+initialThird : ℤ) : ℝ)+1/8 ≤ leftReading c g h j p q r 2*Q ∧
      leftReading c g h j p q r 2*Q ≤ ((leftLap m a b e p q r 2+initialThird : ℤ) : ℝ)+7/8)
    (hthirdclose : leftReading c g h j p q r 0*
      (((leftLap m a b e p q r 1+L 1 : ℤ) : ℝ)+1/8-leftReading c g h j p q r 1*Q) ≤
      leftReading c g h j p q r 1*(((leftLap m a b e p q r 0+L 0 : ℤ) : ℝ)+5/8-leftReading c g h j p q r 0*Q))
    (hlabel1 : ShiftCompatible role middle (middleUnit-unitLap))
    (hclose1 : RebasedClosing c g h j p q r m a b e unitLap middleUnit window role middle Q (firstOpening c g h j p q r m a b e L))
    (hcap2lo : (L 2 : ℝ)-1/8 < leftReading c g h j p q r 2*firstOpening c g h j p q r m a b e L-(leftLap m a b e p q r 2 : ℝ))
    (hcap2hi : leftReading c g h j p q r 2*firstOpening c g h j p q r m a b e L-(leftLap m a b e p q r 2 : ℝ) < (L 2 : ℝ)+1/8)
    (hlabel2 : ShiftCompatible middle finalRole (finalUnit-middleUnit))
    (hclose2 : RebasedClosing c g h j p q r m a b e middleUnit finalUnit window middle finalRole
      (firstOpening c g h j p q r m a b e L) (leftOpening c g h j p q r m a b e 2 (L 2))) :
    IsMove (disparitySet (speeds c g h j p q r) 0) Q (firstOpening c g h j p q r m a b e L) ∧
    IsMove (disparitySet (speeds c g h j p q r) 0) (firstOpening c g h j p q r m a b e L) (leftOpening c g h j p q r m a b e 2 (L 2)) ∧
    LonelyAt (disparitySet (speeds c g h j p q r) 0) (leftOpening c g h j p q r m a b e 2 (L 2)) := by
  have hmove1 := first_move c g h j p q r hp hq hr hs hg hh hj m a b e unitLap window role Q L initialThird
    hcaplo hcaphi hpacket hleft hright
  have ht1 := (capture_opening c g h j p q r hq hr hg hh hj m a b e 1 (L 1) Q hcaplo hcaphi).2.2
  have hp1 := packet_transport_rebased c g h j p q r hp hq hr hs hg hh hj m a b e unitLap middleUnit window role middle Q
    (firstOpening c g h j p q r m a b e L) ht1.le hpacket hlabel1 hclose1
  have hthird := third_cut_at_first c g h j p q r hq hr hg hh hj m a b e Q L hcaplo hcaphi hleft.1 hthirdclose
  have hmid := middle_cuts_at_first c g h j p q r hq hr hg hh hj m a b e L hthird
  obtain ⟨hw2,hop2,ht2⟩ := capture_opening c g h j p q r hq hr hg hh hj m a b e 2 (L 2)
    (firstOpening c g h j p q r m a b e L) hcap2lo hcap2hi
  have hp2 := packet_transport_rebased c g h j p q r hp hq hr hs hg hh hj m a b e middleUnit finalUnit window middle finalRole
    (firstOpening c g h j p q r m a b e L) (leftOpening c g h j p q r m a b e 2 (L 2)) ht2.le hp1 hlabel2 hclose2
  have hcuts := fast_other_cuts c g h j p q r hq hr hg hh hj m a b e
    (firstOpening c g h j p q r m a b e L) L hcap2lo hcap2hi hmid
  have hclear := left_clear c g h j p q r hp hq hr hs hg hh hj m a b e finalUnit window 2 L finalRole hp2 hcuts
  have hmem : |leftReading c g h j p q r 2| ∈ disparitySet (speeds c g h j p q r) 0 :=
    mem_disparitySet.mpr ⟨3,by decide,rfl⟩
  exact ⟨hmove1,Fresh.FourBlockPacketFrameMoves.move_at_supplied_opening
    (Fresh.FourBlockPacketFrameMoves.native_readings_positive c g h j p q r hq hr hg hh hj) hmem hw2 hop2 hclear,hclear⟩

#print axioms two_moves
#print axioms third_cut_at_first
#print axioms middle_cuts_at_first
#print axioms sole_capture_move
#print axioms first_move
end Fresh.FourBlockTwoOutside
