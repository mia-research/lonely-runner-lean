import Fresh.UnitAPPacketFourCharts
import Fresh.FourBlockPacketLiftMoves

/-! Fourteen native AP carry charts at an original left opening. Each
requires only its two extremal packet faces and the two other left cuts. -/
namespace Fresh.FourBlockLeftPacketCharts
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour Fresh.FourBlockAPAnchor
  Fresh.FourBlockLeftOpening Fresh.FourBlockLeftPacketLift Fresh.FourBlockPacketFrameMoves

noncomputable def ChartBands (c g h j : ℝ) (p q r : ℕ) (m a b e unitLap window : ℤ)
    (role : Fin 14) (P : ℝ) : Prop :=
  Fresh.UnitAPPacketFourCharts.Chart role
    (firstPhase c g h j p q r m a b e P-(window : ℝ)) (P-(m : ℝ)-(unitLap : ℝ))

theorem packet_clear (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (m a b e unitLap window : ℤ) (role : Fin 14) (P : ℝ)
    (hc : ChartBands c g h j p q r m a b e unitLap window role P) (i : Fin 4) :
    (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r (packetIndex i)-speeds c g h j p q r 0)*P) := by
  have hwin := Fresh.UnitAPPacketFourCharts.chart_windows role
    (firstPhase c g h j p q r m a b e P-(window : ℝ)) (P-(m : ℝ)-(unitLap : ℝ)) hc i
  have hid := packet_phase c g h j p q r hp hq hr hs m a b e P i
  apply clear_of_window (wholeLap m a b e p q r (packetIndex i)-wholeLap m a b e p q r 0+
    window+(i.val : ℤ)*unitLap+Fresh.UnitAPPacketFourCharts.carry role i)
  all_goals push_cast at hid ⊢; nlinarith only [hid,hwin.1,hwin.2]

theorem packet_charts_iff (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (m a b e unitLap window : ℤ) (P : ℝ)
    (hx0 : (1/8 : ℝ) ≤ firstPhase c g h j p q r m a b e P-(window : ℝ))
    (hx1 : firstPhase c g h j p q r m a b e P-(window : ℝ) ≤ (7/8 : ℝ))
    (ht0 : 0 ≤ P-(m : ℝ)-(unitLap : ℝ)) (ht1 : P-(m : ℝ)-(unitLap : ℝ) ≤ 1) :
    (∃ role : Fin 14, ChartBands c g h j p q r m a b e unitLap window role P) ↔
      ∀ i : Fin 4, (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r (packetIndex i)-speeds c g h j p q r 0)*P) := by
  constructor
  · rintro ⟨role,hc⟩
    exact packet_clear c g h j p q r hp hq hr hs m a b e unitLap window role P hc
  · intro hclear
    apply Fresh.UnitAPPacketFourCharts.clear_chart _ _ hx0 hx1 ht0 ht1
    intro i
    have hi := hclear i
    have hid := packet_phase c g h j p q r hp hq hr hs m a b e P i
    have he : (speeds c g h j p q r (packetIndex i)-speeds c g h j p q r 0)*P=
        (firstPhase c g h j p q r m a b e P-(window : ℝ)+(i : ℝ)*(P-(m : ℝ)-(unitLap : ℝ)))+
        ((wholeLap m a b e p q r (packetIndex i)-wholeLap m a b e p q r 0+window+(i.val : ℤ)*unitLap : ℤ) : ℝ) := by
      push_cast at hid ⊢
      nlinarith only [hid]
    rwa [he,distInt_add_int] at hi

theorem left_clear (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e unitLap window : ℤ) (u : Fin 3) (L : Fin 3 → ℤ) (role : Fin 14)
    (hf : ChartBands c g h j p q r m a b e unitLap window role (leftOpening c g h j p q r m a b e u (L u)))
    (hl : OtherLeftBandsAt c g h j p q r m a b e (leftOpening c g h j p q r m a b e u (L u)) L u) :
    LonelyAt (disparitySet (speeds c g h j p q r) 0) (leftOpening c g h j p q r m a b e u (L u)) := by
  have hb := bands_at_opening c g h j p q r hq hr hg hh hj m a b e u L hl
  have hprefix (v : Fin 3) : (1/8 : ℝ) ≤ distInt (leftReading c g h j p q r v*leftOpening c g h j p q r m a b e u (L u)) :=
    clear_of_window _ (hb v).1 (hb v).2
  have htail := packet_clear c g h j p q r hp hq hr hs m a b e unitLap window role
    (leftOpening c g h j p q r m a b e u (L u)) hf
  intro d hd
  obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
  rw [Fresh.Localisation.distInt_abs_mul]
  fin_cases i
  · exact (hi0 rfl).elim
  · simpa only [leftReading,Fresh.FourBlockOuterTailClear.prefixIndex] using hprefix 0
  · simpa only [leftReading,Fresh.FourBlockOuterTailClear.prefixIndex] using hprefix 1
  · simpa only [leftReading,Fresh.FourBlockOuterTailClear.prefixIndex] using hprefix 2
  · exact htail 0
  · exact htail 1
  · exact htail 2
  · exact htail 3

theorem left_move (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e unitLap window : ℤ) (u : Fin 3) (L : Fin 3 → ℤ) (role : Fin 14)
    (hf : ChartBands c g h j p q r m a b e unitLap window role (leftOpening c g h j p q r m a b e u (L u)))
    (hl : OtherLeftBandsAt c g h j p q r m a b e (leftOpening c g h j p q r m a b e u (L u)) L u) (t : ℝ)
    (hcaplo : (L u : ℝ)-1/8 < leftReading c g h j p q r u*t-(leftLap m a b e p q r u : ℝ))
    (hcaphi : leftReading c g h j p q r u*t-(leftLap m a b e p q r u : ℝ) < (L u : ℝ)+1/8) :
    IsMove (disparitySet (speeds c g h j p q r) 0) t (leftOpening c g h j p q r m a b e u (L u)) := by
  obtain ⟨hw,hop,ht⟩ := capture_opening c g h j p q r hq hr hg hh hj m a b e u (L u) t hcaplo hcaphi
  have hmem : |leftReading c g h j p q r u| ∈ disparitySet (speeds c g h j p q r) 0 := by
    refine mem_disparitySet.mpr ⟨Fresh.FourBlockOuterTailClear.prefixIndex u,?_,rfl⟩
    intro heq
    have hc := congrArg Fin.val heq
    simp [Fresh.FourBlockOuterTailClear.prefixIndex] at hc
  exact move_at_supplied_opening (native_readings_positive c g h j p q r hq hr hg hh hj) hmem hw hop
    (left_clear c g h j p q r hp hq hr hs hg hh hj m a b e unitLap window u L role hf hl)

#print axioms packet_charts_iff
#print axioms left_move
#print axioms packet_clear
#print axioms left_clear
end Fresh.FourBlockLeftPacketCharts
