import Fresh.FourBlockLeftPacketChartsArrangement

/-! Closed lower packet faces join original left-opening charts to the
named AP opening rules. The original return integer is derived, with its
whole unit lap and carry label retained. -/
namespace Fresh.FourBlockPacketChartJoins
open Fresh Fresh.FourBlockNeighbour Fresh.FourBlockLongTailBounds Fresh.FourBlockAPAnchor
  Fresh.FourBlockLeftPacketLift Fresh.FourBlockLeftPacketCharts

theorem chart_residual_bounds (role : Fin 14) (x theta : ℝ)
    (hc : Fresh.UnitAPPacketFourCharts.Chart role x theta) : 0 ≤ theta ∧ theta ≤ 1 := by
  fin_cases role <;> dsimp [Fresh.UnitAPPacketFourCharts.Chart] at hc
  all_goals obtain ⟨h0,h1,hl,hh⟩ := hc
  all_goals constructor <;> linarith

theorem lower_face_opening (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e unitLap window : ℤ)
    (role : Fin 14) (P : ℝ) (i : Fin 4)
    (hface : firstPhase c g h j p q r m a b e P-(window : ℝ)+
      (i : ℝ)*(P-(m : ℝ)-(unitLap : ℝ))-(Fresh.UnitAPPacketFourCharts.carry role i : ℝ)=1/8) :
    P=anchorOpening g h j m a b e (window+(i.val : ℤ)*unitLap+Fresh.UnitAPPacketFourCharts.carry role i) i := by
  have hphase := packet_phase c g h j p q r hp hq hr hs m a b e P i
  rw [tail_reading c g h j p q r hp hq hr hs _ (by dsimp [packetIndex]; omega),
    tail_lap p q r hp hq hr hs m a b e _ (by dsimp [packetIndex]; omega)] at hphase
  have hanchor := Fresh.FourBlockAPAnchor.opening_identity g h j hg hh hj m a b e
    (window+(i.val : ℤ)*unitLap+Fresh.UnitAPPacketFourCharts.carry role i) i
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hpos : 0 < (i : ℝ)+1+g+h+j := by linarith
  dsimp [packetIndex] at hphase
  push_cast at hphase hanchor
  nlinarith only [hphase,hanchor,hface,hpos]

theorem lower_face_cell (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e unitLap window : ℤ)
    (role : Fin 14) (P : ℝ) (i : Fin 4)
    (hc : ChartBands c g h j p q r m a b e unitLap window role P)
    (hface : firstPhase c g h j p q r m a b e P-(window : ℝ)+
      (i : ℝ)*(P-(m : ℝ)-(unitLap : ℝ))-(Fresh.UnitAPPacketFourCharts.carry role i : ℝ)=1/8) :
    Fresh.UnitAPPacketFourLift.Cell i (P-(m : ℝ)-(unitLap : ℝ)) := by
  have hjoin := lower_face_opening c g h j p q r hp hq hr hs hg hh hj m a b e unitLap window role P i hface
  have hb := chart_residual_bounds role _ _ hc
  have hclear := packet_clear c g h j p q r hp hq hr hs m a b e unitLap window role P hc
  rw [hjoin] at hb hclear ⊢
  exact (packet_cell_iff c g h j p q r hp hq hr hs hg hh hj m a b e
    (window+(i.val : ℤ)*unitLap+Fresh.UnitAPPacketFourCharts.carry role i) unitLap i hb.1 hb.2).2 hclear

#print axioms chart_residual_bounds
#print axioms lower_face_opening
#print axioms lower_face_cell
end Fresh.FourBlockPacketChartJoins
