import Fresh.FourBlockOutsideTransport

/-! A whole unit lap reindexes original packet windows; it does not reset
any runner or discard its phase. The 0123→0000 join is an actual transport. -/
namespace Fresh.FourBlockOutsideRebase
open Fresh Fresh.FourBlockNeighbour Fresh.FourBlockLongTailBounds Fresh.FourBlockAPAnchor
  Fresh.FourBlockLeftOpening Fresh.FourBlockLeftPacketLift Fresh.FourBlockLeftPacketCharts
  Fresh.FourBlockOutsideTransport Fresh.UnitAPPacketChartMotion

def RebasedClosing (c g h j : ℝ) (p q r : ℕ) (m a b e unitBefore unitAfter window : ℤ)
    (before after : Fin 14) (Q P : ℝ) : Prop :=
  Sector after (packetTheta m unitAfter P) ∧
  packetX c g h j p q r m a b e window Q+(maximum after : ℝ)*packetTheta m unitBefore Q-
    (Fresh.UnitAPPacketFourCharts.carry before (maximum after) : ℝ)+
    (speeds c g h j p q r 4-speeds c g h j p q r 0+(maximum after : ℝ))*(P-Q) ≤ 7/8

theorem packet_transport_rebased (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e unitBefore unitAfter window : ℤ)
    (before after : Fin 14) (Q P : ℝ) (hQP : Q ≤ P)
    (hc : ChartBands c g h j p q r m a b e unitBefore window before Q)
    (hlabels : ShiftCompatible before after (unitAfter-unitBefore))
    (hclose : RebasedClosing c g h j p q r m a b e unitBefore unitAfter window before after Q P) :
    ChartBands c g h j p q r m a b e unitAfter window after P := by
  have hbase : 0 ≤ speeds c g h j p q r 4-speeds c g h j p q r 0 := by
    rw [tail_reading c g h j p q r hp hq hr hs 4 (by norm_num)]
    norm_num; linarith
  have het : packetTheta m unitAfter P=packetTheta m unitBefore Q+(P-Q)-((unitAfter-unitBefore : ℤ) : ℝ) := by
    dsimp [packetTheta]; push_cast; ring
  have ht := transport_rebased before after (unitAfter-unitBefore)
    (packetX c g h j p q r m a b e window Q) (packetTheta m unitBefore Q)
    (speeds c g h j p q r 4-speeds c g h j p q r 0) (P-Q) hc hlabels hbase (sub_nonneg.mpr hQP)
    (by rw [←het]; exact hclose.1) hclose.2
  have hx := first_phase_advance c g h j p q r m a b e Q P
  have hex : firstPhase c g h j p q r m a b e P-(window : ℝ)=
      packetX c g h j p q r m a b e window Q+
      (speeds c g h j p q r 4-speeds c g h j p q r 0)*(P-Q) := by dsimp [packetX]; linarith only [hx]
  change Fresh.UnitAPPacketFourCharts.Chart after _ _
  rw [hex]
  change Fresh.UnitAPPacketFourCharts.Chart after _ (packetTheta m unitAfter P)
  rwa [het]

#print axioms packet_transport_rebased
end Fresh.FourBlockOutsideRebase
