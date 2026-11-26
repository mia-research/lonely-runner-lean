import Fresh.NativeOpeningRetention
import Fresh.UnitAPPacketChartMotion

/-! Original outside openings transport the AP packet from entry faces.
The two other outside cuts are derived by native speed order. -/
namespace Fresh.FourBlockOutsideTransport
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockLongTailBounds Fresh.FourBlockAPAnchor Fresh.FourBlockLeftOpening
  Fresh.FourBlockLeftPacketLift Fresh.FourBlockLeftPacketCharts Fresh.UnitAPPacketChartMotion

noncomputable def packetX (c g h j : ℝ) (p q r : ℕ) (m a b e window : ℤ) (Q : ℝ) : ℝ :=
  firstPhase c g h j p q r m a b e Q-(window : ℝ)

noncomputable def packetTheta (m unitLap : ℤ) (Q : ℝ) : ℝ := Q-(m : ℝ)-(unitLap : ℝ)

theorem first_phase_advance (c g h j : ℝ) (p q r : ℕ) (m a b e : ℤ) (Q P : ℝ) :
    firstPhase c g h j p q r m a b e P=firstPhase c g h j p q r m a b e Q+
      (speeds c g h j p q r 4-speeds c g h j p q r 0)*(P-Q) := by
  dsimp [firstPhase]; ring

def PacketClosing (c g h j : ℝ) (p q r : ℕ) (m a b e unitLap window : ℤ)
    (after : Fin 14) (Q P : ℝ) : Prop :=
  Sector after (packetTheta m unitLap Q+(P-Q)) ∧
  packetX c g h j p q r m a b e window Q+(maximum after : ℝ)*packetTheta m unitLap Q-
    (Fresh.UnitAPPacketFourCharts.carry after (maximum after) : ℝ)+
    (speeds c g h j p q r 4-speeds c g h j p q r 0+(maximum after : ℝ))*(P-Q) ≤ 7/8

theorem packet_transport (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e unitLap window : ℤ)
    (before after : Fin 14) (Q P : ℝ) (hQP : Q ≤ P)
    (hc : ChartBands c g h j p q r m a b e unitLap window before Q)
    (hlabels : Compatible before after)
    (hclose : PacketClosing c g h j p q r m a b e unitLap window after Q P) :
    ChartBands c g h j p q r m a b e unitLap window after P := by
  have hbase : 0 ≤ speeds c g h j p q r 4-speeds c g h j p q r 0 := by
    rw [tail_reading c g h j p q r hp hq hr hs 4 (by norm_num)]
    norm_num; linarith
  have ht := transport before after (packetX c g h j p q r m a b e window Q)
    (packetTheta m unitLap Q) (speeds c g h j p q r 4-speeds c g h j p q r 0) (P-Q)
    hc hlabels hbase (sub_nonneg.mpr hQP) hclose.1 hclose.2
  have hx := first_phase_advance c g h j p q r m a b e Q P
  have hex : firstPhase c g h j p q r m a b e P-(window : ℝ)=
      packetX c g h j p q r m a b e window Q+
      (speeds c g h j p q r 4-speeds c g h j p q r 0)*(P-Q) := by dsimp [packetX]; linarith only [hx]
  have het : P-(m : ℝ)-(unitLap : ℝ)=packetTheta m unitLap Q+(P-Q) := by dsimp [packetTheta]; ring
  dsimp [ChartBands]
  rwa [hex,het]

def EntryMiddleCuts (c g h j : ℝ) (p q r : ℕ) (m a b e : ℤ) (Q : ℝ) (L : Fin 3 → ℤ) : Prop :=
  ∀ v : Fin 3, v≠2 → ((leftLap m a b e p q r v+L v : ℤ) : ℝ)+1/8 ≤ leftReading c g h j p q r v*Q ∧
    leftReading c g h j p q r v*Q ≤ ((leftLap m a b e p q r v+L v : ℤ) : ℝ)+5/8

theorem earlier_cut_order (c g h j : ℝ) (p q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (v : Fin 3) :
    leftReading c g h j p q r v ≤ leftReading c g h j p q r 2 := by
  have hm : StrictMono (speeds c g h j p q r) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro idx
    have hd := Fresh.FourBlockEndpoints.adjacent_speed_gap c g h j p q r hq hr idx
    split_ifs at hd <;> linarith
  apply sub_le_sub_right (hm.monotone ?_) _
  change v.val+1 ≤ 2+1
  omega

theorem fast_other_cuts (c g h j : ℝ) (p q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e : ℤ) (Q : ℝ) (L : Fin 3 → ℤ)
    (hlo : (L 2 : ℝ)-1/8 < leftReading c g h j p q r 2*Q-(leftLap m a b e p q r 2 : ℝ))
    (hhi : leftReading c g h j p q r 2*Q-(leftLap m a b e p q r 2 : ℝ) < (L 2 : ℝ)+1/8)
    (hmiddle : EntryMiddleCuts c g h j p q r m a b e Q L) :
    OtherLeftBandsAt c g h j p q r m a b e (leftOpening c g h j p q r m a b e 2 (L 2)) L 2 := by
  intro v hv
  have hop := Fresh.FourBlockLeftOpening.opening_identity c g h j p q r hq hr hg hh hj m a b e 2 (L 2)
  have hb := hmiddle v hv
  have hnear0 : ((leftLap m a b e p q r 2+L 2 : ℤ) : ℝ)-1/8 < leftReading c g h j p q r 2*Q := by push_cast; linarith
  have hnear1 : leftReading c g h j p q r 2*Q < ((leftLap m a b e p q r 2+L 2 : ℤ) : ℝ)+1/8 := by push_cast; linarith
  have hh' := Fresh.NativeOpeningRetention.slower_window _ _ Q _ _ _
    (reading_pos c g h j p q r hq hr hg hh hj 2)
    (reading_pos c g h j p q r hq hr hg hh hj v).le
    (earlier_cut_order c g h j p q r hq hr hg hh hj v) hop hnear0 hnear1 hb.1 hb.2
  exact ⟨hh'.1,hh'.2.le⟩

theorem forced_fast_clear (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e unitLap window : ℤ)
    (before after : Fin 14) (Q : ℝ) (L : Fin 3 → ℤ)
    (hlo : (L 2 : ℝ)-1/8 < leftReading c g h j p q r 2*Q-(leftLap m a b e p q r 2 : ℝ))
    (hhi : leftReading c g h j p q r 2*Q-(leftLap m a b e p q r 2 : ℝ) < (L 2 : ℝ)+1/8)
    (hmiddle : EntryMiddleCuts c g h j p q r m a b e Q L)
    (hc : ChartBands c g h j p q r m a b e unitLap window before Q)
    (hlabels : Compatible before after)
    (hclose : PacketClosing c g h j p q r m a b e unitLap window after Q
      (leftOpening c g h j p q r m a b e 2 (L 2))) :
    LonelyAt (disparitySet (speeds c g h j p q r) 0) (leftOpening c g h j p q r m a b e 2 (L 2)) := by
  have htime := (capture_opening c g h j p q r hq hr hg hh hj m a b e 2 (L 2) Q hlo hhi).2.2
  have hpacket := packet_transport c g h j p q r hp hq hr hs hg hh hj m a b e unitLap window before after Q
    (leftOpening c g h j p q r m a b e 2 (L 2)) htime.le hc hlabels hclose
  have hleft := fast_other_cuts c g h j p q r hq hr hg hh hj m a b e Q L hlo hhi hmiddle
  exact left_clear c g h j p q r hp hq hr hs hg hh hj m a b e unitLap window 2 L after hpacket hleft

theorem forced_fast_move (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e unitLap window : ℤ)
    (before after : Fin 14) (Q : ℝ) (L : Fin 3 → ℤ)
    (hlo : (L 2 : ℝ)-1/8 < leftReading c g h j p q r 2*Q-(leftLap m a b e p q r 2 : ℝ))
    (hhi : leftReading c g h j p q r 2*Q-(leftLap m a b e p q r 2 : ℝ) < (L 2 : ℝ)+1/8)
    (hmiddle : EntryMiddleCuts c g h j p q r m a b e Q L)
    (hc : ChartBands c g h j p q r m a b e unitLap window before Q)
    (hlabels : Compatible before after)
    (hclose : PacketClosing c g h j p q r m a b e unitLap window after Q
      (leftOpening c g h j p q r m a b e 2 (L 2))) :
    IsMove (disparitySet (speeds c g h j p q r) 0) Q (leftOpening c g h j p q r m a b e 2 (L 2)) := by
  obtain ⟨hw,hop,ht⟩ := capture_opening c g h j p q r hq hr hg hh hj m a b e 2 (L 2) Q hlo hhi
  have hmem : |leftReading c g h j p q r 2| ∈ disparitySet (speeds c g h j p q r) 0 := by
    exact mem_disparitySet.mpr ⟨3,by decide,rfl⟩
  exact Fresh.FourBlockPacketFrameMoves.move_at_supplied_opening
    (Fresh.FourBlockPacketFrameMoves.native_readings_positive c g h j p q r hq hr hg hh hj) hmem hw hop
    (forced_fast_clear c g h j p q r hp hq hr hs hg hh hj m a b e unitLap window before after Q L
      hlo hhi hmiddle hc hlabels hclose)

#print axioms forced_fast_move
#print axioms first_phase_advance
#print axioms packet_transport
#print axioms earlier_cut_order
#print axioms fast_other_cuts
#print axioms forced_fast_clear
end Fresh.FourBlockOutsideTransport
