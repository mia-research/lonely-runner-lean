import Fresh.NativeOpeningRecovery
import Fresh.FourBlockOutsideRebase

/-! Native returns into changed packet windows. Two extremal original
opening comparisons derive the packet; remaining cuts are retained or
passed explicitly, rather than assumed clear at the output. -/
namespace Fresh.FourBlockOpeningRecovery
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour Fresh.FourBlockAPAnchor
  Fresh.FourBlockLeftOpening Fresh.FourBlockLeftPacketLift Fresh.FourBlockLeftPacketCharts
  Fresh.UnitAPPacketChartMotion Fresh.NativeOpeningRecovery

def packetLap (m a b e unitLap window : ℤ) (p q r : ℕ) (role : Fin 14) (i : Fin 4) : ℤ :=
  wholeLap m a b e p q r (packetIndex i)-wholeLap m a b e p q r 0+
    window+(i.val : ℤ)*unitLap+Fresh.UnitAPPacketFourCharts.carry role i

def PacketRecovery (c g h j : ℝ) (p q r : ℕ) (m a b e unitLap window : ℤ)
    (u : Fin 3) (L : Fin 3 → ℤ) (role : Fin 14) : Prop :=
  Sector role (leftOpening c g h j p q r m a b e u (L u)-(m : ℝ)-(unitLap : ℝ)) ∧
  leftReading c g h j p q r u*((packetLap m a b e unitLap window p q r role (minimum role) : ℝ)+1/8) ≤
    (speeds c g h j p q r (packetIndex (minimum role))-speeds c g h j p q r 0)*
      (((leftLap m a b e p q r u+L u : ℤ) : ℝ)+1/8) ∧
  (speeds c g h j p q r (packetIndex (maximum role))-speeds c g h j p q r 0)*
      (((leftLap m a b e p q r u+L u : ℤ) : ℝ)+1/8) ≤
    leftReading c g h j p q r u*((packetLap m a b e unitLap window p q r role (maximum role) : ℝ)+7/8)

def OutsideRecovery (c g h j : ℝ) (p q r : ℕ) (m a b e : ℤ) (Q : ℝ) (u : Fin 3) (L : Fin 3 → ℤ) : Prop :=
  ∀ v : Fin 3, v≠u →
    LowerRecovery (leftReading c g h j p q r u) (leftReading c g h j p q r v) Q
      (leftLap m a b e p q r u+L u) (leftLap m a b e p q r v+L v) ∧
    leftReading c g h j p q r v*(((leftLap m a b e p q r u+L u : ℤ) : ℝ)+1/8-leftReading c g h j p q r u*Q) ≤
      leftReading c g h j p q r u*(((leftLap m a b e p q r v+L v : ℤ) : ℝ)+7/8-leftReading c g h j p q r v*Q)

theorem recovered_packet (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e unitLap window : ℤ)
    (u : Fin 3) (L : Fin 3 → ℤ) (role : Fin 14)
    (hb : PacketRecovery c g h j p q r m a b e unitLap window u L role) :
    ChartBands c g h j p q r m a b e unitLap window role (leftOpening c g h j p q r m a b e u (L u)) := by
  have ho := Fresh.FourBlockLeftOpening.opening_identity c g h j p q r hq hr hg hh hj m a b e u (L u)
  have hd := reading_pos c g h j p q r hq hr hg hh hj u
  apply from_extrema role _ _ hb.1
  · have hlow := opening_order_lower _ _ _ _ _ hd ho hb.2.1
    have hid := packet_phase c g h j p q r hp hq hr hs m a b e (leftOpening c g h j p q r m a b e u (L u)) (minimum role)
    dsimp [packetLap] at hlow
    push_cast at hlow hid
    nlinarith only [hlow,hid]
  · have hhigh := opening_order_upper _ _ _ _ _ hd ho hb.2.2
    have hid := packet_phase c g h j p q r hp hq hr hs m a b e (leftOpening c g h j p q r m a b e u (L u)) (maximum role)
    dsimp [packetLap] at hhigh
    push_cast at hhigh hid
    nlinarith only [hhigh,hid]

theorem recovered_cuts (c g h j : ℝ) (p q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e : ℤ) (Q : ℝ) (u : Fin 3) (L : Fin 3 → ℤ)
    (hlo : (L u : ℝ)-1/8 < leftReading c g h j p q r u*Q-(leftLap m a b e p q r u : ℝ))
    (hhi : leftReading c g h j p q r u*Q-(leftLap m a b e p q r u : ℝ) < (L u : ℝ)+1/8)
    (hb : OutsideRecovery c g h j p q r m a b e Q u L) :
    OtherLeftBandsAt c g h j p q r m a b e (leftOpening c g h j p q r m a b e u (L u)) L u := by
  have ht := (capture_opening c g h j p q r hq hr hg hh hj m a b e u (L u) Q hlo hhi).2.2
  have ho := Fresh.FourBlockLeftOpening.opening_identity c g h j p q r hq hr hg hh hj m a b e u (L u)
  intro v hv
  exact recovered_window _ _ Q _ _ _ (reading_pos c g h j p q r hq hr hg hh hj u)
    (reading_pos c g h j p q r hq hr hg hh hj v).le ht.le ho (hb v hv).1 (hb v hv).2

theorem recovered_clear (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e unitLap window : ℤ)
    (Q : ℝ) (u : Fin 3) (L : Fin 3 → ℤ) (role : Fin 14)
    (hlo : (L u : ℝ)-1/8 < leftReading c g h j p q r u*Q-(leftLap m a b e p q r u : ℝ))
    (hhi : leftReading c g h j p q r u*Q-(leftLap m a b e p q r u : ℝ) < (L u : ℝ)+1/8)
    (hpkt : PacketRecovery c g h j p q r m a b e unitLap window u L role)
    (hcuts : OutsideRecovery c g h j p q r m a b e Q u L) :
    LonelyAt (disparitySet (speeds c g h j p q r) 0) (leftOpening c g h j p q r m a b e u (L u)) := by
  exact left_clear c g h j p q r hp hq hr hs hg hh hj m a b e unitLap window u L role
    (recovered_packet c g h j p q r hp hq hr hs hg hh hj m a b e unitLap window u L role hpkt)
    (recovered_cuts c g h j p q r hq hr hg hh hj m a b e Q u L hlo hhi hcuts)

theorem recovered_move (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e unitLap window : ℤ)
    (Q : ℝ) (u : Fin 3) (L : Fin 3 → ℤ) (role : Fin 14)
    (hlo : (L u : ℝ)-1/8 < leftReading c g h j p q r u*Q-(leftLap m a b e p q r u : ℝ))
    (hhi : leftReading c g h j p q r u*Q-(leftLap m a b e p q r u : ℝ) < (L u : ℝ)+1/8)
    (hpkt : PacketRecovery c g h j p q r m a b e unitLap window u L role)
    (hcuts : OutsideRecovery c g h j p q r m a b e Q u L) :
    IsMove (disparitySet (speeds c g h j p q r) 0) Q (leftOpening c g h j p q r m a b e u (L u)) := by
  obtain ⟨hw,hop,ht⟩ := capture_opening c g h j p q r hq hr hg hh hj m a b e u (L u) Q hlo hhi
  have hmem : |leftReading c g h j p q r u| ∈ disparitySet (speeds c g h j p q r) 0 := by
    refine mem_disparitySet.mpr ⟨Fresh.FourBlockOuterTailClear.prefixIndex u,?_,rfl⟩
    intro he
    have hh := congrArg Fin.val he
    dsimp [Fresh.FourBlockOuterTailClear.prefixIndex] at hh
    omega
  exact Fresh.FourBlockPacketFrameMoves.move_at_supplied_opening
    (Fresh.FourBlockPacketFrameMoves.native_readings_positive c g h j p q r hq hr hg hh hj) hmem hw hop
    (recovered_clear c g h j p q r hp hq hr hs hg hh hj m a b e unitLap window Q u L role hlo hhi hpkt hcuts)

#print axioms recovered_move
#print axioms recovered_packet
#print axioms recovered_cuts
#print axioms recovered_clear
end Fresh.FourBlockOpeningRecovery
