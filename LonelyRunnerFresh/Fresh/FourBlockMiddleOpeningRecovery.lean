import Fresh.FourBlockDoubleOpeningRecovery

/-! The same original-entry recovery mechanism for middle AP packets.
Lower packet faces may be retained or passed, with no target cut bands
assumed. The selected original opener supplies its own boundary. -/
namespace Fresh.FourBlockMiddleOpeningRecovery
open Fresh Fresh.FourBlockNeighbour Fresh.FourBlockShortOpening Fresh.FourBlockMiddlePacket
  Fresh.UnitAPPacketThreeMotion Fresh.NativeOpeningRecovery

def packetLap (m a d e unitLap window : ℤ) (p q r : ℕ) (b : Fin 6) (role : Fin 6) (i : Fin 3) : ℤ :=
  wholeLap m a d e p q r (middleIndex b i)-wholeLap m a d e p q r 0+
    window+(i.val : ℤ)*unitLap+Fresh.UnitAPPacketThreeCharts.carry role i

noncomputable def PacketRecovery (c g h j : ℝ) (p q r : ℕ) (b : Fin 6)
    (m a d e rho unitLap window : ℤ) (Q : ℝ) (u : Fin 7) (role : Fin 6) : Prop :=
  Sector role (opening c g h j p q r m a d e rho u-(m : ℝ)-(unitLap : ℝ)) ∧
  LowerRecovery (reading c g h j p q r u)
    (speeds c g h j p q r (middleIndex b (minimum role))-speeds c g h j p q r 0) Q
    (lap m a d e p q r u+rho) (packetLap m a d e unitLap window p q r b role (minimum role)) ∧
  (speeds c g h j p q r (middleIndex b (maximum role))-speeds c g h j p q r 0)*
    (((lap m a d e p q r u+rho : ℤ) : ℝ)+1/8-reading c g h j p q r u*Q) ≤
    reading c g h j p q r u*((packetLap m a d e unitLap window p q r b role (maximum role) : ℝ)+7/8-
      (speeds c g h j p q r (middleIndex b (maximum role))-speeds c g h j p q r 0)*Q)

noncomputable def OutsideRecovery (c g h j : ℝ) (p q r : ℕ) (b : Fin 6)
    (m a d e rho : ℤ) (Q : ℝ) (u : Fin 7) (L : Fin 8 → ℤ) : Prop :=
  ∀ i : Fin 8, i≠0 → i≠openingIndex u → (i.val < b.val ∨ b.val+3 ≤ i.val) →
    LowerRecovery (reading c g h j p q r u) (speeds c g h j p q r i-speeds c g h j p q r 0) Q
      (lap m a d e p q r u+rho) (wholeLap m a d e p q r i-wholeLap m a d e p q r 0+L i) ∧
    (speeds c g h j p q r i-speeds c g h j p q r 0)*
      (((lap m a d e p q r u+rho : ℤ) : ℝ)+1/8-reading c g h j p q r u*Q) ≤
      reading c g h j p q r u*((((wholeLap m a d e p q r i-wholeLap m a d e p q r 0+L i : ℤ) : ℝ))+7/8-
        (speeds c g h j p q r i-speeds c g h j p q r 0)*Q)

theorem recovered_packet (c g h j : ℝ) (p q r : ℕ) (b : Fin 6)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hhost : MiddleHost p q r b)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a d e rho unitLap window : ℤ)
    (Q : ℝ) (u : Fin 7) (role : Fin 6)
    (hlo : (rho : ℝ)-1/8 < reading c g h j p q r u*Q-(lap m a d e p q r u : ℝ))
    (hhi : reading c g h j p q r u*Q-(lap m a d e p q r u : ℝ) < (rho : ℝ)+1/8)
    (hb : PacketRecovery c g h j p q r b m a d e rho unitLap window Q u role) :
    PacketBands c g h j p q r b m a d e unitLap window role (opening c g h j p q r m a d e rho u) := by
  have ht := (Fresh.FourBlockShortOpeningMoves.capture_opening c g h j p q r hq hr hg hh hj m a d e u rho Q hlo hhi).2.2
  have ho := Fresh.FourBlockShortOpening.opening_identity c g h j p q r hq hr hg hh hj m a d e rho u
  have hd := reading_pos c g h j p q r hq hr hg hh hj u
  have hs : 0 ≤ speeds c g h j p q r (middleIndex b (minimum role))-speeds c g h j p q r 0 :=
    sub_nonneg.mpr ((Fresh.FourBlockEndpoints.speeds_monotone c g h j p q r hq hr hg hh hj) (Fin.zero_le _))
  apply from_extrema role _ _ hb.1
  · have hl := Fresh.NativeOpeningFaces.lower_from_entry _ _ Q _ _ _ hd hs ht.le ho hb.2.1
    have hid := packet_phase c g h j p q r b hp hq hr hhost m a d e (opening c g h j p q r m a d e rho u) (minimum role)
    dsimp [packetLap] at hl
    push_cast at hl hid
    nlinarith only [hl,hid]
  · have hu := Fresh.NativeOpeningFaces.upper_from_deficit _ _ Q _ _ _ (7/8) hd ho hb.2.2
    have hid := packet_phase c g h j p q r b hp hq hr hhost m a d e (opening c g h j p q r m a d e rho u) (maximum role)
    dsimp [packetLap] at hu
    push_cast at hu hid
    nlinarith only [hu,hid]

theorem recovered_cuts (c g h j : ℝ) (p q r : ℕ) (b : Fin 6) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a d e rho : ℤ)
    (Q : ℝ) (u : Fin 7) (L : Fin 8 → ℤ)
    (hlo : (rho : ℝ)-1/8 < reading c g h j p q r u*Q-(lap m a d e p q r u : ℝ))
    (hhi : reading c g h j p q r u*Q-(lap m a d e p q r u : ℝ) < (rho : ℝ)+1/8)
    (hb : OutsideRecovery c g h j p q r b m a d e rho Q u L) :
    RemainingBands c g h j p q r b m a d e (opening c g h j p q r m a d e rho u) L u := by
  have ht := (Fresh.FourBlockShortOpeningMoves.capture_opening c g h j p q r hq hr hg hh hj m a d e u rho Q hlo hhi).2.2
  have ho := Fresh.FourBlockShortOpening.opening_identity c g h j p q r hq hr hg hh hj m a d e rho u
  have hd := reading_pos c g h j p q r hq hr hg hh hj u
  intro i hi hiu hout
  have hs : 0 ≤ speeds c g h j p q r i-speeds c g h j p q r 0 :=
    sub_nonneg.mpr ((Fresh.FourBlockEndpoints.speeds_monotone c g h j p q r hq hr hg hh hj) (Fin.zero_le i))
  exact recovered_window _ _ Q _ _ _ hd hs ht.le ho (hb i hi hiu hout).1 (hb i hi hiu hout).2

theorem recovered_move (c g h j : ℝ) (p q r : ℕ) (b : Fin 6)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hhost : MiddleHost p q r b)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a d e rho unitLap window : ℤ)
    (Q : ℝ) (u : Fin 7) (role : Fin 6) (L : Fin 8 → ℤ)
    (hlo : (rho : ℝ)-1/8 < reading c g h j p q r u*Q-(lap m a d e p q r u : ℝ))
    (hhi : reading c g h j p q r u*Q-(lap m a d e p q r u : ℝ) < (rho : ℝ)+1/8)
    (hpkt : PacketRecovery c g h j p q r b m a d e rho unitLap window Q u role)
    (hcuts : OutsideRecovery c g h j p q r b m a d e rho Q u L) :
    Fresh.IsMove (disparitySet (speeds c g h j p q r) 0) Q (opening c g h j p q r m a d e rho u) := by
  exact Fresh.FourBlockMiddlePacket.opening_move c g h j p q r b hp hq hr hhost hg hh hj m a d e rho unitLap window u role L
    (recovered_packet c g h j p q r b hp hq hr hhost hg hh hj m a d e rho unitLap window Q u role hlo hhi hpkt)
    (recovered_cuts c g h j p q r b hq hr hg hh hj m a d e rho Q u L hlo hhi hcuts) Q hlo hhi

#print axioms recovered_packet
#print axioms recovered_cuts
#print axioms recovered_move
end Fresh.FourBlockMiddleOpeningRecovery
