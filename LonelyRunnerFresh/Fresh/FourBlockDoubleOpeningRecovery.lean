import Fresh.FourBlockDoubleSingletonArrangement
import Fresh.UnitAPPacketThreeMotion
import Fresh.NativeOpeningFaces

/-! Two-endpoint packet recovery from original entry comparisons. The
selected opening derives its own boundary and positive displacement; the
packet and remaining cuts are conclusions rather than target assumptions. -/
namespace Fresh.FourBlockDoubleOpeningRecovery
open Fresh Fresh.FourBlockNeighbour Fresh.FourBlockDoubleSingleton
  Fresh.UnitAPPacketThreeMotion Fresh.NativeOpeningRecovery

def packetLap (m a d e unitLap window : ℤ) (q r : ℕ) (b : Fin 6)
    (right : Bool) (role : Fin 6) (i : Fin 3) : ℤ :=
  lap m a d e q r right (packetIndex right b i)+window+(i.val : ℤ)*unitLap+
    Fresh.UnitAPPacketThreeCharts.carry role i

noncomputable def PacketRecovery (c g h j : ℝ) (q r : ℕ) (b : Fin 6) (right : Bool)
    (m a d e rho unitLap window : ℤ) (Q : ℝ) (u : Fin 7) (role : Fin 6) : Prop :=
  Sector role (opening c g h j q r right m a d e rho u-(m : ℝ)-(unitLap : ℝ)) ∧
  LowerRecovery (reading c g h j q r right (openingIndex right u))
    (reading c g h j q r right (packetIndex right b (minimum role))) Q
    (lap m a d e q r right (openingIndex right u)+rho) (packetLap m a d e unitLap window q r b right role (minimum role)) ∧
  reading c g h j q r right (packetIndex right b (maximum role))*
    (((lap m a d e q r right (openingIndex right u)+rho : ℤ) : ℝ)+1/8-reading c g h j q r right (openingIndex right u)*Q) ≤
    reading c g h j q r right (openingIndex right u)*
      ((packetLap m a d e unitLap window q r b right role (maximum role) : ℝ)+7/8-
        reading c g h j q r right (packetIndex right b (maximum role))*Q)

noncomputable def OutsideRecovery (c g h j : ℝ) (q r : ℕ) (b : Fin 6) (right : Bool)
    (m a d e rho : ℤ) (Q : ℝ) (u : Fin 7) (L : Fin 8 → ℤ) : Prop :=
  ∀ i : Fin 8, i≠endpoint right → i≠openingIndex right u → (i.val < b.val ∨ b.val+3 ≤ i.val) →
    LowerRecovery (reading c g h j q r right (openingIndex right u)) (reading c g h j q r right i) Q
      (lap m a d e q r right (openingIndex right u)+rho) (lap m a d e q r right i+L i) ∧
    reading c g h j q r right i*
      (((lap m a d e q r right (openingIndex right u)+rho : ℤ) : ℝ)+1/8-reading c g h j q r right (openingIndex right u)*Q) ≤
      reading c g h j q r right (openingIndex right u)*
        (((lap m a d e q r right i+L i : ℤ) : ℝ)+7/8-reading c g h j q r right i*Q)

theorem opening_identity (c g h j : ℝ) (q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (right : Bool) (m a d e rho : ℤ) (u : Fin 7) :
    reading c g h j q r right (openingIndex right u)*opening c g h j q r right m a d e rho u=
      ((lap m a d e q r right (openingIndex right u)+rho : ℤ) : ℝ)+1/8 := by
  have hp := opening_reading_pos c g h j q r hq hr hg hh hj right u
  dsimp [opening]
  field_simp

theorem capture_advance (c g h j : ℝ) (q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (right : Bool) (m a d e rho : ℤ) (Q : ℝ) (u : Fin 7)
    (hlo : (rho : ℝ)-1/8 < phase c g h j q r right m a d e (openingIndex right u) Q)
    (hhi : phase c g h j q r right m a d e (openingIndex right u) Q < (rho : ℝ)+1/8) :
    Q < opening c g h j q r right m a d e rho u := by
  have ht := Fresh.NativeOpeningRetention.capture_advance _ Q _ _
    (opening_reading_pos c g h j q r hq hr hg hh hj right u)
    (opening_identity c g h j q r hq hr hg hh hj right m a d e rho u)
    (by dsimp [Fresh.FourBlockDoubleSingleton.phase] at hlo; push_cast; linarith only [hlo])
    (by dsimp [Fresh.FourBlockDoubleSingleton.phase] at hhi; push_cast; linarith only [hhi])
  linarith only [ht.1]

theorem recovered_packet (c g h j : ℝ) (q r : ℕ) (b : Fin 6) (hq : 1 ≤ q) (hr : 1 ≤ r) (hhost : Host q r b)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (right : Bool) (m a d e rho unitLap window : ℤ)
    (Q : ℝ) (u : Fin 7) (role : Fin 6)
    (hlo : (rho : ℝ)-1/8 < phase c g h j q r right m a d e (openingIndex right u) Q)
    (hhi : phase c g h j q r right m a d e (openingIndex right u) Q < (rho : ℝ)+1/8)
    (hb : PacketRecovery c g h j q r b right m a d e rho unitLap window Q u role) :
    PacketBands c g h j q r b right m a d e unitLap window role (opening c g h j q r right m a d e rho u) := by
  have ht := capture_advance c g h j q r hq hr hg hh hj right m a d e rho Q u hlo hhi
  have ho := opening_identity c g h j q r hq hr hg hh hj right m a d e rho u
  have hd := opening_reading_pos c g h j q r hq hr hg hh hj right u
  have hs : 0 ≤ reading c g h j q r right (packetIndex right b (minimum role)) := by
    rw [←reading_abs c g h j q r hq hr hg hh hj]
    exact abs_nonneg _
  apply from_extrema role _ _ hb.1
  · have hl := Fresh.NativeOpeningFaces.lower_from_entry _ _ Q _ _ _ hd hs ht.le ho hb.2.1
    have hid := packet_phase c g h j q r b hq hr hhost m a d e right (opening c g h j q r right m a d e rho u) (minimum role)
    dsimp [packetLap] at hl
    dsimp [Fresh.FourBlockDoubleSingleton.phase] at hid ⊢
    push_cast at hl
    nlinarith only [hl,hid]
  · have hu := Fresh.NativeOpeningFaces.upper_from_deficit _ _ Q _ _ _ (7/8) hd ho hb.2.2
    have hid := packet_phase c g h j q r b hq hr hhost m a d e right (opening c g h j q r right m a d e rho u) (maximum role)
    dsimp [packetLap] at hu
    dsimp [Fresh.FourBlockDoubleSingleton.phase] at hid ⊢
    push_cast at hu
    nlinarith only [hu,hid]

theorem recovered_cuts (c g h j : ℝ) (q r : ℕ) (b : Fin 6) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (right : Bool) (m a d e rho : ℤ)
    (Q : ℝ) (u : Fin 7) (L : Fin 8 → ℤ)
    (hlo : (rho : ℝ)-1/8 < phase c g h j q r right m a d e (openingIndex right u) Q)
    (hhi : phase c g h j q r right m a d e (openingIndex right u) Q < (rho : ℝ)+1/8)
    (hb : OutsideRecovery c g h j q r b right m a d e rho Q u L) :
    RemainingBands c g h j q r b right m a d e (opening c g h j q r right m a d e rho u) L u := by
  have ht := capture_advance c g h j q r hq hr hg hh hj right m a d e rho Q u hlo hhi
  have ho := opening_identity c g h j q r hq hr hg hh hj right m a d e rho u
  have hd := opening_reading_pos c g h j q r hq hr hg hh hj right u
  intro i hi hiu hout
  have hs : 0 ≤ reading c g h j q r right i := by
    rw [←reading_abs c g h j q r hq hr hg hh hj]
    exact abs_nonneg _
  have hw := recovered_window _ _ Q _ _ _ hd hs ht.le ho (hb i hi hiu hout).1 (hb i hi hiu hout).2
  dsimp [Fresh.FourBlockDoubleSingleton.phase]
  push_cast at hw
  constructor <;> linarith only [hw.1,hw.2]

theorem recovered_move (c g h j : ℝ) (q r : ℕ) (b : Fin 6) (hq : 1 ≤ q) (hr : 1 ≤ r) (hhost : Host q r b)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (right : Bool) (m a d e rho unitLap window : ℤ)
    (Q : ℝ) (u : Fin 7) (role : Fin 6) (L : Fin 8 → ℤ)
    (hlo : (rho : ℝ)-1/8 < phase c g h j q r right m a d e (openingIndex right u) Q)
    (hhi : phase c g h j q r right m a d e (openingIndex right u) Q < (rho : ℝ)+1/8)
    (hpkt : PacketRecovery c g h j q r b right m a d e rho unitLap window Q u role)
    (hcuts : OutsideRecovery c g h j q r b right m a d e rho Q u L) :
    Fresh.IsMove (disparitySet (speeds c g h j 1 q r) (endpoint right)) Q (opening c g h j q r right m a d e rho u) := by
  exact opening_move c g h j q r b hq hr hhost hg hh hj right m a d e rho unitLap window u role L
    (recovered_packet c g h j q r b hq hr hhost hg hh hj right m a d e rho unitLap window Q u role hlo hhi hpkt)
    (recovered_cuts c g h j q r b hq hr hg hh hj right m a d e rho Q u L hlo hhi hcuts) Q hlo hhi

#print axioms opening_identity
#print axioms capture_advance
#print axioms recovered_packet
#print axioms recovered_cuts
#print axioms recovered_move
end Fresh.FourBlockDoubleOpeningRecovery
