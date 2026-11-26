import Fresh.FourBlockLeftPacketLiftArrangement
import Fresh.FourBlockPacketFrameMoves

/-! Actual original moves into the lifted packet families. Strict capture
selects the named retained integer opening; native packet faces derive the
terminal clearance and allow all original competing openings. -/
namespace Fresh.FourBlockPacketLiftMoves
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour Fresh.FourBlockLongTailBounds
  Fresh.FourBlockLeftOpening Fresh.FourBlockAPAnchor Fresh.FourBlockLeftPacketLift
  Fresh.FourBlockPacketFrameMoves

theorem anchor_capture (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho : ℤ) (aidx : Fin 4) (t : ℝ)
    (hlo : (rho : ℝ)-1/8 <
      (speeds c g h j p q r (packetIndex aidx)-speeds c g h j p q r 0)*t-
      ((wholeLap m a b e p q r (packetIndex aidx)-wholeLap m a b e p q r 0 : ℤ) : ℝ))
    (hhi : (speeds c g h j p q r (packetIndex aidx)-speeds c g h j p q r 0)*t-
      ((wholeLap m a b e p q r (packetIndex aidx)-wholeLap m a b e p q r 0 : ℤ) : ℝ) < (rho : ℝ)+1/8) :
    InWay |speeds c g h j p q r (packetIndex aidx)-speeds c g h j p q r 0| t ∧
      nextOpening |speeds c g h j p q r (packetIndex aidx)-speeds c g h j p q r 0| t=
        anchorOpening g h j m a b e rho aidx := by
  let d := speeds c g h j p q r (packetIndex aidx)-speeds c g h j p q r 0
  let N := wholeLap m a b e p q r (packetIndex aidx)-wholeLap m a b e p q r 0
  have hd : d=(aidx : ℝ)+1+g+h+j := by
    dsimp [d]
    rw [tail_reading c g h j p q r hp hq hr hs _ (by dsimp [packetIndex]; omega)]
    dsimp [packetIndex]; push_cast; ring
  have hN : N=((aidx.val : ℤ)+1)*m+a+b+e := by
    dsimp [N]
    rw [tail_lap p q r hp hq hr hs m a b e _ (by dsimp [packetIndex]; omega)]
    dsimp [packetIndex]; push_cast; ring
  have ha : (0 : ℝ) ≤ aidx := Nat.cast_nonneg _
  have hdpos : 0 < d := by rw [hd]; linarith
  have hnear : |d*t-((N+rho : ℤ) : ℝ)| < 1/8 := by
    rw [abs_lt]; push_cast
    constructor <;> linarith
  have hw : InWay |d| t := by
    rw [abs_of_pos hdpos]
    exact lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (N+rho)) hnear
  refine ⟨hw,?_⟩
  change nextOpening |d| t=_
  rw [abs_of_pos hdpos,nextOpening_eq hnear,hd,hN]
  rfl

theorem anchor_move (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho unitLap : ℤ) (aidx : Fin 4) (L : Fin 3 → ℤ)
    (h0 : 0 ≤ anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ))
    (h1 : anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ) ≤ 1)
    (hc : Fresh.UnitAPPacketFourLift.Cell aidx (anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ)))
    (hl : LeftBandsAt c g h j p q r m a b e (anchorOpening g h j m a b e rho aidx) L) (t : ℝ)
    (hcaplo : (rho : ℝ)-1/8 <
      (speeds c g h j p q r (packetIndex aidx)-speeds c g h j p q r 0)*t-
      ((wholeLap m a b e p q r (packetIndex aidx)-wholeLap m a b e p q r 0 : ℤ) : ℝ))
    (hcaphi : (speeds c g h j p q r (packetIndex aidx)-speeds c g h j p q r 0)*t-
      ((wholeLap m a b e p q r (packetIndex aidx)-wholeLap m a b e p q r 0 : ℤ) : ℝ) < (rho : ℝ)+1/8) :
    IsMove (disparitySet (speeds c g h j p q r) 0) t (anchorOpening g h j m a b e rho aidx) := by
  obtain ⟨hw,hop⟩ := anchor_capture c g h j p q r hp hq hr hs hg hh hj m a b e rho aidx t hcaplo hcaphi
  have hmem : |speeds c g h j p q r (packetIndex aidx)-speeds c g h j p q r 0| ∈
      disparitySet (speeds c g h j p q r) 0 := by
    refine mem_disparitySet.mpr ⟨packetIndex aidx,?_,rfl⟩
    intro he
    have hc := congrArg Fin.val he
    dsimp [packetIndex] at hc
    omega
  exact move_at_supplied_opening (native_readings_positive c g h j p q r hq hr hg hh hj) hmem hw hop
    (anchor_clear c g h j p q r hp hq hr hs hg hh hj m a b e rho unitLap aidx L h0 h1 hc hl)

theorem left_move (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e unitLap window : ℤ) (u : Fin 3) (L : Fin 3 → ℤ)
    (hf : PacketFaces c g h j p q r m a b e unitLap window (leftOpening c g h j p q r m a b e u (L u)))
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
    (left_clear c g h j p q r hp hq hr hs hg hh hj m a b e unitLap window u L hf hl)

#print axioms anchor_capture
#print axioms anchor_move
#print axioms left_move
end Fresh.FourBlockPacketLiftMoves
