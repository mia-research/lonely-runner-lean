import Fresh.FourBlockLongTailBounds

/-! Original retained phase identities across the unit AP packet. -/
namespace Fresh.FourBlockLongTailPhase
open Fresh Fresh.FourBlockNeighbour Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailBounds

theorem native_phase_gaps (c g h j : ℝ) (p q r : ℕ)
    (hq : 1 ≤ q) (hr : 1 ≤ r) (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j) :
    ∀i : Fin 7,(1/8 : ℝ) ≤ phase c g h j p q r m a b e i.succ-
      phase c g h j p q r m a b e i.castSucc := by
  have hu : (1/8 : ℝ) ≤ g*((m : ℝ)+1/8)-(a : ℝ) := by nlinarith
  have hv : (1/8 : ℝ) ≤ h*((m : ℝ)+1/8)-(b : ℝ) := by nlinarith
  have hw : (1/8 : ℝ) ≤ j*((m : ℝ)+1/8)-(e : ℝ) := by nlinarith
  intro i
  rw [adjacent_phase_gap c g h j p q r hq hr m a b e i]
  split_ifs <;> linarith

theorem native_remainder_band (g h j : ℝ) (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4) :
    (7/8 : ℝ) ≤ remainder g h j m a b e ∧ remainder g h j m a b e ≤ 1 := by
  dsimp [remainder]
  constructor <;> nlinarith

theorem packet_phase (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e s : ℤ) (hsl : (s : ℝ) ≤ 3)
    (i : Fin 8) (hi : 4 ≤ (i : ℕ)) :
    (speeds c g h j p q r i-speeds c g h j p q r 0)*packetOpening g h j m a b e s-
      ((wholeLap m a b e p q r i-wholeLap m a b e p q r 0 : ℤ) : ℝ)=
      9/8+((i : ℝ)-7+(s : ℝ))*(packetOpening g h j m a b e s-(m : ℝ)) := by
  rw [tail_reading c g h j p q r hp hq hr hs i hi,tail_lap p q r hp hq hr hs m a b e i hi]
  have hid := packet_identity g h j hg hh hj m a b e s hsl
  dsimp [spanLap] at hid
  push_cast at hid ⊢
  nlinarith only [hid]

#print axioms native_phase_gaps
#print axioms native_remainder_band
#print axioms packet_phase
end Fresh.FourBlockLongTailPhase
