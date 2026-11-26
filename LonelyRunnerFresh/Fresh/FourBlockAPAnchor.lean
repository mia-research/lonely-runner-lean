import Fresh.UnitAPPacketFourSymmetry
import Fresh.FourBlockPacketFrameArrangement

/-! Any of the four original tail readings may open, on any explicitly
retained anchor return and unit-step lap. Closed AP cells replace four
individual tail inequalities; the original three left cuts remain explicit. -/
namespace Fresh.FourBlockAPAnchor
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockLongTailBounds Fresh.FourBlockLeftOpening Fresh.FourBlockOuterTailClear

def packetIndex (a : Fin 4) : Fin 8 := ⟨a.val+4,by omega⟩

noncomputable def anchorOpening (g h j : ℝ) (m a b e rho : ℤ) (aidx : Fin 4) : ℝ :=
  (((((aidx.val : ℤ)+1)*m+a+b+e+rho : ℤ) : ℝ)+1/8)/((aidx : ℝ)+1+g+h+j)

theorem opening_identity (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e rho : ℤ) (aidx : Fin 4) :
    ((aidx : ℝ)+1+g+h+j)*anchorOpening g h j m a b e rho aidx=
      (((((aidx.val : ℤ)+1)*m+a+b+e+rho : ℤ) : ℝ)+1/8) := by
  have ha : (0 : ℝ) ≤ aidx := Nat.cast_nonneg _
  have hd : 0 < (aidx : ℝ)+1+g+h+j := by linarith
  dsimp [anchorOpening]
  field_simp [ne_of_gt hd]

theorem anchor_phase (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho : ℤ) (aidx i : Fin 4) :
    (speeds c g h j p q r (packetIndex i)-speeds c g h j p q r 0)*anchorOpening g h j m a b e rho aidx-
      ((wholeLap m a b e p q r (packetIndex i)-wholeLap m a b e p q r 0 : ℤ) : ℝ)=
      (rho : ℝ)+1/8+((i : ℝ)-(aidx : ℝ))*(anchorOpening g h j m a b e rho aidx-(m : ℝ)) := by
  rw [tail_reading c g h j p q r hp hq hr hs _ (by dsimp [packetIndex]; omega),
    tail_lap p q r hp hq hr hs m a b e _ (by dsimp [packetIndex]; omega)]
  have hid := opening_identity g h j hg hh hj m a b e rho aidx
  dsimp [packetIndex]
  push_cast at hid ⊢
  nlinarith only [hid]

theorem packet_cell_iff (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho unitLap : ℤ) (aidx : Fin 4)
    (h0 : 0 ≤ anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ))
    (h1 : anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ) ≤ 1) :
    Fresh.UnitAPPacketFourLift.Cell aidx (anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ)) ↔
      ∀ i : Fin 4, (1/8 : ℝ) ≤ distInt
        ((speeds c g h j p q r (packetIndex i)-speeds c g h j p q r 0)*anchorOpening g h j m a b e rho aidx) := by
  rw [Fresh.UnitAPPacketFourLift.lifted_iff aidx rho unitLap _ h0 h1]
  have he (i : Fin 4) : distInt
      ((speeds c g h j p q r (packetIndex i)-speeds c g h j p q r 0)*anchorOpening g h j m a b e rho aidx)=
      distInt ((rho : ℝ)+1/8+((i : ℝ)-(aidx : ℝ))*(anchorOpening g h j m a b e rho aidx-(m : ℝ))) := by
    have hid := anchor_phase c g h j p q r hp hq hr hs hg hh hj m a b e rho aidx i
    have hx : (speeds c g h j p q r (packetIndex i)-speeds c g h j p q r 0)*anchorOpening g h j m a b e rho aidx=
      ((rho : ℝ)+1/8+((i : ℝ)-(aidx : ℝ))*(anchorOpening g h j m a b e rho aidx-(m : ℝ)))+
        ((wholeLap m a b e p q r (packetIndex i)-wholeLap m a b e p q r 0 : ℤ) : ℝ) := by linarith
    rw [hx,distInt_add_int]
  simp_rw [he]

theorem anchor_clear (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho unitLap : ℤ) (aidx : Fin 4) (L : Fin 3 → ℤ)
    (h0 : 0 ≤ anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ))
    (h1 : anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ) ≤ 1)
    (hc : Fresh.UnitAPPacketFourLift.Cell aidx (anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ)))
    (hl : LeftBandsAt c g h j p q r m a b e (anchorOpening g h j m a b e rho aidx) L) :
    LonelyAt (disparitySet (speeds c g h j p q r) 0) (anchorOpening g h j m a b e rho aidx) := by
  have htail := (packet_cell_iff c g h j p q r hp hq hr hs hg hh hj m a b e rho unitLap aidx h0 h1).1 hc
  have hprefix (u : Fin 3) : (1/8 : ℝ) ≤ distInt (leftReading c g h j p q r u*anchorOpening g h j m a b e rho aidx) :=
    clear_of_window _ (hl u).1 (hl u).2
  intro d hd
  obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
  rw [Fresh.Localisation.distInt_abs_mul]
  fin_cases i
  · exact (hi0 rfl).elim
  · simpa only [leftReading,prefixIndex] using hprefix 0
  · simpa only [leftReading,prefixIndex] using hprefix 1
  · simpa only [leftReading,prefixIndex] using hprefix 2
  · exact htail 0
  · exact htail 1
  · exact htail 2
  · exact htail 3

#print axioms opening_identity
#print axioms anchor_phase
#print axioms packet_cell_iff
#print axioms anchor_clear
end Fresh.FourBlockAPAnchor
