import Fresh.UnitAPPacketThreeCells
import Fresh.FourBlockShortOpening

/-! Three original AP anchors, arbitrary retained integer return laps and
whole unit-step laps. Known packet clearance is normalized into the same
six native charts used by outside openings. -/
namespace Fresh.FourBlockShortAnchor
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour Fresh.FourBlockShortTail

noncomputable def anchorOpening (g h j : ℝ) (m a b e rho : ℤ) (aidx : Fin 3) : ℝ :=
  (((((aidx.val : ℤ)+2)*m+a+b+e+rho : ℤ) : ℝ)+1/8)/((aidx : ℝ)+2+g+h+j)

theorem opening_identity (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e rho : ℤ) (aidx : Fin 3) :
    ((aidx : ℝ)+2+g+h+j)*anchorOpening g h j m a b e rho aidx=
      (((((aidx.val : ℤ)+2)*m+a+b+e+rho : ℤ) : ℝ)+1/8) := by
  have ha : (0 : ℝ) ≤ aidx := Nat.cast_nonneg _
  have hd : 0 < (aidx : ℝ)+2+g+h+j := by linarith
  dsimp [anchorOpening]
  field_simp [ne_of_gt hd]

theorem anchor_phase (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 5)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho : ℤ) (aidx i : Fin 3) :
    (speeds c g h j p q r (tailIndex i)-speeds c g h j p q r 0)*anchorOpening g h j m a b e rho aidx-
      ((wholeLap m a b e p q r (tailIndex i)-wholeLap m a b e p q r 0 : ℤ) : ℝ)=
      (rho : ℝ)+1/8+((i : ℝ)-(aidx : ℝ))*(anchorOpening g h j m a b e rho aidx-(m : ℝ)) := by
  rw [tail_reading c g h j p q r hp hq hr hs _ (by dsimp [tailIndex]; omega),
    tail_lap p q r hp hq hr hs m a b e _ (by dsimp [tailIndex]; omega)]
  have hid := opening_identity g h j hg hh hj m a b e rho aidx
  dsimp [tailIndex]
  push_cast at hid ⊢
  nlinarith only [hid]

theorem packet_cell_iff (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 5)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho unitLap : ℤ) (aidx : Fin 3)
    (h0 : 0 ≤ anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ))
    (h1 : anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ) ≤ 1) :
    Fresh.UnitAPPacketThreeCells.Cell aidx (anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ)) ↔
      ∀ i : Fin 3, (1/8 : ℝ) ≤ distInt
        ((speeds c g h j p q r (tailIndex i)-speeds c g h j p q r 0)*anchorOpening g h j m a b e rho aidx) := by
  rw [Fresh.UnitAPPacketThreeCells.lifted_iff aidx rho unitLap _ h0 h1]
  have he (i : Fin 3) : distInt
      ((speeds c g h j p q r (tailIndex i)-speeds c g h j p q r 0)*anchorOpening g h j m a b e rho aidx)=
      distInt ((rho : ℝ)+1/8+((i : ℝ)-(aidx : ℝ))*(anchorOpening g h j m a b e rho aidx-(m : ℝ))) := by
    have hid := anchor_phase c g h j p q r hp hq hr hs hg hh hj m a b e rho aidx i
    have hx : (speeds c g h j p q r (tailIndex i)-speeds c g h j p q r 0)*anchorOpening g h j m a b e rho aidx=
      ((rho : ℝ)+1/8+((i : ℝ)-(aidx : ℝ))*(anchorOpening g h j m a b e rho aidx-(m : ℝ)))+
        ((wholeLap m a b e p q r (tailIndex i)-wholeLap m a b e p q r 0 : ℤ) : ℝ) := by linarith
    rw [hx,distInt_add_int]
  simp_rw [he]

theorem packet_bands_of_clear (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 5)
    (m a b e unitLap : ℤ) (P : ℝ)
    (h0 : 0 ≤ P-(m : ℝ)-(unitLap : ℝ)) (h1 : P-(m : ℝ)-(unitLap : ℝ) ≤ 1)
    (hc : ∀ i : Fin 3, (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r (tailIndex i)-speeds c g h j p q r 0)*P)) :
    ∃ (window : ℤ) (role : Fin 6), PacketBands c g h j p q r m a b e unitLap window role P := by
  let w : ℤ := ⌊firstPhase c g h j p q r m a b e P⌋
  have hf : (1/8 : ℝ) ≤ distInt (firstPhase c g h j p q r m a b e P) := by
    have hh := hc 0
    have he : firstPhase c g h j p q r m a b e P=
      (speeds c g h j p q r 5-speeds c g h j p q r 0)*P+
      ((-(wholeLap m a b e p q r 5-wholeLap m a b e p q r 0) : ℤ) : ℝ) := by
      dsimp [firstPhase]; push_cast; ring
    rw [he,distInt_add_int]
    exact hh
  have hx := (clear_iff_fract _).mp hf
  change (1/8 : ℝ) ≤ firstPhase c g h j p q r m a b e P-(w : ℝ) ∧
    firstPhase c g h j p q r m a b e P-(w : ℝ) ≤ 7/8 at hx
  obtain ⟨role,hrole⟩ := Fresh.UnitAPPacketThreeCharts.clear_chart
    (firstPhase c g h j p q r m a b e P-(w : ℝ)) (P-(m : ℝ)-(unitLap : ℝ)) hx.1 hx.2 h0 h1 (by
      intro i
      have hi := hc i
      have hid := Fresh.FourBlockShortTail.packet_phase c g h j p q r hp hq hr hs m a b e P i
      have he : (speeds c g h j p q r (tailIndex i)-speeds c g h j p q r 0)*P=
        (firstPhase c g h j p q r m a b e P-(w : ℝ)+(i : ℝ)*(P-(m : ℝ)-(unitLap : ℝ)))+
        ((wholeLap m a b e p q r (tailIndex i)-wholeLap m a b e p q r 0+w+(i.val : ℤ)*unitLap : ℤ) : ℝ) := by
        push_cast at hid ⊢; nlinarith only [hid]
      rwa [he,distInt_add_int] at hi)
  exact ⟨w,role,hrole⟩

theorem anchor_packet_bands (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 5)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho unitLap : ℤ) (aidx : Fin 3)
    (h0 : 0 ≤ anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ))
    (h1 : anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ) ≤ 1)
    (hc : Fresh.UnitAPPacketThreeCells.Cell aidx (anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ))) :
    ∃ (window : ℤ) (role : Fin 6), PacketBands c g h j p q r m a b e unitLap window role (anchorOpening g h j m a b e rho aidx) := by
  exact packet_bands_of_clear c g h j p q r hp hq hr hs m a b e unitLap _ h0 h1
    ((packet_cell_iff c g h j p q r hp hq hr hs hg hh hj m a b e rho unitLap aidx h0 h1).1 hc)

#print axioms opening_identity
#print axioms anchor_phase
#print axioms packet_cell_iff
#print axioms packet_bands_of_clear
#print axioms anchor_packet_bands
end Fresh.FourBlockShortAnchor
