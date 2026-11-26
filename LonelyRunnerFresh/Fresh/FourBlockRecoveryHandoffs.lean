import Fresh.FourBlockOpeningRecoveryArrangement
import Fresh.FourBlockShortOpeningMoves

/-! Original two-outside handoffs with packet recapture. The first move
is forced by its original sole capture; recovery proves the second move
and terminal clearance even when other packet members are captured. -/
namespace Fresh.FourBlockRecoveryHandoffs
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour Fresh.FourBlockAPAnchor
  Fresh.FourBlockLeftOpening Fresh.FourBlockLeftPacketCharts Fresh.FourBlockOpeningRecovery

theorem first_move (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e unitLap window : ℤ)
    (Q : ℝ) (u : Fin 3) (L : Fin 3 → ℤ) (role : Fin 14)
    (hlo : (L u : ℝ)-1/8 < leftReading c g h j p q r u*Q-(leftLap m a b e p q r u : ℝ))
    (hhi : leftReading c g h j p q r u*Q-(leftLap m a b e p q r u : ℝ) < (L u : ℝ)+1/8)
    (hpacket : ChartBands c g h j p q r m a b e unitLap window role Q)
    (hcuts : OtherLeftBandsAt c g h j p q r m a b e Q L u) :
    IsMove (disparitySet (speeds c g h j p q r) 0) Q (leftOpening c g h j p q r m a b e u (L u)) := by
  obtain ⟨hw,hop,ht⟩ := capture_opening c g h j p q r hq hr hg hh hj m a b e u (L u) Q hlo hhi
  have hmem : |leftReading c g h j p q r u| ∈ disparitySet (speeds c g h j p q r) 0 := by
    refine mem_disparitySet.mpr ⟨Fresh.FourBlockOuterTailClear.prefixIndex u,?_,rfl⟩
    intro he
    have hh := congrArg Fin.val he
    dsimp [Fresh.FourBlockOuterTailClear.prefixIndex] at hh
    omega
  have htail := packet_clear c g h j p q r hp hq hr hs m a b e unitLap window role Q hpacket
  apply Fresh.FourBlockTwoOutside.sole_capture_move hmem hw hop
  intro d hd hinway
  obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
  by_cases hiu : i=Fresh.FourBlockOuterTailClear.prefixIndex u
  · subst i; rfl
  have hnot : ¬ (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r i-speeds c g h j p q r 0)*Q) := by
    rw [←Fresh.Localisation.distInt_abs_mul]
    exact not_le.mpr hinway
  by_cases hi1 : i=1
  · subst i
    have hv : (0 : Fin 3)≠u := by intro he; subst u; exact hiu rfl
    exact (hnot (clear_of_window _ (hcuts 0 hv).1 (hcuts 0 hv).2)).elim
  by_cases hi2 : i=2
  · subst i
    have hv : (1 : Fin 3)≠u := by intro he; subst u; exact hiu rfl
    exact (hnot (clear_of_window _ (hcuts 1 hv).1 (hcuts 1 hv).2)).elim
  by_cases hi3 : i=3
  · subst i
    have hv : (2 : Fin 3)≠u := by intro he; subst u; exact hiu rfl
    exact (hnot (clear_of_window _ (hcuts 2 hv).1 (hcuts 2 hv).2)).elim
  have hv0 := Fin.val_ne_of_ne hi0
  have hv1 := Fin.val_ne_of_ne hi1
  have hv2 := Fin.val_ne_of_ne hi2
  have hv3 := Fin.val_ne_of_ne hi3
  let v : Fin 4 := ⟨i.val-4,by have hi := i.isLt; omega⟩
  have he : packetIndex v=i := by apply Fin.ext; dsimp [packetIndex,v]; omega
  have hc := htail v
  rw [he] at hc
  exact (hnot hc).elim

theorem two_handoffs (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e unitLap window : ℤ)
    (Q : ℝ) (u : Fin 3) (L : Fin 3 → ℤ) (role : Fin 14)
    (hlo : (L u : ℝ)-1/8 < leftReading c g h j p q r u*Q-(leftLap m a b e p q r u : ℝ))
    (hhi : leftReading c g h j p q r u*Q-(leftLap m a b e p q r u : ℝ) < (L u : ℝ)+1/8)
    (hpacket : ChartBands c g h j p q r m a b e unitLap window role Q)
    (hcuts : OtherLeftBandsAt c g h j p q r m a b e Q L u)
    (second : Fin 3) (Lfinal : Fin 3 → ℤ) (finalUnit finalWindow : ℤ) (finalRole : Fin 14)
    (hsecondlo : (Lfinal second : ℝ)-1/8 <
      leftReading c g h j p q r second*leftOpening c g h j p q r m a b e u (L u)-(leftLap m a b e p q r second : ℝ))
    (hsecondhi : leftReading c g h j p q r second*leftOpening c g h j p q r m a b e u (L u)-
      (leftLap m a b e p q r second : ℝ) < (Lfinal second : ℝ)+1/8)
    (hrecover : PacketRecovery c g h j p q r m a b e finalUnit finalWindow second Lfinal finalRole)
    (houtside : OutsideRecovery c g h j p q r m a b e
      (leftOpening c g h j p q r m a b e u (L u)) second Lfinal) :
    IsMove (disparitySet (speeds c g h j p q r) 0) Q (leftOpening c g h j p q r m a b e u (L u)) ∧
    IsMove (disparitySet (speeds c g h j p q r) 0) (leftOpening c g h j p q r m a b e u (L u))
      (leftOpening c g h j p q r m a b e second (Lfinal second)) ∧
    LonelyAt (disparitySet (speeds c g h j p q r) 0) (leftOpening c g h j p q r m a b e second (Lfinal second)) := by
  exact ⟨first_move c g h j p q r hp hq hr hs hg hh hj m a b e unitLap window Q u L role hlo hhi hpacket hcuts,
    recovered_move c g h j p q r hp hq hr hs hg hh hj m a b e finalUnit finalWindow
      (leftOpening c g h j p q r m a b e u (L u)) second Lfinal finalRole hsecondlo hsecondhi hrecover houtside,
    recovered_clear c g h j p q r hp hq hr hs hg hh hj m a b e finalUnit finalWindow
      (leftOpening c g h j p q r m a b e u (L u)) second Lfinal finalRole hsecondlo hsecondhi hrecover houtside⟩

#print axioms first_move
#print axioms two_handoffs
end Fresh.FourBlockRecoveryHandoffs
