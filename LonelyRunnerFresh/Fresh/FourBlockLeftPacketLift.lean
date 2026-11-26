import Fresh.FourBlockAPAnchorArrangement

/-! Retain one original AP window after an explicit whole unit lap.
At a later left opening, the first and last packet faces force the two
interior original readings; no bound on the number of cascade moves is used. -/
namespace Fresh.FourBlockLeftPacketLift
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockLongTailBounds Fresh.FourBlockLeftOpening Fresh.FourBlockAPAnchor

noncomputable def firstPhase (c g h j : ℝ) (p q r : ℕ) (m a b e : ℤ) (P : ℝ) : ℝ :=
  (speeds c g h j p q r 4-speeds c g h j p q r 0)*P-
    ((wholeLap m a b e p q r 4-wholeLap m a b e p q r 0 : ℤ) : ℝ)

theorem packet_phase (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (m a b e : ℤ) (P : ℝ) (i : Fin 4) :
    (speeds c g h j p q r (packetIndex i)-speeds c g h j p q r 0)*P-
      ((wholeLap m a b e p q r (packetIndex i)-wholeLap m a b e p q r 0 : ℤ) : ℝ)=
      firstPhase c g h j p q r m a b e P+(i : ℝ)*(P-(m : ℝ)) := by
  dsimp [firstPhase]
  rw [tail_reading c g h j p q r hp hq hr hs _ (by dsimp [packetIndex]; omega),
    tail_reading c g h j p q r hp hq hr hs 4 (by norm_num),
    tail_lap p q r hp hq hr hs m a b e _ (by dsimp [packetIndex]; omega),
    tail_lap p q r hp hq hr hs m a b e 4 (by norm_num)]
  dsimp [packetIndex]
  push_cast
  norm_num
  ring

def PacketFaces (c g h j : ℝ) (p q r : ℕ) (m a b e unitLap window : ℤ) (P : ℝ) : Prop :=
  0 ≤ P-(m : ℝ)-(unitLap : ℝ) ∧
  (window : ℝ)+1/8 ≤ firstPhase c g h j p q r m a b e P ∧
  firstPhase c g h j p q r m a b e P+3*(P-(m : ℝ)-(unitLap : ℝ)) ≤ (window : ℝ)+7/8

theorem retained_packet (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (m a b e unitLap window : ℤ) (P : ℝ)
    (hf : PacketFaces c g h j p q r m a b e unitLap window P) (i : Fin 4) :
    (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r (packetIndex i)-speeds c g h j p q r 0)*P) := by
  obtain ⟨ht,hlo,hhi⟩ := hf
  have hp' := packet_phase c g h j p q r hp hq hr hs m a b e P i
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hi3 : (i : ℝ) ≤ 3 := by exact_mod_cast (show i.val ≤ 3 by omega)
  have hmul0 := mul_nonneg hi0 ht
  have hmul3 := mul_le_mul_of_nonneg_right hi3 ht
  apply clear_of_window (wholeLap m a b e p q r (packetIndex i)-wholeLap m a b e p q r 0+window+(i.val : ℤ)*unitLap)
  all_goals push_cast at hp' ⊢; nlinarith only [hp',hmul0,hmul3,hlo,hhi]

theorem residual_bounds (c g h j : ℝ) (p q r : ℕ) (m a b e unitLap window : ℤ) (P : ℝ)
    (hf : PacketFaces c g h j p q r m a b e unitLap window P) :
    0 ≤ P-(m : ℝ)-(unitLap : ℝ) ∧ P-(m : ℝ)-(unitLap : ℝ) ≤ 1/4 := by
  obtain ⟨ht,hl,hh⟩ := hf
  exact ⟨ht,by linarith⟩

theorem left_clear (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e unitLap window : ℤ) (u : Fin 3) (L : Fin 3 → ℤ)
    (hf : PacketFaces c g h j p q r m a b e unitLap window (leftOpening c g h j p q r m a b e u (L u)))
    (hl : OtherLeftBandsAt c g h j p q r m a b e (leftOpening c g h j p q r m a b e u (L u)) L u) :
    LonelyAt (disparitySet (speeds c g h j p q r) 0) (leftOpening c g h j p q r m a b e u (L u)) := by
  have hb := bands_at_opening c g h j p q r hq hr hg hh hj m a b e u L hl
  have hprefix (v : Fin 3) : (1/8 : ℝ) ≤ distInt (leftReading c g h j p q r v*leftOpening c g h j p q r m a b e u (L u)) :=
    clear_of_window _ (hb v).1 (hb v).2
  have htail := retained_packet c g h j p q r hp hq hr hs m a b e unitLap window
    (leftOpening c g h j p q r m a b e u (L u)) hf
  intro d hd
  obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
  rw [Fresh.Localisation.distInt_abs_mul]
  fin_cases i
  · exact (hi0 rfl).elim
  · simpa only [leftReading,Fresh.FourBlockOuterTailClear.prefixIndex] using hprefix 0
  · simpa only [leftReading,Fresh.FourBlockOuterTailClear.prefixIndex] using hprefix 1
  · simpa only [leftReading,Fresh.FourBlockOuterTailClear.prefixIndex] using hprefix 2
  · exact htail 0
  · exact htail 1
  · exact htail 2
  · exact htail 3

#print axioms packet_phase
#print axioms retained_packet
#print axioms residual_bounds
#print axioms left_clear
end Fresh.FourBlockLeftPacketLift
