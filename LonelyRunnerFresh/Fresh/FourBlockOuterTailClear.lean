import Fresh.FourBlockOuterLapMove

/-! The same native outer packet across all four long-tail partitions.
Only the first three original readings need explicit retained cut bands. -/
namespace Fresh.FourBlockOuterTailClear
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailBounds Fresh.FourBlockOuterLapPhase

def prefixIndex (i : Fin 3) : Fin 8 := ⟨i.val+1,by omega⟩

-- STANDING: DEFINITION
def LeftBands (c g h j : ℝ) (p q r : ℕ) (m a b e rho : ℤ) (L : Fin 3 → ℤ) : Prop :=
  ∀ i : Fin 3,
    (((wholeLap m a b e p q r (prefixIndex i)-wholeLap m a b e p q r 0+L i : ℤ) : ℝ)+1/8 ≤
      (speeds c g h j p q r (prefixIndex i)-speeds c g h j p q r 0)*outerLapOpening g h j m a b e rho) ∧
    ((speeds c g h j p q r (prefixIndex i)-speeds c g h j p q r 0)*outerLapOpening g h j m a b e rho ≤
      ((wholeLap m a b e p q r (prefixIndex i)-wholeLap m a b e p q r 0+L i : ℤ) : ℝ)+7/8)

theorem tail_phase (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho : ℤ)
    (i : Fin 8) (hi : 4 ≤ (i : ℕ)) :
    (speeds c g h j p q r i-speeds c g h j p q r 0)*outerLapOpening g h j m a b e rho-
      ((wholeLap m a b e p q r i-wholeLap m a b e p q r 0 : ℤ) : ℝ)=
      (rho : ℝ)+1/8+((i : ℝ)-7)*(outerLapOpening g h j m a b e rho-(m : ℝ)) := by
  rw [tail_reading c g h j p q r hp hq hr hs i hi,tail_lap p q r hp hq hr hs m a b e i hi]
  have hid := opening_identity g h j hg hh hj m a b e rho
  dsimp [spanLap] at hid
  push_cast at hid ⊢
  nlinarith only [hid]

theorem outer_clear (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho : ℤ) (L : Fin 3 → ℤ)
    (hlo : 11*(g+h+j)+16*remainder g h j m a b e ≤ 16*(rho : ℝ)-42)
    (hhi : 8*(rho : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hleft : LeftBands c g h j p q r m a b e rho L) :
    LonelyAt (disparitySet (speeds c g h j p q r) 0) (outerLapOpening g h j m a b e rho) := by
  obtain ⟨hPlo,hPhi⟩ := opening_bounds g h j hg hh hj m a b e rho hlo hhi
  have hprefix : ∀ u : Fin 3, (1/8 : ℝ) ≤ distInt
      ((speeds c g h j p q r (prefixIndex u)-speeds c g h j p q r 0)*outerLapOpening g h j m a b e rho) := by
    intro u
    exact clear_of_window _ (hleft u).1 (hleft u).2
  have hf4 := tail_phase c g h j p q r hp hq hr hs hg hh hj m a b e rho (4 : Fin 8) (by norm_num)
  norm_num at hf4
  have hc4 : (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r 4-speeds c g h j p q r 0)*outerLapOpening g h j m a b e rho) := by
    apply clear_of_window (wholeLap m a b e p q r 4-wholeLap m a b e p q r 0+rho-3)
    all_goals push_cast at hf4 ⊢; linarith
  have hf5 := tail_phase c g h j p q r hp hq hr hs hg hh hj m a b e rho (5 : Fin 8) (by norm_num)
  norm_num at hf5
  have hc5 : (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r 5-speeds c g h j p q r 0)*outerLapOpening g h j m a b e rho) := by
    apply clear_of_window (wholeLap m a b e p q r 5-wholeLap m a b e p q r 0+rho-2)
    all_goals push_cast at hf5 ⊢; linarith
  have hf6 := tail_phase c g h j p q r hp hq hr hs hg hh hj m a b e rho (6 : Fin 8) (by norm_num)
  norm_num at hf6
  have hc6 : (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r 6-speeds c g h j p q r 0)*outerLapOpening g h j m a b e rho) := by
    apply clear_of_window (wholeLap m a b e p q r 6-wholeLap m a b e p q r 0+rho-1)
    all_goals push_cast at hf6 ⊢; linarith
  have hf7 := tail_phase c g h j p q r hp hq hr hs hg hh hj m a b e rho (7 : Fin 8) (by norm_num)
  norm_num at hf7
  have hc7 : (1/8 : ℝ) ≤ distInt ((speeds c g h j p q r 7-speeds c g h j p q r 0)*outerLapOpening g h j m a b e rho) := by
    apply clear_of_window (wholeLap m a b e p q r 7-wholeLap m a b e p q r 0+rho-0)
    all_goals push_cast at hf7 ⊢; linarith
  intro d hd
  obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
  rw [Fresh.Localisation.distInt_abs_mul]
  fin_cases i
  · exact (hi0 rfl).elim
  · simpa only [prefixIndex] using hprefix 0
  · simpa only [prefixIndex] using hprefix 1
  · simpa only [prefixIndex] using hprefix 2
  · exact hc4
  · exact hc5
  · exact hc6
  · exact hc7

theorem partitions (p q r : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4) :
    (p=1 ∧ q=1 ∧ r=1) ∨ (p=2 ∧ q=1 ∧ r=1) ∨
      (p=1 ∧ q=2 ∧ r=1) ∨ (p=1 ∧ q=1 ∧ r=2) := by omega

#print axioms tail_phase
#print axioms outer_clear
#print axioms partitions
end Fresh.FourBlockOuterTailClear
