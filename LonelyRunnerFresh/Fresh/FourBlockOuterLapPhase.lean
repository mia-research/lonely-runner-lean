import Fresh.FourBlockFiveReturnArrangement

/-! The original outer opening retains an arbitrary integer return lap.
Its unit AP packet uses the same anchor law on every such lap. -/
namespace Fresh.FourBlockOuterLapPhase
open Fresh Fresh.FourBlockNeighbour Fresh.FourBlockEndpointCapture

noncomputable def outerLapOpening (g h j : ℝ) (m a b e r : ℤ) : ℝ :=
  ((spanLap m a b e : ℝ)+(r : ℝ)+1/8)/(4+g+h+j)

theorem opening_identity (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e r : ℤ) :
    (4+g+h+j)*outerLapOpening g h j m a b e r=(spanLap m a b e : ℝ)+(r : ℝ)+1/8 := by
  have hp : 0 < 4+g+h+j := by linarith
  dsimp [outerLapOpening]
  field_simp [ne_of_gt hp]

theorem opening_delta (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e r : ℤ) :
    (4+g+h+j)*(outerLapOpening g h j m a b e r-((m : ℝ)+1/8))=
      (r : ℝ)+1/8-remainder g h j m a b e := by
  have hid := opening_identity g h j hg hh hj m a b e r
  dsimp [spanLap] at hid
  dsimp [remainder]
  push_cast at hid
  nlinarith only [hid]

theorem opening_bounds (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e r : ℤ)
    (hlo : 11*(g+h+j)+16*remainder g h j m a b e ≤ 16*(r : ℝ)-42)
    (hhi : 8*(r : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e) :
    (m : ℝ)+13/16 ≤ outerLapOpening g h j m a b e r ∧
    outerLapOpening g h j m a b e r ≤ (m : ℝ)+1 := by
  have hd := opening_delta g h j hg hh hj m a b e r
  have hp : 0 < 4+g+h+j := by linarith
  constructor <;> nlinarith

theorem packet_phase (c g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e r : ℤ) (i : Fin 8) (hi : 3 ≤ (i : ℕ)) :
    (speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 0)*outerLapOpening g h j m a b e r-
      ((wholeLap m a b e 1 1 1 i-wholeLap m a b e 1 1 1 0 : ℤ) : ℝ)=
      (r : ℝ)+1/8+((i : ℝ)-7)*(outerLapOpening g h j m a b e r-(m : ℝ)) := by
  let N : Fin 8 → ℤ := fun u=>wholeLap m a b e 1 1 1 u-wholeLap m a b e 1 1 1 0
  have h1 : (1 : ℕ) ≤ (i : ℕ) := by omega
  have h2 : (2 : ℕ) ≤ (i : ℕ) := by omega
  have hs : speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 7=((i : ℝ)-7)*1 := by
    norm_num [speeds,h1,h2,hi]
  have hn : N i-N 7=(((i : ℕ) : ℤ)-((7 : Fin 8) : ℕ))*m := by
    dsimp [N]
    norm_num [wholeLap,h1,h2,hi]
    ring
  have ha : (speeds c g h j 1 1 1 7-speeds c g h j 1 1 1 0)*outerLapOpening g h j m a b e r=
      (N 7 : ℝ)+(r : ℝ)+1/8 := by
    have hid := opening_identity g h j hg hh hj m a b e r
    norm_num [N,wholeLap,speeds,spanLap] at *
    nlinarith only [hid]
  have hp := Fresh.UnitAPPacketPhase.phase_at_anchor (speeds c g h j 1 1 1) N 0 7 i 1
    (outerLapOpening g h j m a b e r) m r hs hn ha
  norm_num at hp
  exact hp

#print axioms opening_identity
#print axioms opening_delta
#print axioms opening_bounds
#print axioms packet_phase
end Fresh.FourBlockOuterLapPhase
