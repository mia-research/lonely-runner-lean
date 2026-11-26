import Fresh.FourBlockFourthArrangement

/-! The original outer endpoint returns on its next lap. Exact opening
identities expose the closed join with the earlier fourth-opening escape. -/
namespace Fresh.FourBlockOuterReturnBounds
open Fresh Fresh.FourBlockNeighbour Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailBounds

noncomputable def returnOpening (g h j : ℝ) (m a b e : ℤ) : ℝ :=
  ((spanLap m a b e : ℝ)+17/8)/(4+g+h+j)

theorem return_identity (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ) :
    (4+g+h+j)*returnOpening g h j m a b e=(spanLap m a b e : ℝ)+17/8 := by
  have hpos : 0 < 4+g+h+j := by linarith
  dsimp [returnOpening]
  field_simp [ne_of_gt hpos]

theorem return_delta (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ) :
    (4+g+h+j)*(returnOpening g h j m a b e-((m : ℝ)+1/8))=
      17/8-remainder g h j m a b e := by
  have hid := return_identity g h j hg hh hj m a b e
  dsimp [spanLap] at hid
  dsimp [remainder]
  push_cast at hid
  nlinarith only [hid]

theorem return_bounds (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ)
    (hlo : 3*(g+h+j)+16*remainder g h j m a b e ≤ 22)
    (hhi : 31 ≤ 5*(g+h+j)+24*remainder g h j m a b e) :
    (m : ℝ)+5/16 ≤ returnOpening g h j m a b e ∧
    returnOpening g h j m a b e ≤ (m : ℝ)+1/3 := by
  have hd := return_delta g h j hg hh hj m a b e
  have hp : 0 < 4+g+h+j := by linarith
  constructor <;> nlinarith

theorem return_phase (c g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ) (i : Fin 8) (hi : 3 ≤ (i : ℕ)) :
    (speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 0)*returnOpening g h j m a b e-
      ((wholeLap m a b e 1 1 1 i-wholeLap m a b e 1 1 1 0 : ℤ) : ℝ)=
      17/8-(7-(i : ℝ))*(returnOpening g h j m a b e-(m : ℝ)) := by
  have h1 : (1 : ℕ) ≤ (i : ℕ) := by omega
  have h2 : (2 : ℕ) ≤ (i : ℕ) := by omega
  have hD : speeds c g h j 1 1 1 i-speeds c g h j 1 1 1 0=(i : ℝ)-3+g+h+j := by
    norm_num [speeds,h1,h2,hi]
    ring
  have hN : wholeLap m a b e 1 1 1 i-wholeLap m a b e 1 1 1 0=
      ((((i : ℕ) : ℤ)-3)*m+a+b+e) := by
    norm_num [wholeLap,h1,h2,hi]
    ring
  rw [hD,hN]
  have hid := return_identity g h j hg hh hj m a b e
  dsimp [spanLap] at hid
  push_cast at hid ⊢
  nlinarith only [hid]

theorem capture_bounds (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ) (hRhi : remainder g h j m a b e ≤ 1)
    (hlo : 3*(g+h+j)+16*remainder g h j m a b e ≤ 22)
    (hhi : 31 < 5*(g+h+j)+24*remainder g h j m a b e) :
    (m : ℝ)+1/4 < packetOpening g h j m a b e 3 ∧
    packetOpening g h j m a b e 3 < (m : ℝ)+1/3 := by
  have hd := packet_delta g h j hg hh hj m a b e 3 (by norm_num)
  have hp : 0 < 4+g+h+j-(3 : ℝ) := by linarith
  have hs : g+h+j+8*remainder g h j m a b e ≤ 10 := by linarith
  norm_num at hd
  constructor <;> nlinarith

theorem closed_join (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ) (hface : 5*(g+h+j)+24*remainder g h j m a b e=31) :
    returnOpening g h j m a b e=packetOpening g h j m a b e 3 := by
  have hD : 0 < 4+g+h+j := by linarith
  have hD3 : 0 < 4+g+h+j-(3 : ℝ) := by linarith
  have hd := packet_delta g h j hg hh hj m a b e 3 (by norm_num)
  have hP : packetOpening g h j m a b e 3=(m : ℝ)+1/3 := by
    norm_num at hd
    nlinarith
  have hr := return_identity g h j hg hh hj m a b e
  have hp := packet_identity g h j hg hh hj m a b e 3 (by norm_num)
  push_cast at hp
  nlinarith only [hr,hp,hP,hD]

#print axioms return_identity
#print axioms return_delta
#print axioms return_bounds
#print axioms return_phase
#print axioms capture_bounds
#print axioms closed_join
end Fresh.FourBlockOuterReturnBounds
