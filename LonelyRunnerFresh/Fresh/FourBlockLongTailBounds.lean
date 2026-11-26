import Fresh.FourBlockEndpointSecondMove
import Fresh.EndpointRetainedSegment

/-! Exact native AP-packet openings for an opposite block of length at least4.
The exit inequality is a closed clearance face of the next original reading,
not a bound on the length of an arbitrary cascade. -/
namespace Fresh.FourBlockLongTailBounds
open Fresh Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour Fresh.FourBlockEndpointCapture

noncomputable def packetOpening (g h j : ℝ) (m a b e s : ℤ) : ℝ :=
  (((spanLap m a b e-s*m : ℤ) : ℝ)+9/8)/(4+g+h+j-(s : ℝ))

theorem tail_reading (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (i : Fin 8) (hi : 4 ≤ (i : ℕ)) :
    speeds c g h j p q r i-speeds c g h j p q r 0=(i : ℝ)-3+g+h+j := by
  have hpi : p ≤ (i : ℕ) := by omega
  have hpqi : p+q ≤ (i : ℕ) := by omega
  have hpqri : p+q+r ≤ (i : ℕ) := by omega
  have h0p : ¬p ≤ 0 := by omega
  have h0q : ¬p+q ≤ 0 := by omega
  have h0r : ¬p+q+r ≤ 0 := by omega
  norm_num [speeds,hpi,hpqi,hpqri,h0p,h0q,h0r]
  ring

theorem tail_lap (p q r : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hs : p+q+r ≤ 4) (m a b e : ℤ) (i : Fin 8) (hi : 4 ≤ (i : ℕ)) :
    wholeLap m a b e p q r i-wholeLap m a b e p q r 0=
      ((((i : ℕ) : ℤ)-3)*m+a+b+e) := by
  have hpi : p ≤ (i : ℕ) := by omega
  have hpqi : p+q ≤ (i : ℕ) := by omega
  have hpqri : p+q+r ≤ (i : ℕ) := by omega
  have h0p : ¬p ≤ 0 := by omega
  have h0q : ¬p+q ≤ 0 := by omega
  have h0r : ¬p+q+r ≤ 0 := by omega
  norm_num [wholeLap,hpi,hpqi,hpqri,h0p,h0q,h0r]
  ring

theorem packet_identity (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e s : ℤ) (hs : (s : ℝ) ≤ 3) :
    (4+g+h+j-(s : ℝ))*packetOpening g h j m a b e s=
      ((spanLap m a b e-s*m : ℤ) : ℝ)+9/8 := by
  have hpos : 0 < 4+g+h+j-(s : ℝ) := by linarith
  dsimp [packetOpening]
  field_simp [ne_of_gt hpos]

theorem packet_delta (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e s : ℤ) (hs : (s : ℝ) ≤ 3) :
    (4+g+h+j-(s : ℝ))*(packetOpening g h j m a b e s-((m : ℝ)+1/8))=
      (9+(s : ℝ))/8-remainder g h j m a b e := by
  have hid := packet_identity g h j hg hh hj m a b e s hs
  dsimp [remainder] at *
  dsimp [spanLap] at hid
  push_cast at hid
  nlinarith only [hid]

theorem first_partner_bounds (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ) (hlo : (7/8 : ℝ) ≤ remainder g h j m a b e)
    (hhi : remainder g h j m a b e ≤ 1) :
    (m : ℝ)+1/8 < packetOpening g h j m a b e 1 ∧
    packetOpening g h j m a b e 1 < (m : ℝ)+1/4 := by
  have hd := packet_delta g h j hg hh hj m a b e 1 (by norm_num)
  norm_num at hd
  have hp : 3 < 4+g+h+j-(1 : ℝ) := by linarith
  constructor <;> nlinarith

theorem second_partner_bounds (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ) (hlo : (7/8 : ℝ) ≤ remainder g h j m a b e)
    (hhi : remainder g h j m a b e ≤ 1) :
    (m : ℝ)+1/8 < packetOpening g h j m a b e 2 ∧
    packetOpening g h j m a b e 2 < (m : ℝ)+3/8 := by
  have hd := packet_delta g h j hg hh hj m a b e 2 (by norm_num)
  norm_num at hd
  have hp : 2 < 4+g+h+j-(2 : ℝ) := by linarith
  constructor <;> nlinarith

theorem exit_face (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (m a b e : ℤ) :
    (m : ℝ)+1/4 ≤ packetOpening g h j m a b e 2 ↔
      g+h+j+8*remainder g h j m a b e ≤ 9 := by
  have hd := packet_delta g h j hg hh hj m a b e 2 (by norm_num)
  norm_num at hd
  have hp : 0 < 4+g+h+j-(2 : ℝ) := by linarith
  constructor <;> intro h <;> nlinarith

#print axioms tail_reading
#print axioms tail_lap
#print axioms packet_identity
#print axioms packet_delta
#print axioms first_partner_bounds
#print axioms second_partner_bounds
#print axioms exit_face
end Fresh.FourBlockLongTailBounds
