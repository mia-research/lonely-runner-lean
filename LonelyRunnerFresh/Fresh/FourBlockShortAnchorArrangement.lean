import Fresh.FourBlockShortOpeningArrangement

/-! AP-anchor inputs enter the same short-packet opening family. Their
one-dimensional exact cells derive the six-chart packet condition. -/
namespace Fresh.FourBlockShortAnchorArrangement
open Fresh Fresh.OneMover Fresh.FourBlockNeighbour Fresh.FourBlockShortTail
  Fresh.FourBlockShortAnchor Fresh.FourBlockShortOpeningArrangement

def anchorIndex (a : Fin 3) : Fin 7 := ⟨a.val+4,by omega⟩

theorem opening_anchor_eq (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 5)
    (m a b e rho : ℤ) (aidx : Fin 3) :
    Fresh.FourBlockShortOpening.opening c g h j p q r m a b e rho (anchorIndex aidx)=
      anchorOpening g h j m a b e rho aidx := by
  have hi : Fresh.FourBlockShortOpening.openingIndex (anchorIndex aidx)=tailIndex aidx := by
    apply Fin.ext
    simp [Fresh.FourBlockShortOpening.openingIndex,anchorIndex,tailIndex]
  dsimp [Fresh.FourBlockShortOpening.opening,Fresh.FourBlockShortOpening.lap,Fresh.FourBlockShortOpening.reading]
  rw [hi,tail_lap p q r hp hq hr hs m a b e _ (by dsimp [tailIndex]; omega),
    tail_reading c g h j p q r hp hq hr hs _ (by dsimp [tailIndex]; omega)]
  dsimp [anchorOpening,tailIndex]
  congr 1 <;> push_cast <;> ring

def AllCutBands (c g h j : ℝ) (p q r : ℕ) (m a b e : ℤ) (P : ℝ) (L : Fin 4 → ℤ) : Prop :=
  ∀ v : Fin 4, ((cutLap m a b e p q r v+L v : ℤ) : ℝ)+1/8 ≤ cutReading c g h j p q r v*P ∧
    cutReading c g h j p q r v*P ≤ ((cutLap m a b e p q r v+L v : ℤ) : ℝ)+7/8

-- STANDING: DEFINITION
def ShortAnchorClassAt (V : Fin 8 → ℝ) (p q r : ℕ) (aidx : Fin 3) : Prop :=
  (∀ i,0 < V i) ∧ Function.Injective V ∧
  ∃ (c g h j B z : ℝ) (m a b e rho unitLap : ℤ) (L : Fin 4 → ℤ) (σ : Equiv.Perm (Fin 8)),
    1 ≤ p ∧ 1 ≤ q ∧ 1 ≤ r ∧ p+q+r=5 ∧
    0 < g ∧ 0 < h ∧ 0 < j ∧ 1 ≤ m ∧ g+h+j ≤ 3 ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j ∧
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4 ∧
    0 < anchorOpening g h j m a b e rho aidx ∧
    0 ≤ anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ) ∧
    anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ) ≤ 1 ∧
    Fresh.UnitAPPacketThreeCells.Cell aidx (anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ)) ∧
    AllCutBands c g h j p q r m a b e (anchorOpening g h j m a b e rho aidx) L ∧
    z≠0 ∧ V=(fun i=>B+z*speeds c g h j p q r (σ i))

-- STANDING: DEFINITION
def ShortAnchorClass (V : Fin 8 → ℝ) : Prop := ∃ (p q r : ℕ) (aidx : Fin 3), ShortAnchorClassAt V p q r aidx

theorem shortAnchor_into_shortOpening {V : Fin 8 → ℝ} (hV : ShortAnchorClass V) : ShortOpeningClass V := by
  obtain ⟨p,q,r,aidx,hAt⟩ := hV
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,rho,unitLap,L,σ,hp,hq,hr,hs,hg,hh,hj,hm,hsmall,
    hga,hgb,hge,hsum,hP,h0,h1,hcell,hcuts,hz,hrepr⟩ := hAt
  obtain ⟨window,role,hpacket⟩ := anchor_packet_bands c g h j p q r hp hq hr (by omega) hg hh hj
    m a b e rho unitLap aidx h0 h1 hcell
  have he := opening_anchor_eq c g h j p q r hp hq hr (by omega) m a b e rho aidx
  have hb : Fresh.FourBlockShortOpening.RemainingCutBands c g h j p q r m a b e
      (Fresh.FourBlockShortOpening.opening c g h j p q r m a b e rho (anchorIndex aidx)) L (anchorIndex aidx) := by
    intro v hv
    rw [he]
    exact hcuts v
  refine ⟨p,q,r,anchorIndex aidx,role,hpos,hinj,c,g,h,j,B,z,m,a,b,e,rho,unitLap,window,L,σ,
    hp,hq,hr,hs,hg,hh,hj,hm,hsmall,hga,hgb,hge,hsum,?_,?_,hb,hz,hrepr⟩
  · rwa [he]
  · rwa [he]

theorem shortAnchor_isolation {V : Fin 8 → ℝ} (hV : ShortAnchorClass V) (k : Fin 8) : Isolation V k := by
  exact shortOpeningClass_isolation (shortAnchor_into_shortOpening hV) k

#print axioms opening_anchor_eq
#print axioms shortAnchor_into_shortOpening
#print axioms shortAnchor_isolation
end Fresh.FourBlockShortAnchorArrangement
