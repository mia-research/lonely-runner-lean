import Fresh.FourBlockAPAnchor

/-! All physical subjects for the native four-tail anchor cells, retaining
arbitrary original integer laps, signed scale and runner relabelling. -/
namespace Fresh.FourBlockAPAnchorArrangement
open Fresh Fresh.OneMover Fresh.FourBlockNeighbour Fresh.FourBlockAPAnchor Fresh.FourBlockLeftOpening

theorem all_subjects (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j) (m a b e rho unitLap : ℤ)
    (aidx : Fin 4) (L : Fin 3 → ℤ) (hm : 1 ≤ m) (hsmall : g+h+j ≤ 3)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hP : 0 < anchorOpening g h j m a b e rho aidx)
    (h0 : 0 ≤ anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ))
    (h1 : anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ) ≤ 1)
    (hc : Fresh.UnitAPPacketFourLift.Cell aidx (anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ)))
    (hl : LeftBandsAt c g h j p q r m a b e (anchorOpening g h j m a b e rho aidx) L)
    (k : Fin 8) : Isolation (speeds c g h j p q r) k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  by_cases hk0 : k=0
  · subst k
    exact ⟨anchorOpening g h j m a b e rho aidx,hP,(Fresh.Localisation.isolatedAt_iff _ _ _).2
      (anchor_clear c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e rho unitLap aidx L h0 h1 hc hl)⟩
  · by_cases hk7 : k=7
    · subst k
      exact ⟨1/8,by norm_num,Fresh.FourBlockEndpoints.right_direct c g h j p q r hp hq hr (by omega)
        hgpos hhpos hjpos hsmall (by intro hbad; omega)⟩
    · have hn0 := Fin.val_ne_of_ne hk0
      have hn7 := Fin.val_ne_of_ne hk7
      have hi := k.isLt
      exact ⟨(m : ℝ)+1/8,by linarith,
        internal_at_reference c g h j p q r hp hq hr (by omega) m a b e hg hh hj hsum k (by omega) (by omega)⟩

-- STANDING: DEFINITION
def APAnchorClassAt (V : Fin 8 → ℝ) (p q r : ℕ) (aidx : Fin 4) : Prop :=
  (∀ i,0 < V i) ∧ Function.Injective V ∧
  ∃ (c g h j B z : ℝ) (m a b e rho unitLap : ℤ) (L : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 8)),
    1 ≤ p ∧ 1 ≤ q ∧ 1 ≤ r ∧ p+q+r ≤ 4 ∧
    0 < g ∧ 0 < h ∧ 0 < j ∧ 1 ≤ m ∧ g+h+j ≤ 3 ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j ∧
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4 ∧
    0 < anchorOpening g h j m a b e rho aidx ∧
    0 ≤ anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ) ∧
    anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ) ≤ 1 ∧
    Fresh.UnitAPPacketFourLift.Cell aidx (anchorOpening g h j m a b e rho aidx-(m : ℝ)-(unitLap : ℝ)) ∧
    LeftBandsAt c g h j p q r m a b e (anchorOpening g h j m a b e rho aidx) L ∧ z≠0 ∧
    V=(fun i=>B+z*speeds c g h j p q r (σ i))

-- STANDING: DEFINITION
def APAnchorClass (V : Fin 8 → ℝ) : Prop :=
  ∃ (p q r : ℕ) (aidx : Fin 4), APAnchorClassAt V p q r aidx

theorem apAnchorClass_isolation {V : Fin 8 → ℝ} (hV : APAnchorClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨p,q,r,aidx,hAt⟩ := hV
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,rho,unitLap,L,σ,hp,hq,hr,hs,hgpos,hhpos,hjpos,hm,hsmall,
    hg,hh,hj,hsum,hP,h0,h1,hc,hl,hz,hrepr⟩ := hAt
  have hi := all_subjects c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e rho unitLap aidx L
    hm hsmall hg hh hj hsum hP h0 h1 hc hl (σ k)
  rw [hrepr]
  exact (Fresh.isolation_comp_perm _ σ k).2 (subject_isolation_affine B z hz hi)

theorem partition_normal_form {V : Fin 8 → ℝ} (hV : APAnchorClass V) :
    ∃ (p q r : ℕ) (aidx : Fin 4),
      ((p=1 ∧ q=1 ∧ r=1) ∨ (p=2 ∧ q=1 ∧ r=1) ∨
        (p=1 ∧ q=2 ∧ r=1) ∨ (p=1 ∧ q=1 ∧ r=2)) ∧ APAnchorClassAt V p q r aidx := by
  obtain ⟨p,q,r,aidx,hAt⟩ := hV
  have hsave := hAt
  obtain ⟨_,_,c,g,h,j,B,z,m,a,b,e,rho,unitLap,L,σ,hp,hq,hr,hs,_⟩ := hAt
  exact ⟨p,q,r,aidx,Fresh.FourBlockOuterTailClear.partitions p q r hp hq hr hs,hsave⟩

-- STANDING: DEFINITION
def APAnchorCoveredClass (V : Fin 8 → ℝ) : Prop :=
  Fresh.FourBlockPacketFrameArrangement.PacketFrameCoveredClass V ∨ APAnchorClass V

theorem apAnchorCovered_isolation {V : Fin 8 → ℝ} (hV : APAnchorCoveredClass V) (k : Fin 8) : Isolation V k := by
  rcases hV with hold|ha
  · exact Fresh.FourBlockPacketFrameArrangement.packetFrameCovered_isolation hold k
  · exact apAnchorClass_isolation ha k

#print axioms all_subjects
#print axioms apAnchorClass_isolation
#print axioms partition_normal_form
#print axioms apAnchorCovered_isolation
end Fresh.FourBlockAPAnchorArrangement
