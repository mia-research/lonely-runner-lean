import Fresh.FourBlockLeftPacketCharts

/-! Native quartet charts reduce each original left-opening packet to a
finite carry role while retaining unbounded supplied grid labels. -/
namespace Fresh.FourBlockLeftPacketChartsArrangement
open Fresh Fresh.OneMover Fresh.FourBlockNeighbour Fresh.FourBlockLeftOpening
  Fresh.FourBlockLeftPacketCharts Fresh.FourBlockLeftPacketLift

theorem all_subjects (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j) (m a b e unitLap window : ℤ)
    (u : Fin 3) (L : Fin 3 → ℤ) (role : Fin 14) (hm : 1 ≤ m) (hsmall : g+h+j ≤ 3)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hP : 0 < leftOpening c g h j p q r m a b e u (L u))
    (hf : ChartBands c g h j p q r m a b e unitLap window role (leftOpening c g h j p q r m a b e u (L u)))
    (hl : OtherLeftBandsAt c g h j p q r m a b e (leftOpening c g h j p q r m a b e u (L u)) L u)
    (k : Fin 8) : Isolation (speeds c g h j p q r) k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  by_cases hk0 : k=0
  · subst k
    exact ⟨leftOpening c g h j p q r m a b e u (L u),hP,(Fresh.Localisation.isolatedAt_iff _ _ _).2
      (left_clear c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e unitLap window u L role hf hl)⟩
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
def LeftChartsClassAt (V : Fin 8 → ℝ) (p q r : ℕ) (u : Fin 3) (role : Fin 14) : Prop :=
  (∀ i,0 < V i) ∧ Function.Injective V ∧
  ∃ (c g h j B z : ℝ) (m a b e unitLap window : ℤ)
    (L : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 8)),
    1 ≤ p ∧ 1 ≤ q ∧ 1 ≤ r ∧ p+q+r ≤ 4 ∧
    0 < g ∧ 0 < h ∧ 0 < j ∧ 1 ≤ m ∧ g+h+j ≤ 3 ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j ∧
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4 ∧
    0 < leftOpening c g h j p q r m a b e u (L u) ∧
    ChartBands c g h j p q r m a b e unitLap window role (leftOpening c g h j p q r m a b e u (L u)) ∧
    OtherLeftBandsAt c g h j p q r m a b e (leftOpening c g h j p q r m a b e u (L u)) L u ∧ z≠0 ∧
    V=(fun i=>B+z*speeds c g h j p q r (σ i))

-- STANDING: DEFINITION
def LeftChartsClass (V : Fin 8 → ℝ) : Prop :=
  ∃ (p q r : ℕ) (u : Fin 3) (role : Fin 14), LeftChartsClassAt V p q r u role

theorem leftChartsClass_isolation {V : Fin 8 → ℝ} (hV : LeftChartsClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨p,q,r,u,role,hAt⟩ := hV
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,unitLap,window,L,σ,hp,hq,hr,hs,hgpos,hhpos,hjpos,hm,hsmall,
    hg,hh,hj,hsum,hP,hf,hl,hz,hrepr⟩ := hAt
  have hi := all_subjects c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e unitLap window u L role
    hm hsmall hg hh hj hsum hP hf hl (σ k)
  rw [hrepr]
  exact (Fresh.isolation_comp_perm _ σ k).2 (subject_isolation_affine B z hz hi)

theorem finite_normal_form {V : Fin 8 → ℝ} (hV : LeftChartsClass V) :
    ∃ (p q r : ℕ) (u : Fin 3) (role : Fin 14),
      ((p=1 ∧ q=1 ∧ r=1) ∨ (p=2 ∧ q=1 ∧ r=1) ∨
        (p=1 ∧ q=2 ∧ r=1) ∨ (p=1 ∧ q=1 ∧ r=2)) ∧ LeftChartsClassAt V p q r u role := by
  obtain ⟨p,q,r,u,role,hAt⟩ := hV
  have hsave := hAt
  obtain ⟨_,_,c,g,h,j,B,z,m,a,b,e,unitLap,window,L,σ,hp,hq,hr,hs,_⟩ := hAt
  exact ⟨p,q,r,u,role,Fresh.FourBlockOuterTailClear.partitions p q r hp hq hr hs,hsave⟩

theorem leftPacket_into_leftCharts {V : Fin 8 → ℝ}
    (hV : Fresh.FourBlockLeftPacketLiftArrangement.LeftPacketClass V) : LeftChartsClass V := by
  obtain ⟨hpos,hinj,c,g,h,j,B,z,p,q,r,m,a,b,e,unitLap,window,u,L,σ,hp,hq,hr,hs,hgpos,hhpos,hjpos,hm,hsmall,
    hg,hh,hj,hsum,hP,hf,hl,hz,hrepr⟩ := hV
  have ht := residual_bounds c g h j p q r m a b e unitLap window (leftOpening c g h j p q r m a b e u (L u)) hf
  have hc : ChartBands c g h j p q r m a b e unitLap window 0 (leftOpening c g h j p q r m a b e u (L u)) := by
    dsimp [ChartBands,Fresh.UnitAPPacketFourCharts.Chart]
    obtain ⟨h0,hlo,hhi⟩ := hf
    exact ⟨ht.1,ht.2,by linarith,by linarith⟩
  exact ⟨p,q,r,u,0,hpos,hinj,c,g,h,j,B,z,m,a,b,e,unitLap,window,L,σ,
    hp,hq,hr,hs,hgpos,hhpos,hjpos,hm,hsmall,hg,hh,hj,hsum,hP,hc,hl,hz,hrepr⟩

-- STANDING: DEFINITION
def ChartsCoveredClass (V : Fin 8 → ℝ) : Prop :=
  Fresh.FourBlockAPAnchorArrangement.APAnchorCoveredClass V ∨ LeftChartsClass V

theorem chartsCovered_isolation {V : Fin 8 → ℝ} (hV : ChartsCoveredClass V) (k : Fin 8) : Isolation V k := by
  rcases hV with hold|hl
  · exact Fresh.FourBlockAPAnchorArrangement.apAnchorCovered_isolation hold k
  · exact leftChartsClass_isolation hl k

theorem packetLiftCovered_into_chartsCovered {V : Fin 8 → ℝ}
    (hV : Fresh.FourBlockLeftPacketLiftArrangement.PacketLiftCoveredClass V) : ChartsCoveredClass V := by
  rcases hV with hold|hl
  · exact Or.inl hold
  · exact Or.inr (leftPacket_into_leftCharts hl)

#print axioms all_subjects
#print axioms leftChartsClass_isolation
#print axioms finite_normal_form
#print axioms leftPacket_into_leftCharts
#print axioms chartsCovered_isolation
#print axioms packetLiftCovered_into_chartsCovered
end Fresh.FourBlockLeftPacketChartsArrangement
