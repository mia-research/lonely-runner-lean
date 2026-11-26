import Fresh.FourBlockOpeningRecovery

/-! Entry-defined recovery families embed into the existing native chart
catalogue. Original outside cuts may remain in or advance their windows. -/
namespace Fresh.FourBlockOpeningRecoveryArrangement
open Fresh Fresh.OneMover Fresh.FourBlockNeighbour Fresh.FourBlockLeftOpening
  Fresh.FourBlockLeftPacketCharts Fresh.FourBlockOpeningRecovery

-- STANDING: DEFINITION
def RecoveryClassAt (V : Fin 8 → ℝ) (p q r : ℕ) (u : Fin 3) (role : Fin 14) : Prop :=
  (∀ i,0 < V i) ∧ Function.Injective V ∧
  ∃ (c g h j B z Q : ℝ) (m a b e unitLap window : ℤ)
    (L : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 8)),
    1 ≤ p ∧ 1 ≤ q ∧ 1 ≤ r ∧ p+q+r ≤ 4 ∧
    0 < g ∧ 0 < h ∧ 0 < j ∧ 1 ≤ m ∧ g+h+j ≤ 3 ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j ∧
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4 ∧
    0 < Q ∧
    (L u : ℝ)-1/8 < leftReading c g h j p q r u*Q-(leftLap m a b e p q r u : ℝ) ∧
    leftReading c g h j p q r u*Q-(leftLap m a b e p q r u : ℝ) < (L u : ℝ)+1/8 ∧
    PacketRecovery c g h j p q r m a b e unitLap window u L role ∧
    OutsideRecovery c g h j p q r m a b e Q u L ∧
    z≠0 ∧ V=(fun i=>B+z*speeds c g h j p q r (σ i))

-- STANDING: DEFINITION
def RecoveryClass (V : Fin 8 → ℝ) : Prop := ∃ (p q r : ℕ) (u : Fin 3) (role : Fin 14), RecoveryClassAt V p q r u role

theorem recovery_into_leftCharts {V : Fin 8 → ℝ} (hV : RecoveryClass V) :
    Fresh.FourBlockLeftPacketChartsArrangement.LeftChartsClass V := by
  obtain ⟨p,q,r,u,role,hAt⟩ := hV
  obtain ⟨hpos,hinj,c,g,h,j,B,z,Q,m,a,b,e,unitLap,window,L,σ,hp,hq,hr,hs,hg,hh,hj,hm,hsmall,
    hga,hgb,hge,hsum,hQ,hlo,hhi,hpacket,hcuts,hz,hrepr⟩ := hAt
  have ht := (capture_opening c g h j p q r hq hr hg hh hj m a b e u (L u) Q hlo hhi).2.2
  have hpkt := recovered_packet c g h j p q r hp hq hr hs hg hh hj m a b e unitLap window u L role hpacket
  have hcut := recovered_cuts c g h j p q r hq hr hg hh hj m a b e Q u L hlo hhi hcuts
  exact ⟨p,q,r,u,role,hpos,hinj,c,g,h,j,B,z,m,a,b,e,unitLap,window,L,σ,
    hp,hq,hr,hs,hg,hh,hj,hm,hsmall,hga,hgb,hge,hsum,lt_trans hQ ht,hpkt,hcut,hz,hrepr⟩

theorem recovery_isolation {V : Fin 8 → ℝ} (hV : RecoveryClass V) (k : Fin 8) : Isolation V k := by
  exact Fresh.FourBlockLeftPacketChartsArrangement.leftChartsClass_isolation (recovery_into_leftCharts hV) k

theorem finite_normal_form {V : Fin 8 → ℝ} (hV : RecoveryClass V) :
    ∃ (p q r : ℕ) (u : Fin 3) (role : Fin 14),
      ((p=1 ∧ q=1 ∧ r=1) ∨ (p=2 ∧ q=1 ∧ r=1) ∨
        (p=1 ∧ q=2 ∧ r=1) ∨ (p=1 ∧ q=1 ∧ r=2)) ∧ RecoveryClassAt V p q r u role := by
  obtain ⟨p,q,r,u,role,hAt⟩ := hV
  have hsave := hAt
  obtain ⟨_,_,c,g,h,j,B,z,Q,m,a,b,e,unitLap,window,L,σ,hp,hq,hr,hs,_⟩ := hAt
  exact ⟨p,q,r,u,role,Fresh.FourBlockOuterTailClear.partitions p q r hp hq hr hs,hsave⟩

#print axioms recovery_into_leftCharts
#print axioms recovery_isolation
#print axioms finite_normal_form
end Fresh.FourBlockOpeningRecoveryArrangement
