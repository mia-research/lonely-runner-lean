import Fresh.FourBlockMiddleOpeningRecovery
import Fresh.FourBlockReversal

/-! Entry-defined joins into the existing physical families. The endpoint
choices may use an earlier checked opening or derive a new one from actual
capture and original-face recovery. No redundant catalogue branch is added. -/
namespace Fresh.FourBlockPacketEntryArrangement
open Fresh Fresh.OneMover Fresh.FourBlockNeighbour Fresh.FourBlockDoubleSingleton

noncomputable def RecoveredEndpointData (c g h j : ℝ) (q r : ℕ) (m a d e : ℤ) (right : Bool) : Prop :=
  ∃ (b : Fin 6) (u : Fin 7) (role : Fin 6) (rho unitLap window : ℤ) (L : Fin 8 → ℤ) (Q : ℝ),
    Host q r b ∧ 0 < Q ∧
    (rho : ℝ)-1/8 < phase c g h j q r right m a d e (openingIndex right u) Q ∧
    phase c g h j q r right m a d e (openingIndex right u) Q < (rho : ℝ)+1/8 ∧
    Fresh.FourBlockDoubleOpeningRecovery.PacketRecovery c g h j q r b right m a d e rho unitLap window Q u role ∧
    Fresh.FourBlockDoubleOpeningRecovery.OutsideRecovery c g h j q r b right m a d e rho Q u L

theorem endpointData_of_recovery (c g h j : ℝ) (q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a d e : ℤ) (right : Bool)
    (hd : RecoveredEndpointData c g h j q r m a d e right) :
    Fresh.FourBlockDoubleSingletonArrangement.EndpointData c g h j q r m a d e right := by
  obtain ⟨b,u,role,rho,unitLap,window,L,Q,hhost,hQ,hlo,hhi,hpkt,hcuts⟩ := hd
  have ht := Fresh.FourBlockDoubleOpeningRecovery.capture_advance c g h j q r hq hr hg hh hj right m a d e rho Q u hlo hhi
  exact ⟨b,u,role,rho,unitLap,window,L,hhost,lt_trans hQ ht,
    Fresh.FourBlockDoubleOpeningRecovery.recovered_packet c g h j q r b hq hr hhost hg hh hj right m a d e rho unitLap window Q u role hlo hhi hpkt,
    Fresh.FourBlockDoubleOpeningRecovery.recovered_cuts c g h j q r b hq hr hg hh hj right m a d e rho Q u L hlo hhi hcuts⟩

-- STANDING: DEFINITION
noncomputable def DoubleEntryClassAt (V : Fin 8 → ℝ) (q r : ℕ) : Prop :=
  (∀ i,0 < V i) ∧ Function.Injective V ∧
  ∃ (c g h j B z : ℝ) (m a d e : ℤ) (σ : Equiv.Perm (Fin 8)),
    1 ≤ q ∧ 1 ≤ r ∧ q+r=6 ∧ 0 < g ∧ 0 < h ∧ 0 < j ∧ 1 ≤ m ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(d : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j ∧
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(d : ℝ)+(e : ℝ))+4 ∧
    (∀ right : Bool, Fresh.FourBlockDoubleSingletonArrangement.EndpointData c g h j q r m a d e right ∨
      RecoveredEndpointData c g h j q r m a d e right) ∧ z≠0 ∧
    V=(fun i=>B+z*speeds c g h j 1 q r (σ i))

-- STANDING: DEFINITION
noncomputable def DoubleEntryClass (V : Fin 8 → ℝ) : Prop := ∃ q r : ℕ, DoubleEntryClassAt V q r

theorem doubleEntry_into_double {V : Fin 8 → ℝ} (hV : DoubleEntryClass V) :
    Fresh.FourBlockDoubleSingletonArrangement.DoubleSingletonClass V := by
  obtain ⟨q,r,hpos,hinj,c,g,h,j,B,z,m,a,d,e,σ,hq,hr,hs,hg,hh,hj,hm,hga,hgd,hge,hsum,hd,hz,hrepr⟩ := hV
  refine ⟨q,r,hpos,hinj,c,g,h,j,B,z,m,a,d,e,σ,hq,hr,hs,hg,hh,hj,hm,hga,hgd,hge,hsum,?_,hz,hrepr⟩
  intro right
  rcases hd right with hold|hentry
  · exact hold
  · exact endpointData_of_recovery c g h j q r hq hr hg hh hj m a d e right hentry

theorem double_into_doubleEntry {V : Fin 8 → ℝ}
    (hV : Fresh.FourBlockDoubleSingletonArrangement.DoubleSingletonClass V) : DoubleEntryClass V := by
  obtain ⟨q,r,hpos,hinj,c,g,h,j,B,z,m,a,d,e,σ,hq,hr,hs,hg,hh,hj,hm,hga,hgd,hge,hsum,hd,hz,hrepr⟩ := hV
  exact ⟨q,r,hpos,hinj,c,g,h,j,B,z,m,a,d,e,σ,hq,hr,hs,hg,hh,hj,hm,hga,hgd,hge,hsum,fun right => Or.inl (hd right),hz,hrepr⟩

theorem doubleEntry_isolation {V : Fin 8 → ℝ} (hV : DoubleEntryClass V) (k : Fin 8) : Isolation V k :=
  Fresh.FourBlockDoubleSingletonArrangement.doubleSingleton_isolation (doubleEntry_into_double hV) k

-- STANDING: DEFINITION
noncomputable def MiddleEntryClassAt (V : Fin 8 → ℝ) (p q r : ℕ) (b : Fin 6) (u : Fin 7) (role : Fin 6) : Prop :=
  (∀ i,0 < V i) ∧ Function.Injective V ∧
  ∃ (c g h j B z Q : ℝ) (m a d e rho unitLap window : ℤ) (L : Fin 8 → ℤ) (σ : Equiv.Perm (Fin 8)),
    1 ≤ p ∧ 1 ≤ q ∧ 1 ≤ r ∧ Fresh.FourBlockMiddlePacket.MiddleHost p q r b ∧
    0 < g ∧ 0 < h ∧ 0 < j ∧ 1 ≤ m ∧ g+h+j ≤ 3 ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(d : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j ∧
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(d : ℝ)+(e : ℝ))+4 ∧ 0 < Q ∧
    (rho : ℝ)-1/8 < Fresh.FourBlockShortOpening.reading c g h j p q r u*Q-(Fresh.FourBlockShortOpening.lap m a d e p q r u : ℝ) ∧
    Fresh.FourBlockShortOpening.reading c g h j p q r u*Q-(Fresh.FourBlockShortOpening.lap m a d e p q r u : ℝ) < (rho : ℝ)+1/8 ∧
    Fresh.FourBlockMiddleOpeningRecovery.PacketRecovery c g h j p q r b m a d e rho unitLap window Q u role ∧
    Fresh.FourBlockMiddleOpeningRecovery.OutsideRecovery c g h j p q r b m a d e rho Q u L ∧ z≠0 ∧
    V=(fun i=>B+z*speeds c g h j p q r (σ i))

-- STANDING: DEFINITION
noncomputable def MiddleEntryClass (V : Fin 8 → ℝ) : Prop :=
  ∃ (p q r : ℕ) (b : Fin 6) (u : Fin 7) (role : Fin 6), MiddleEntryClassAt V p q r b u role

theorem middleEntry_into_middle {V : Fin 8 → ℝ} (hV : MiddleEntryClass V) :
    Fresh.FourBlockMiddlePacketArrangement.MiddlePacketClass V := by
  obtain ⟨p,q,r,b,u,role,hpos,hinj,c,g,h,j,B,z,Q,m,a,d,e,rho,unitLap,window,L,σ,hp,hq,hr,hhost,hg,hh,hj,hm,hsmall,
    hga,hgd,hge,hsum,hQ,hlo,hhi,hpkt,hcuts,hz,hrepr⟩ := hV
  have ht := (Fresh.FourBlockShortOpeningMoves.capture_opening c g h j p q r hq hr hg hh hj m a d e u rho Q hlo hhi).2.2
  exact ⟨p,q,r,b,u,role,hpos,hinj,c,g,h,j,B,z,m,a,d,e,rho,unitLap,window,L,σ,hp,hq,hr,hhost,hg,hh,hj,hm,hsmall,
    hga,hgd,hge,hsum,lt_trans hQ ht,
    Fresh.FourBlockMiddleOpeningRecovery.recovered_packet c g h j p q r b hp hq hr hhost hg hh hj m a d e rho unitLap window Q u role hlo hhi hpkt,
    Fresh.FourBlockMiddleOpeningRecovery.recovered_cuts c g h j p q r b hq hr hg hh hj m a d e rho Q u L hlo hhi hcuts,hz,hrepr⟩

theorem middleEntry_isolation {V : Fin 8 → ℝ} (hV : MiddleEntryClass V) (k : Fin 8) : Isolation V k :=
  Fresh.FourBlockMiddlePacketArrangement.middlePacket_isolation (middleEntry_into_middle hV) k

#print axioms endpointData_of_recovery
#print axioms doubleEntry_into_double
#print axioms double_into_doubleEntry
#print axioms doubleEntry_isolation
#print axioms middleEntry_into_middle
#print axioms middleEntry_isolation
end Fresh.FourBlockPacketEntryArrangement
