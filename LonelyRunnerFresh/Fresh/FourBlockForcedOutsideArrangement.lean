import Fresh.FourBlockOutsideTransport

/-! Entry-defined fastest outside families. Neither the two other target
cut bands nor the target packet chart are assumptions: both are derived. -/
namespace Fresh.FourBlockForcedOutsideArrangement
open Fresh Fresh.OneMover Fresh.FourBlockNeighbour Fresh.FourBlockLeftOpening
  Fresh.FourBlockLeftPacketCharts Fresh.FourBlockOutsideTransport Fresh.UnitAPPacketChartMotion

-- STANDING: DEFINITION
def ForcedOutsideClassAt (V : Fin 8 → ℝ) (p q r : ℕ) (before after : Fin 14) : Prop :=
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
    (L 2 : ℝ)-1/8 < leftReading c g h j p q r 2*Q-(leftLap m a b e p q r 2 : ℝ) ∧
    leftReading c g h j p q r 2*Q-(leftLap m a b e p q r 2 : ℝ) < (L 2 : ℝ)+1/8 ∧
    EntryMiddleCuts c g h j p q r m a b e Q L ∧
    ChartBands c g h j p q r m a b e unitLap window before Q ∧ Compatible before after ∧
    PacketClosing c g h j p q r m a b e unitLap window after Q (leftOpening c g h j p q r m a b e 2 (L 2)) ∧
    z≠0 ∧ V=(fun i=>B+z*speeds c g h j p q r (σ i))

-- STANDING: DEFINITION
def ForcedOutsideClass (V : Fin 8 → ℝ) : Prop :=
  ∃ (p q r : ℕ) (before after : Fin 14), ForcedOutsideClassAt V p q r before after

theorem forcedOutside_into_leftCharts {V : Fin 8 → ℝ} (hV : ForcedOutsideClass V) :
    Fresh.FourBlockLeftPacketChartsArrangement.LeftChartsClass V := by
  obtain ⟨p,q,r,before,after,hAt⟩ := hV
  obtain ⟨hpos,hinj,c,g,h,j,B,z,Q,m,a,b,e,unitLap,window,L,σ,hp,hq,hr,hs,hg,hh,hj,hm,hsmall,
    hga,hgb,hge,hsum,hQ,hlo,hhi,hmid,hchart,hlabels,hclose,hz,hrepr⟩ := hAt
  have ht := (capture_opening c g h j p q r hq hr hg hh hj m a b e 2 (L 2) Q hlo hhi).2.2
  have hpacket := packet_transport c g h j p q r hp hq hr hs hg hh hj m a b e unitLap window before after Q
    (leftOpening c g h j p q r m a b e 2 (L 2)) ht.le hchart hlabels hclose
  have hcuts := fast_other_cuts c g h j p q r hq hr hg hh hj m a b e Q L hlo hhi hmid
  exact ⟨p,q,r,2,after,hpos,hinj,c,g,h,j,B,z,m,a,b,e,unitLap,window,L,σ,
    hp,hq,hr,hs,hg,hh,hj,hm,hsmall,hga,hgb,hge,hsum,lt_trans hQ ht,hpacket,hcuts,hz,hrepr⟩

theorem forcedOutside_isolation {V : Fin 8 → ℝ} (hV : ForcedOutsideClass V) (k : Fin 8) : Isolation V k := by
  exact Fresh.FourBlockLeftPacketChartsArrangement.leftChartsClass_isolation (forcedOutside_into_leftCharts hV) k

theorem finite_forward_roles {V : Fin 8 → ℝ} (hV : ForcedOutsideClass V) :
    ∃ (p q r : ℕ) (before after : Fin 14),
      ((p=1 ∧ q=1 ∧ r=1) ∨ (p=2 ∧ q=1 ∧ r=1) ∨
        (p=1 ∧ q=2 ∧ r=1) ∨ (p=1 ∧ q=1 ∧ r=2)) ∧
      (before=after ∨ (before=1 ∧ after=2) ∨ (before=3 ∧ after=4) ∨
        (before=5 ∧ after=6) ∨ (before=7 ∧ after=8) ∨
        (before=9 ∧ after=10) ∨ (before=11 ∧ after=12)) ∧ ForcedOutsideClassAt V p q r before after := by
  obtain ⟨p,q,r,before,after,hAt⟩ := hV
  have hsave := hAt
  obtain ⟨hpos,hinj,c,g,h,j,B,z,Q,m,a,b,e,unitLap,window,L,σ,hp,hq,hr,hs,hg,hh,hj,hm,hsmall,
    hga,hgb,hge,hsum,hQ,hlo,hhi,hmid,hchart,hlabels,hclose,hz,hrepr⟩ := hAt
  have ht := (capture_opening c g h j p q r hq hr hg hh hj m a b e 2 (L 2) Q hlo hhi).2.2
  have hroles := forward_roles before after _ _ hlabels (chart_sector before _ _ hchart) hclose.1
    (by dsimp [packetTheta]; linarith only [ht])
  exact ⟨p,q,r,before,after,Fresh.FourBlockOuterTailClear.partitions p q r hp hq hr hs,hroles,hsave⟩

#print axioms forcedOutside_into_leftCharts
#print axioms forcedOutside_isolation
#print axioms finite_forward_roles
end Fresh.FourBlockForcedOutsideArrangement
