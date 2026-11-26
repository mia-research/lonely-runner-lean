import Fresh.FourBlockShortTail
import Fresh.FourBlockForcedOutsideArrangement

/-! Six further physical four-block partitions, ending in a three-runner
AP packet. The original opening supplies its own outside boundary. -/
namespace Fresh.FourBlockShortTailArrangement
open Fresh Fresh.OneMover Fresh.FourBlockNeighbour Fresh.FourBlockShortTail

theorem all_subjects (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 5)
    (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j) (m a b e unitLap window : ℤ)
    (u : Fin 4) (L : Fin 4 → ℤ) (role : Fin 6) (hm : 1 ≤ m) (hsmall : g+h+j ≤ 3)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hP : 0 < cutOpening c g h j p q r m a b e u (L u))
    (hf : PacketBands c g h j p q r m a b e unitLap window role (cutOpening c g h j p q r m a b e u (L u)))
    (hl : OtherCutBands c g h j p q r m a b e (cutOpening c g h j p q r m a b e u (L u)) L u)
    (k : Fin 8) : Isolation (speeds c g h j p q r) k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  by_cases hk0 : k=0
  · subst k
    exact ⟨cutOpening c g h j p q r m a b e u (L u),hP,(Fresh.Localisation.isolatedAt_iff _ _ _).2
      (cut_clear c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e unitLap window role u L hf hl)⟩
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
def ShortTailClassAt (V : Fin 8 → ℝ) (p q r : ℕ) (u : Fin 4) (role : Fin 6) : Prop :=
  (∀ i,0 < V i) ∧ Function.Injective V ∧
  ∃ (c g h j B z : ℝ) (m a b e unitLap window : ℤ)
    (L : Fin 4 → ℤ) (σ : Equiv.Perm (Fin 8)),
    1 ≤ p ∧ 1 ≤ q ∧ 1 ≤ r ∧ p+q+r = 5 ∧
    0 < g ∧ 0 < h ∧ 0 < j ∧ 1 ≤ m ∧ g+h+j ≤ 3 ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j ∧
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4 ∧
    0 < cutOpening c g h j p q r m a b e u (L u) ∧
    PacketBands c g h j p q r m a b e unitLap window role (cutOpening c g h j p q r m a b e u (L u)) ∧
    OtherCutBands c g h j p q r m a b e (cutOpening c g h j p q r m a b e u (L u)) L u ∧ z≠0 ∧
    V=(fun i=>B+z*speeds c g h j p q r (σ i))

-- STANDING: DEFINITION
def ShortTailClass (V : Fin 8 → ℝ) : Prop :=
  ∃ (p q r : ℕ) (u : Fin 4) (role : Fin 6), ShortTailClassAt V p q r u role

theorem shortTailClass_isolation {V : Fin 8 → ℝ} (hV : ShortTailClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨p,q,r,u,role,hAt⟩ := hV
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,unitLap,window,L,σ,hp,hq,hr,hs,hgpos,hhpos,hjpos,hm,hsmall,
    hg,hh,hj,hsum,hP,hf,hl,hz,hrepr⟩ := hAt
  have hi := all_subjects c g h j p q r hp hq hr (by omega) hgpos hhpos hjpos m a b e unitLap window u L role
    hm hsmall hg hh hj hsum hP hf hl (σ k)
  rw [hrepr]
  exact (Fresh.isolation_comp_perm _ σ k).2 (subject_isolation_affine B z hz hi)

theorem finite_normal_form {V : Fin 8 → ℝ} (hV : ShortTailClass V) :
    ∃ (p q r : ℕ) (u : Fin 4) (role : Fin 6),
      ((p=3 ∧ q=1 ∧ r=1) ∨ (p=1 ∧ q=3 ∧ r=1) ∨ (p=1 ∧ q=1 ∧ r=3) ∨
        (p=2 ∧ q=2 ∧ r=1) ∨ (p=2 ∧ q=1 ∧ r=2) ∨ (p=1 ∧ q=2 ∧ r=2)) ∧ ShortTailClassAt V p q r u role := by
  obtain ⟨p,q,r,u,role,hAt⟩ := hV
  have hsave := hAt
  obtain ⟨_,_,c,g,h,j,B,z,m,a,b,e,unitLap,window,L,σ,hp,hq,hr,hs,_⟩ := hAt
  exact ⟨p,q,r,u,role,by omega,hsave⟩

-- STANDING: DEFINITION
def ShortTailCoveredClass (V : Fin 8 → ℝ) : Prop :=
  Fresh.FourBlockLeftPacketChartsArrangement.ChartsCoveredClass V ∨ ShortTailClass V

theorem shortTailCovered_isolation {V : Fin 8 → ℝ} (hV : ShortTailCoveredClass V) (k : Fin 8) : Isolation V k := by
  rcases hV with hold|hs
  · exact Fresh.FourBlockLeftPacketChartsArrangement.chartsCovered_isolation hold k
  · exact shortTailClass_isolation hs k

theorem chartsCovered_into_shortTailCovered {V : Fin 8 → ℝ}
    (hV : Fresh.FourBlockLeftPacketChartsArrangement.ChartsCoveredClass V) : ShortTailCoveredClass V := by
  exact Or.inl hV

#print axioms all_subjects
#print axioms shortTailClass_isolation
#print axioms finite_normal_form
#print axioms shortTailCovered_isolation
#print axioms chartsCovered_into_shortTailCovered
end Fresh.FourBlockShortTailArrangement
