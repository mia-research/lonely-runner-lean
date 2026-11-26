import Fresh.FourBlockLeftExitArrangement

/-! The final original left opening may follow earlier moves while the AP
packet stays clear. All physical subjects and finite discrete roles remain. -/
namespace Fresh.FourBlockLeftOpeningArrangement
open Fresh Fresh.OneMover Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockOuterLapPhase Fresh.FourBlockOuterTailClear
  Fresh.FourBlockOuterPacketRetention Fresh.FourBlockLeftOpening Fresh.FourBlockLeftExit

-- STANDING: DEFINITION
def OpeningBands (c g h j : ℝ) (p q r : ℕ) (m a b e rho : ℤ) (u : Fin 3) (L : Fin 3 → ℤ) : Prop :=
  outerLapOpening g h j m a b e rho ≤ leftOpening c g h j p q r m a b e u (L u) ∧
  (4+g+h+j)*(leftOpening c g h j p q r m a b e u (L u)-outerLapOpening g h j m a b e rho) ≤ 3/4 ∧
  (4+g+h+j)*(leftOpening c g h j p q r m a b e u (L u)-outerLapOpening g h j m a b e rho)+
    3*(1-(leftOpening c g h j p q r m a b e u (L u)-(m : ℝ))) ≤ 3/4 ∧
  OtherLeftBandsAt c g h j p q r m a b e (leftOpening c g h j p q r m a b e u (L u)) L u

theorem all_subjects (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j) (m a b e rho : ℤ) (u : Fin 3) (L : Fin 3 → ℤ)
    (hm : 1 ≤ m) (hsmall : g+h+j ≤ 3)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hlo : 11*(g+h+j)+16*remainder g h j m a b e ≤ 16*(rho : ℝ)-42)
    (hhi : 8*(rho : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hexit : OpeningBands c g h j p q r m a b e rho u L)
    (k : Fin 8) : Isolation (speeds c g h j p q r) k := by
  obtain ⟨hQP,houter,hinner,hother⟩ := hexit
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  by_cases hk0 : k=0
  · subst k
    have hb := bands_at_opening c g h j p q r hq hr hgpos hhpos hjpos m a b e u L hother
    have hc := displaced_clear c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e rho
      (leftOpening c g h j p q r m a b e u (L u)) L hlo hhi hQP houter hinner hb
    have htime := (opening_bounds g h j hgpos hhpos hjpos m a b e rho hlo hhi).1
    exact ⟨leftOpening c g h j p q r m a b e u (L u),by linarith,(isolatedAt_iff _ _ _).2 hc⟩
  · by_cases hk7 : k=7
    · subst k
      exact ⟨1/8,by norm_num,FourBlockEndpoints.right_direct c g h j p q r hp hq hr (by omega)
        hgpos hhpos hjpos hsmall (by intro hbad; omega)⟩
    · have hn0 := Fin.val_ne_of_ne hk0
      have hn7 := Fin.val_ne_of_ne hk7
      have hi := k.isLt
      exact ⟨(m : ℝ)+1/8,by linarith,
        internal_at_reference c g h j p q r hp hq hr (by omega) m a b e hg hh hj hsum k (by omega) (by omega)⟩

-- STANDING: DEFINITION
def LeftOpeningClassAt (V : Fin 8 → ℝ) (p q r : ℕ) (rho : ℤ) (u : Fin 3) (L : Fin 3 → ℤ) : Prop :=
  (∀ i,0 < V i) ∧ Function.Injective V ∧
  ∃ (c g h j B z : ℝ) (m a b e : ℤ) (σ : Equiv.Perm (Fin 8)),
    1 ≤ p ∧ 1 ≤ q ∧ 1 ≤ r ∧ p+q+r ≤ 4 ∧
    0 < g ∧ 0 < h ∧ 0 < j ∧ 1 ≤ m ∧ g+h+j ≤ 3 ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j ∧
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4 ∧
    11*(g+h+j)+16*remainder g h j m a b e ≤ 16*(rho : ℝ)-42 ∧
    8*(rho : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e ∧
    OpeningBands c g h j p q r m a b e rho u L ∧ z≠0 ∧
    V=(fun i=>B+z*speeds c g h j p q r (σ i))

-- STANDING: DEFINITION
def LeftOpeningClass (V : Fin 8 → ℝ) : Prop :=
  ∃ (p q r : ℕ) (rho : ℤ) (u : Fin 3) (L : Fin 3 → ℤ), LeftOpeningClassAt V p q r rho u L

theorem leftOpeningClass_isolation {V : Fin 8 → ℝ} (hV : LeftOpeningClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨p,q,r,rho,u,L,hAt⟩ := hV
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,σ,hp,hq,hr,hs,hgpos,hhpos,hjpos,hm,hsmall,
    hg,hh,hj,hsum,hlo,hhi,hexit,hz,hrepr⟩ := hAt
  have hi := all_subjects c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e rho u L
    hm hsmall hg hh hj hsum hlo hhi hexit (σ k)
  rw [hrepr]
  exact (Fresh.isolation_comp_perm _ σ k).2 (subject_isolation_affine B z hz hi)

theorem finite_normal_form {V : Fin 8 → ℝ} (hV : LeftOpeningClass V) :
    ∃ (p q r : ℕ) (rho : ℤ) (u : Fin 3) (L : Fin 3 → ℤ),
      ((p=1 ∧ q=1 ∧ r=1) ∨ (p=2 ∧ q=1 ∧ r=1) ∨
        (p=1 ∧ q=2 ∧ r=1) ∨ (p=1 ∧ q=1 ∧ r=2)) ∧
      (rho=4 ∨ rho=5 ∨ rho=6) ∧
      0 ≤ L 0 ∧ L 0 ≤ L 1 ∧ L 1 ≤ L 2 ∧ L 2 ≤ 4 ∧ LeftOpeningClassAt V p q r rho u L := by
  obtain ⟨p,q,r,rho,u,L,hAt⟩ := hV
  have hsave := hAt
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,σ,hp,hq,hr,hs,hgpos,hhpos,hjpos,hm,hsmall,
    hg,hh,hj,hsum,hlo,hhi,hexit,hz,hrepr⟩ := hAt
  obtain ⟨hQP,houter,hinner,hother⟩ := hexit
  obtain ⟨hPlo,hPhi⟩ := displaced_time_bounds g h j hgpos hhpos hjpos m a b e rho
    (leftOpening c g h j p q r m a b e u (L u)) hlo hhi hQP houter
  have hleft := bands_at_opening c g h j p q r hq hr hgpos hhpos hjpos m a b e u L hother
  obtain ⟨hl0,hl01,hl12,hl2⟩ := Fresh.FourBlockDisplacedLeftRoles.left_roles_at_time c g h j p q r hp hq hr hs
    hgpos hhpos hjpos m a b e (leftOpening c g h j p q r m a b e u (L u)) L hsmall
    hg hh hj hsum (by linarith) hPhi hleft
  exact ⟨p,q,r,rho,u,L,partitions p q r hp hq hr hs,
    Fresh.FourBlockOuterLapRoles.return_role g h j hgpos hhpos hjpos m a b e rho
      hsmall hg hh hj hsum hlo hhi,hl0,hl01,hl12,hl2,hsave⟩

theorem leftExit_into_leftOpening {V : Fin 8 → ℝ}
    (hV : Fresh.FourBlockLeftExitArrangement.LeftExitClass V) : LeftOpeningClass V := by
  obtain ⟨p,q,r,rho,u,L,hAt⟩ := hV
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,σ,hp,hq,hr,hs,hgpos,hhpos,hjpos,hm,hsmall,
    hg,hh,hj,hsum,hlo,hhi,hexit,hz,hrepr⟩ := hAt
  obtain ⟨hcaplo,hcaphi,houter,hinner,hother⟩ := hexit
  have ht := (capture_opening c g h j p q r hq hr hgpos hhpos hjpos m a b e u (L u)
    (outerLapOpening g h j m a b e rho) hcaplo hcaphi).2.2
  exact ⟨p,q,r,rho,u,L,hpos,hinj,c,g,h,j,B,z,m,a,b,e,σ,
    hp,hq,hr,hs,hgpos,hhpos,hjpos,hm,hsmall,hg,hh,hj,hsum,hlo,hhi,
    ⟨ht.le,houter,hinner,hother⟩,hz,hrepr⟩

-- STANDING: DEFINITION
def LeftOpeningCoveredClass (V : Fin 8 → ℝ) : Prop :=
  Fresh.FourBlockOuterTailArrangement.OuterTailCoveredClass V ∨ LeftOpeningClass V

theorem leftOpeningCovered_isolation {V : Fin 8 → ℝ} (hV : LeftOpeningCoveredClass V)
    (k : Fin 8) : Isolation V k := by
  rcases hV with hV|hV
  · exact Fresh.FourBlockOuterTailArrangement.outerTailCovered_isolation hV k
  · exact leftOpeningClass_isolation hV k

theorem leftExitCovered_into_leftOpeningCovered {V : Fin 8 → ℝ}
    (hV : Fresh.FourBlockLeftExitArrangement.LeftExitCoveredClass V) : LeftOpeningCoveredClass V := by
  rcases hV with hold|hnew
  · exact Or.inl hold
  · exact Or.inr (leftExit_into_leftOpening hnew)

#print axioms leftExit_into_leftOpening
#print axioms leftExitCovered_into_leftOpeningCovered
#print axioms all_subjects
#print axioms leftOpeningClass_isolation
#print axioms finite_normal_form
#print axioms leftOpeningCovered_isolation
end Fresh.FourBlockLeftOpeningArrangement
