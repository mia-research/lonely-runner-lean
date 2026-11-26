import Fresh.FourBlockOuterTailRoles

/-! All eight subjects for the four native long-tail partitions.
The preceding singleton-prefix family embeds into this common family. -/
namespace Fresh.FourBlockOuterTailArrangement
open Fresh Fresh.OneMover Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockOuterLapPhase Fresh.FourBlockOuterTailClear

theorem all_subjects (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j) (m a b e rho : ℤ) (L : Fin 3 → ℤ)
    (hm : 1 ≤ m) (hsmall : g+h+j ≤ 3)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hlo : 11*(g+h+j)+16*remainder g h j m a b e ≤ 16*(rho : ℝ)-42)
    (hhi : 8*(rho : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hleft : LeftBands c g h j p q r m a b e rho L)
    (k : Fin 8) : Isolation (speeds c g h j p q r) k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  by_cases hk0 : k=0
  · subst k
    have hc := outer_clear c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e rho L hlo hhi hleft
    have htime := (opening_bounds g h j hgpos hhpos hjpos m a b e rho hlo hhi).1
    exact ⟨outerLapOpening g h j m a b e rho,by linarith,(isolatedAt_iff _ _ _).2 hc⟩
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
def OuterTailClassAt (V : Fin 8 → ℝ) (p q r : ℕ) (rho : ℤ) (L : Fin 3 → ℤ) : Prop :=
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
    LeftBands c g h j p q r m a b e rho L ∧ z≠0 ∧
    V=(fun i=>B+z*speeds c g h j p q r (σ i))

-- STANDING: DEFINITION
def OuterTailClass (V : Fin 8 → ℝ) : Prop :=
  ∃ (p q r : ℕ) (rho : ℤ) (L : Fin 3 → ℤ), OuterTailClassAt V p q r rho L

theorem outerTailClass_isolation {V : Fin 8 → ℝ} (hV : OuterTailClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨p,q,r,rho,L,hAt⟩ := hV
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,σ,hp,hq,hr,hs,hgpos,hhpos,hjpos,hm,hsmall,
    hg,hh,hj,hsum,hlo,hhi,hleft,hz,hrepr⟩ := hAt
  have hi := all_subjects c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e rho L
    hm hsmall hg hh hj hsum hlo hhi hleft (σ k)
  rw [hrepr]
  exact (Fresh.isolation_comp_perm _ σ k).2 (subject_isolation_affine B z hz hi)

theorem finite_normal_form {V : Fin 8 → ℝ} (hV : OuterTailClass V) :
    ∃ (p q r : ℕ) (rho : ℤ) (L : Fin 3 → ℤ),
      ((p=1 ∧ q=1 ∧ r=1) ∨ (p=2 ∧ q=1 ∧ r=1) ∨
        (p=1 ∧ q=2 ∧ r=1) ∨ (p=1 ∧ q=1 ∧ r=2)) ∧
      (rho=4 ∨ rho=5 ∨ rho=6) ∧
      0 ≤ L 0 ∧ L 0 ≤ L 1 ∧ L 1 ≤ L 2 ∧ L 2 ≤ 3 ∧ OuterTailClassAt V p q r rho L := by
  obtain ⟨p,q,r,rho,L,hAt⟩ := hV
  have hsave := hAt
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,σ,hp,hq,hr,hs,hgpos,hhpos,hjpos,hm,hsmall,
    hg,hh,hj,hsum,hlo,hhi,hleft,hz,hrepr⟩ := hAt
  obtain ⟨hl0,hl01,hl12,hl2⟩ := Fresh.FourBlockOuterTailRoles.left_roles c g h j p q r hp hq hr hs
    hgpos hhpos hjpos m a b e rho L hsmall hg hh hj hsum hlo hhi hleft
  exact ⟨p,q,r,rho,L,partitions p q r hp hq hr hs,
    Fresh.FourBlockOuterLapRoles.return_role g h j hgpos hhpos hjpos m a b e rho
      hsmall hg hh hj hsum hlo hhi,hl0,hl01,hl12,hl2,hsave⟩

theorem outerLap_into_outerTail {V : Fin 8 → ℝ}
    (hV : Fresh.FourBlockOuterLapArrangement.OuterLapClass V) : OuterTailClass V := by
  obtain ⟨rho,ell,kappa,hAt⟩ := hV
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,σ,hgpos,hhpos,hjpos,hsmall,hm,
    hg,hh,hj,hsum,hlo,hhi,hslo,hshi,hclo,hchi,hcap,hz,hrepr⟩ := hAt
  let L : Fin 3 → ℤ := ![ell,kappa,rho-4]
  have hleft : LeftBands c g h j 1 1 1 m a b e rho L := by
    have hf2 := Fresh.FourBlockOuterLapClear.cut_phase c g h j hgpos hhpos hjpos m a b e rho
    have hf3 := Fresh.FourBlockOuterLapPhase.packet_phase c g h j hgpos hhpos hjpos m a b e rho (3 : Fin 8) (by norm_num)
    obtain ⟨hPlo,hPhi⟩ := opening_bounds g h j hgpos hhpos hjpos m a b e rho hlo hhi
    norm_num [speeds,wholeLap] at hf2 hf3
    intro i
    fin_cases i <;> norm_num [prefixIndex,L,speeds,wholeLap] <;> push_cast <;>
      constructor <;> nlinarith only [hf2,hf3,hPlo,hPhi,hslo,hshi,hclo,hchi]
  exact ⟨1,1,1,rho,L,hpos,hinj,c,g,h,j,B,z,m,a,b,e,σ,
    by norm_num,by norm_num,by norm_num,by norm_num,hgpos,hhpos,hjpos,hm,hsmall,
    hg,hh,hj,hsum,hlo,hhi,hleft,hz,hrepr⟩

-- STANDING: DEFINITION
def OuterTailCoveredClass (V : Fin 8 → ℝ) : Prop :=
  Fresh.FourBlockFiveReturnArrangement.FiveReturnCoveredClass V ∨ OuterTailClass V

theorem outerTailCovered_isolation {V : Fin 8 → ℝ} (hV : OuterTailCoveredClass V)
    (k : Fin 8) : Isolation V k := by
  rcases hV with hV|hV
  · exact Fresh.FourBlockFiveReturnArrangement.fiveReturnCovered_isolation hV k
  · exact outerTailClass_isolation hV k

theorem outerLapCovered_into_outerTailCovered {V : Fin 8 → ℝ}
    (hV : Fresh.FourBlockOuterLapArrangement.OuterLapCoveredClass V) : OuterTailCoveredClass V := by
  rcases hV with hold|hnew
  · exact Or.inl hold
  · exact Or.inr (outerLap_into_outerTail hnew)

#print axioms outerLapCovered_into_outerTailCovered
#print axioms all_subjects
#print axioms outerTailClass_isolation
#print axioms finite_normal_form
#print axioms outerLap_into_outerTail
#print axioms outerTailCovered_isolation
end Fresh.FourBlockOuterTailArrangement
