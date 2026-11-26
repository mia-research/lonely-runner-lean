import Fresh.FourBlockOuterLapRoles

/-! All eight physical subjects for the native outer return with retained integer cut labels.
Earlier classes remain in the enclosing union, with affine and label transport. -/
namespace Fresh.FourBlockOuterLapArrangement
open Fresh Fresh.OneMover Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailPhase Fresh.FourBlockOuterLapPhase Fresh.FourBlockOuterLapClear

theorem all_subjects (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e r ell kappa : ℤ) (hm : 1 ≤ m) (hsmall : g+h+j ≤ 3)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hlo : 11*(g+h+j)+16*remainder g h j m a b e ≤ 16*(r : ℝ)-42)
    (hhi : 8*(r : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hslo : (ell : ℝ)+1/8 ≤ g*outerLapOpening g h j m a b e r-(a : ℝ))
    (hshi : g*outerLapOpening g h j m a b e r-(a : ℝ) ≤ (ell : ℝ)+7/8)
    (hclo : (r : ℝ)-(kappa : ℝ)-3/4 ≤ j*outerLapOpening g h j m a b e r-(e : ℝ)+
      4*(outerLapOpening g h j m a b e r-(m : ℝ)))
    (hchi : j*outerLapOpening g h j m a b e r-(e : ℝ)+
      4*(outerLapOpening g h j m a b e r-(m : ℝ)) ≤ (r : ℝ)-(kappa : ℝ))
    (k : Fin 8) : Isolation (speeds c g h j 1 1 1) k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  by_cases hk0 : k=0
  · subst k
    refine ⟨outerLapOpening g h j m a b e r,?_,?_⟩
    · have hb := (opening_bounds g h j hgpos hhpos hjpos m a b e r hlo hhi).1
      linarith
    · exact (isolatedAt_iff _ _ _).2 (outer_clear c g h j hgpos hhpos hjpos m a b e r ell kappa hlo hhi hslo hshi hclo hchi)
  · by_cases hk7 : k=7
    · subst k
      exact ⟨1/8,by norm_num,FourBlockEndpoints.right_direct c g h j 1 1 1
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) hgpos hhpos hjpos hsmall (by norm_num)⟩
    · have hn0 := Fin.val_ne_of_ne hk0
      have hn7 := Fin.val_ne_of_ne hk7
      have hi := k.isLt
      refine ⟨(m : ℝ)+1/8,by linarith,?_⟩
      exact internal_at_reference c g h j 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        m a b e hg hh hj hsum k (by omega) (by omega)

-- STANDING: DEFINITION
def OuterLapClassAt (V : Fin 8 → ℝ) (r ell kappa : ℤ) : Prop :=
  (∀i,0 < V i) ∧ Function.Injective V ∧
  ∃(c g h j B z : ℝ)(m a b e : ℤ)(σ : Equiv.Perm (Fin 8)),
    0 < g ∧ 0 < h ∧ 0 < j ∧ g+h+j ≤ 3 ∧ 1 ≤ m ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j ∧
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4 ∧
    11*(g+h+j)+16*remainder g h j m a b e ≤ 16*(r : ℝ)-42 ∧
    8*(r : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e ∧
    (ell : ℝ)+1/8 ≤ g*outerLapOpening g h j m a b e r-(a : ℝ) ∧
    g*outerLapOpening g h j m a b e r-(a : ℝ) ≤ (ell : ℝ)+7/8 ∧
    (r : ℝ)-(kappa : ℝ)-3/4 ≤ j*outerLapOpening g h j m a b e r-(e : ℝ)+
      4*(outerLapOpening g h j m a b e r-(m : ℝ)) ∧
    j*outerLapOpening g h j m a b e r-(e : ℝ)+
      4*(outerLapOpening g h j m a b e r-(m : ℝ)) ≤ (r : ℝ)-(kappa : ℝ) ∧
    (7/8 : ℝ) < remainder g h j m a b e ∧ z≠0 ∧
    V=(fun i=>B+z*speeds c g h j 1 1 1 (σ i))

-- STANDING: DEFINITION
def OuterLapClass (V : Fin 8 → ℝ) : Prop :=
  ∃ r ell kappa : ℤ, OuterLapClassAt V r ell kappa

theorem outerLapClass_isolation {V : Fin 8 → ℝ} (hV : OuterLapClass V)
    (k : Fin 8) : Isolation V k := by
  obtain ⟨r,ell,kappa,hAt⟩ := hV
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,σ,hgpos,hhpos,hjpos,hsmall,hm,hg,hh,hj,hsum,hlo,hhi,hslo,hshi,hclo,hchi,hcap,hz,hV⟩ := hAt
  have hi := all_subjects c g h j hgpos hhpos hjpos m a b e r ell kappa hm hsmall hg hh hj hsum hlo hhi hslo hshi hclo hchi (σ k)
  rw [hV]
  exact (Fresh.isolation_comp_perm _ σ k).2 (subject_isolation_affine B z hz hi)

theorem finite_normal_form {V : Fin 8 → ℝ} (hV : OuterLapClass V) :
    ∃ r ell kappa : ℤ, (r=4 ∨ r=5 ∨ r=6) ∧
      0 ≤ ell ∧ ell ≤ kappa ∧ kappa ≤ 2 ∧ OuterLapClassAt V r ell kappa := by
  obtain ⟨r,ell,kappa,hAt⟩ := hV
  have hsave := hAt
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,σ,hgpos,hhpos,hjpos,hsmall,hm,
    hg,hh,hj,hsum,hlo,hhi,hslo,hshi,hclo,hchi,hcap,hz,hrepr⟩ := hAt
  have hr := Fresh.FourBlockOuterLapRoles.return_role g h j hgpos hhpos hjpos m a b e r
    hsmall hg hh hj hsum hlo hhi
  obtain ⟨he,hek,hk⟩ := Fresh.FourBlockOuterLapRoles.cut_roles c g h j hgpos hhpos hjpos
    m a b e r ell kappa hsmall hg hh hj hsum hlo hhi hslo hshi hclo hchi
  exact ⟨r,ell,kappa,hr,he,hek,hk,hsave⟩

-- STANDING: DEFINITION
def OuterLapCoveredClass (V : Fin 8 → ℝ) : Prop :=
  Fresh.FourBlockFiveReturnArrangement.FiveReturnCoveredClass V ∨ OuterLapClass V

theorem outerLapCovered_isolation {V : Fin 8 → ℝ} (hV : OuterLapCoveredClass V)
    (k : Fin 8) : Isolation V k := by
  rcases hV with hV|hV
  · exact Fresh.FourBlockFiveReturnArrangement.fiveReturnCovered_isolation hV k
  · exact outerLapClass_isolation hV k

#print axioms finite_normal_form
#print axioms all_subjects
#print axioms outerLapClass_isolation
#print axioms outerLapCovered_isolation
end Fresh.FourBlockOuterLapArrangement
