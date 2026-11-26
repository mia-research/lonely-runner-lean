import Fresh.FourBlockFourReturnExit
import Fresh.FourBlockInnerArrangement

/-! All eight physical subjects for the original runner4 return opening.
Earlier classes remain in the enclosing union, with affine and label transport. -/
namespace Fresh.FourBlockFourReturnArrangement
open Fresh Fresh.OneMover Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailPhase Fresh.FourBlockFourReturnExit

theorem all_subjects (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ) (hm : 1 ≤ m) (hsmall : g+h+j ≤ 3)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hlo : 3*(g+h+j)+8*remainder g h j m a b e ≤ 17)
    (hhi : 49 ≤ 11*(g+h+j)+24*remainder g h j m a b e)
    (hcut : j*fourOpening g h j m a b e-(e : ℝ)+(fourOpening g h j m a b e-(m : ℝ)) ≤ 1)
    (hsingle : g*fourOpening g h j m a b e-(a : ℝ) ≤ 7/8 ∨
      (9/8 : ℝ) ≤ g*fourOpening g h j m a b e-(a : ℝ))
    (k : Fin 8) : Isolation (speeds c g h j 1 1 1) k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  by_cases hk0 : k=0
  · subst k
    refine ⟨fourOpening g h j m a b e,?_,?_⟩
    · have hb := (four_bounds g h j hgpos hhpos hjpos m a b e hlo hhi).1
      linarith
    · exact (isolatedAt_iff _ _ _).2 (four_clear c g h j hgpos hhpos hjpos m a b e hg hh hj hlo hhi hcut hsingle)
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
def FourReturnClass (V : Fin 8 → ℝ) : Prop :=
  (∀i,0 < V i) ∧ Function.Injective V ∧
  ∃(c g h j B z : ℝ)(m a b e : ℤ)(σ : Equiv.Perm (Fin 8)),
    0 < g ∧ 0 < h ∧ 0 < j ∧ g+h+j ≤ 3 ∧ 1 ≤ m ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j ∧
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4 ∧
    3*(g+h+j)+8*remainder g h j m a b e ≤ 17 ∧
    49 ≤ 11*(g+h+j)+24*remainder g h j m a b e ∧
    j*fourOpening g h j m a b e-(e : ℝ)+(fourOpening g h j m a b e-(m : ℝ)) ≤ 1 ∧
    (g*fourOpening g h j m a b e-(a : ℝ) ≤ 7/8 ∨
      (9/8 : ℝ) ≤ g*fourOpening g h j m a b e-(a : ℝ)) ∧
    (7/8 : ℝ) < remainder g h j m a b e ∧ z≠0 ∧
    V=(fun i=>B+z*speeds c g h j 1 1 1 (σ i))

theorem fourReturnClass_isolation {V : Fin 8 → ℝ} (hV : FourReturnClass V)
    (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,σ,hgpos,hhpos,hjpos,hsmall,hm,hg,hh,hj,hsum,hlo,hhi,hcut,hsingle,hcap,hz,hV⟩ := hV
  have hi := all_subjects c g h j hgpos hhpos hjpos m a b e hm hsmall hg hh hj hsum hlo hhi hcut hsingle (σ k)
  rw [hV]
  exact (Fresh.isolation_comp_perm _ σ k).2 (subject_isolation_affine B z hz hi)

-- STANDING: DEFINITION
def FourReturnCoveredClass (V : Fin 8 → ℝ) : Prop :=
  Fresh.FourBlockInnerArrangement.InnerCoveredClass V ∨ FourReturnClass V

theorem fourReturnCovered_isolation {V : Fin 8 → ℝ} (hV : FourReturnCoveredClass V)
    (k : Fin 8) : Isolation V k := by
  rcases hV with hV|hV
  · exact Fresh.FourBlockInnerArrangement.innerCovered_isolation hV k
  · exact fourReturnClass_isolation hV k

#print axioms all_subjects
#print axioms fourReturnClass_isolation
#print axioms fourReturnCovered_isolation
end Fresh.FourBlockFourReturnArrangement
