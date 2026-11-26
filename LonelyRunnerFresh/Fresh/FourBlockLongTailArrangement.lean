import Fresh.FourBlockLongTailEpisode

/-! All-subject arrangement family with a long opposite AP block and the
native closed packet-exit face. No left singleton-end guard is required.
The strict complement has a forced continuation in the imported episode. -/
namespace Fresh.FourBlockLongTailArrangement
open Fresh Fresh.OneMover Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailBounds Fresh.FourBlockLongTailPhase

theorem all_subjects (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j) (m a b e : ℤ) (hm : 1 ≤ m)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hface : g+h+j+8*remainder g h j m a b e ≤ 9)
    (k : Fin 8) : Isolation (speeds c g h j p q r) k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨hRlo,hRhi⟩ := native_remainder_band g h j m a b e hg hh hj hsum
  by_cases hk0 : k=0
  · subst k
    have hclear := (Fresh.FourBlockLongTailExit.exit_or_continue c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e hg hh hj hsum).1 hface
    have hpos := (second_partner_bounds g h j hgpos hhpos hjpos m a b e hRlo hRhi).1
    refine ⟨packetOpening g h j m a b e 2,by linarith,?_⟩
    exact (isolatedAt_iff _ _ _).2 hclear
  · by_cases hk7 : k=7
    · subst k
      have hsmall : g+h+j ≤ 3 := by linarith
      exact ⟨1/8,by norm_num,FourBlockEndpoints.right_direct c g h j p q r hp hq hr (by omega)
        hgpos hhpos hjpos hsmall (by intro hbad; omega)⟩
    · have hn0 := Fin.val_ne_of_ne hk0
      have hn7 := Fin.val_ne_of_ne hk7
      have hi := k.isLt
      refine ⟨(m : ℝ)+1/8,by linarith,?_⟩
      exact internal_at_reference c g h j p q r hp hq hr (by omega) m a b e hg hh hj hsum k (by omega) (by omega)

-- STANDING: DEFINITION
def LongTailClass (V : Fin 8 → ℝ) : Prop :=
  (∀i,0 < V i) ∧ Function.Injective V ∧
  ∃(c g h j B z : ℝ)(p q r : ℕ)(m a b e : ℤ)(σ : Equiv.Perm (Fin 8)),
    1 ≤ p ∧ 1 ≤ q ∧ 1 ≤ r ∧ p+q+r ≤ 4 ∧
    0 < g ∧ 0 < h ∧ 0 < j ∧ 1 ≤ m ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j ∧
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4 ∧
    g+h+j+8*remainder g h j m a b e ≤ 9 ∧ z≠0 ∧
    V=(fun i=>B+z*speeds c g h j p q r (σ i))

theorem longTail_isolation {V : Fin 8 → ℝ} (hV : LongTailClass V)
    (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,h,j,B,z,p,q,r,m,a,b,e,σ,hp,hq,hr,hs,hgpos,hhpos,hjpos,hm,hg,hh,hj,hsum,hface,hz,hV⟩ := hV
  have hi := all_subjects c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e hm hg hh hj hsum hface (σ k)
  rw [hV]
  exact (Fresh.isolation_comp_perm _ σ k).2 (subject_isolation_affine B z hz hi)

-- STANDING: DEFINITION
def FourBlockCoveredClass (V : Fin 8 → ℝ) : Prop :=
  Fresh.FourBlockArrangement.FourBlockClass V ∨ LongTailClass V

theorem fourBlockCovered_isolation {V : Fin 8 → ℝ} (hV : FourBlockCoveredClass V)
    (k : Fin 8) : Isolation V k := by
  rcases hV with hV|hV
  · exact Fresh.FourBlockArrangement.fourBlock_isolation hV k
  · exact longTail_isolation hV k

#print axioms all_subjects
#print axioms longTail_isolation
#print axioms fourBlockCovered_isolation
end Fresh.FourBlockLongTailArrangement
