import Fresh.FourBlockFourthExit
import Fresh.FourBlockLongTailArrangement

/-! A second all-subject packet-exit family. Native faces are derived from
the returned endpoint and its still-clear partner. The class retains the
strict complement of the earlier third-opening exit, avoiding that repeat.
Positive moving speeds, exact lap labels and signed affine transport remain. -/
namespace Fresh.FourBlockFourthArrangement
open Fresh Fresh.OneMover Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailBounds Fresh.FourBlockLongTailPhase
  Fresh.FourBlockFourthExit

theorem all_subjects (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ) (hm : 1 ≤ m)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hlo : 5*(g+h+j)+24*remainder g h j m a b e ≤ 31)
    (hhi : 5 ≤ g+h+j+4*remainder g h j m a b e)
    (k : Fin 8) : Isolation (speeds c g h j 1 1 1) k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨hRlo,hRhi⟩ := native_remainder_band g h j m a b e hg hh hj hsum
  by_cases hk0 : k=0
  · subst k
    refine ⟨packetOpening g h j m a b e 3,?_,?_⟩
    · have hb := (fourth_bounds g h j hgpos hhpos hjpos m a b e hlo hhi).1
      linarith
    · exact (isolatedAt_iff _ _ _).2 (fourth_clear c g h j hgpos hhpos hjpos m a b e hg hh hj hlo hhi)
  · by_cases hk7 : k=7
    · subst k
      have hsmall : g+h+j ≤ 3 := by linarith
      exact ⟨1/8,by norm_num,FourBlockEndpoints.right_direct c g h j 1 1 1
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) hgpos hhpos hjpos hsmall (by norm_num)⟩
    · have hn0 := Fin.val_ne_of_ne hk0
      have hn7 := Fin.val_ne_of_ne hk7
      have hi := k.isLt
      refine ⟨(m : ℝ)+1/8,by linarith,?_⟩
      exact internal_at_reference c g h j 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        m a b e hg hh hj hsum k (by omega) (by omega)

theorem native_fourth_episode (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hlo : 5*(g+h+j)+24*remainder g h j m a b e ≤ 31)
    (hhi : 5 ≤ g+h+j+4*remainder g h j m a b e)
    (hcontinue : 9 < g+h+j+8*remainder g h j m a b e) :
    let E := disparitySet (speeds c g h j 1 1 1) 0
    IsMove E ((m : ℝ)+1/8) (outerOpening g h j m a b e) ∧
    IsMove E (outerOpening g h j m a b e) (packetOpening g h j m a b e 1) ∧
    IsMove E (packetOpening g h j m a b e 1) (packetOpening g h j m a b e 2) ∧
    IsMove E (packetOpening g h j m a b e 2) (packetOpening g h j m a b e 3) ∧
    LonelyAt E (packetOpening g h j m a b e 3) := by
  dsimp only
  rcases Fresh.FourBlockLongTailEpisode.native_episode c g h j 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hgpos hhpos hjpos m a b e hg hh hj hsum with
    ⟨hedge,hclear⟩|⟨hcap,hfirst,hsecond,hthird,hexit,hcont⟩
  · exfalso
    linarith
  · exact ⟨hfirst,hsecond,hthird,hcont (not_le_of_gt hcontinue),
      fourth_clear c g h j hgpos hhpos hjpos m a b e hg hh hj hlo hhi⟩

-- STANDING: DEFINITION
def FourthClass (V : Fin 8 → ℝ) : Prop :=
  (∀i,0 < V i) ∧ Function.Injective V ∧
  ∃(c g h j B z : ℝ)(m a b e : ℤ)(σ : Equiv.Perm (Fin 8)),
    0 < g ∧ 0 < h ∧ 0 < j ∧ 1 ≤ m ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j ∧
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4 ∧
    5*(g+h+j)+24*remainder g h j m a b e ≤ 31 ∧
    5 ≤ g+h+j+4*remainder g h j m a b e ∧
    9 < g+h+j+8*remainder g h j m a b e ∧ z≠0 ∧
    V=(fun i=>B+z*speeds c g h j 1 1 1 (σ i))

theorem fourthClass_isolation {V : Fin 8 → ℝ} (hV : FourthClass V)
    (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,σ,hgpos,hhpos,hjpos,hm,hg,hh,hj,hsum,hlo,hhi,hcontinue,hz,hV⟩ := hV
  have hi := all_subjects c g h j hgpos hhpos hjpos m a b e hm hg hh hj hsum hlo hhi (σ k)
  rw [hV]
  exact (Fresh.isolation_comp_perm _ σ k).2 (subject_isolation_affine B z hz hi)

-- STANDING: DEFINITION
def PacketCoveredClass (V : Fin 8 → ℝ) : Prop :=
  Fresh.FourBlockLongTailArrangement.FourBlockCoveredClass V ∨ FourthClass V

theorem packetCovered_isolation {V : Fin 8 → ℝ} (hV : PacketCoveredClass V)
    (k : Fin 8) : Isolation V k := by
  rcases hV with hV|hV
  · exact Fresh.FourBlockLongTailArrangement.fourBlockCovered_isolation hV k
  · exact fourthClass_isolation hV k

#print axioms all_subjects
#print axioms native_fourth_episode
#print axioms fourthClass_isolation
#print axioms packetCovered_isolation
end Fresh.FourBlockFourthArrangement
