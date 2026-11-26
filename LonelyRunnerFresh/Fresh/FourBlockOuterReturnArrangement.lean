import Fresh.FourBlockOuterReturnMove

/-! All-subject isolation after an actual nonmonotone outer-endpoint return.
The closed shared face is handled by the preceding fourth-opening family.
Each member retains all eight positive distinct physical speeds and all
seven original subject readings, with signed affine and relabel transport. -/
namespace Fresh.FourBlockOuterReturnArrangement
open Fresh Fresh.OneMover Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockLongTailBounds Fresh.FourBlockLongTailPhase
  Fresh.FourBlockOuterReturnBounds Fresh.FourBlockOuterReturnClear Fresh.FourBlockOuterReturnMove

theorem all_subjects (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ) (hm : 1 ≤ m)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hlo : 3*(g+h+j)+16*remainder g h j m a b e ≤ 22)
    (hhi : 31 ≤ 5*(g+h+j)+24*remainder g h j m a b e)
    (k : Fin 8) : Isolation (speeds c g h j 1 1 1) k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨hRlo,hRhi⟩ := native_remainder_band g h j m a b e hg hh hj hsum
  by_cases hk0 : k=0
  · subst k
    refine ⟨returnOpening g h j m a b e,?_,?_⟩
    · have hb := (return_bounds g h j hgpos hhpos hjpos m a b e hlo hhi).1
      linarith
    · exact (isolatedAt_iff _ _ _).2 (return_clear c g h j hgpos hhpos hjpos m a b e hg hh hj hlo hhi)
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

theorem native_return_episode (c g h j : ℝ) (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j)
    (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hlo : 3*(g+h+j)+16*remainder g h j m a b e ≤ 22)
    (hhi : 31 < 5*(g+h+j)+24*remainder g h j m a b e)
    (hcap : (7/8 : ℝ) < remainder g h j m a b e) :
    let E := disparitySet (speeds c g h j 1 1 1) 0
    IsMove E ((m : ℝ)+1/8) (outerOpening g h j m a b e) ∧
    IsMove E (outerOpening g h j m a b e) (packetOpening g h j m a b e 1) ∧
    IsMove E (packetOpening g h j m a b e 1) (packetOpening g h j m a b e 2) ∧
    IsMove E (packetOpening g h j m a b e 2) (packetOpening g h j m a b e 3) ∧
    IsMove E (packetOpening g h j m a b e 3) (returnOpening g h j m a b e) ∧
    LonelyAt E (returnOpening g h j m a b e) := by
  dsimp only
  obtain ⟨hRlo,hRhi⟩ := native_remainder_band g h j m a b e hg hh hj hsum
  have hcontinue : 9 < g+h+j+8*remainder g h j m a b e := by linarith
  rcases Fresh.FourBlockLongTailEpisode.native_episode c g h j 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hgpos hhpos hjpos m a b e hg hh hj hsum with
    ⟨hedge,hclear⟩|⟨hcap',hfirst,hsecond,hthird,hexit,hcont⟩
  · exfalso
    linarith
  · exact ⟨hfirst,hsecond,hthird,hcont (not_le_of_gt hcontinue),
      return_move c g h j hgpos hhpos hjpos m a b e hg hh hj hsum hlo hhi,
      return_clear c g h j hgpos hhpos hjpos m a b e hg hh hj hlo hhi.le⟩

-- STANDING: DEFINITION
def OuterReturnClass (V : Fin 8 → ℝ) : Prop :=
  (∀i,0 < V i) ∧ Function.Injective V ∧
  ∃(c g h j B z : ℝ)(m a b e : ℤ)(σ : Equiv.Perm (Fin 8)),
    0 < g ∧ 0 < h ∧ 0 < j ∧ 1 ≤ m ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j ∧
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4 ∧
    3*(g+h+j)+16*remainder g h j m a b e ≤ 22 ∧
    31 < 5*(g+h+j)+24*remainder g h j m a b e ∧
    (7/8 : ℝ) < remainder g h j m a b e ∧ z≠0 ∧
    V=(fun i=>B+z*speeds c g h j 1 1 1 (σ i))

theorem outerReturnClass_isolation {V : Fin 8 → ℝ} (hV : OuterReturnClass V)
    (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,σ,hgpos,hhpos,hjpos,hm,hg,hh,hj,hsum,hlo,hhi,hcap,hz,hV⟩ := hV
  have hi := all_subjects c g h j hgpos hhpos hjpos m a b e hm hg hh hj hsum hlo hhi.le (σ k)
  rw [hV]
  exact (Fresh.isolation_comp_perm _ σ k).2 (subject_isolation_affine B z hz hi)

-- STANDING: DEFINITION
def ReturnCoveredClass (V : Fin 8 → ℝ) : Prop :=
  Fresh.FourBlockFourthArrangement.PacketCoveredClass V ∨ OuterReturnClass V

theorem returnCovered_isolation {V : Fin 8 → ℝ} (hV : ReturnCoveredClass V)
    (k : Fin 8) : Isolation V k := by
  rcases hV with hV|hV
  · exact Fresh.FourBlockFourthArrangement.packetCovered_isolation hV k
  · exact outerReturnClass_isolation hV k

#print axioms all_subjects
#print axioms native_return_episode
#print axioms outerReturnClass_isolation
#print axioms returnCovered_isolation
end Fresh.FourBlockOuterReturnArrangement
