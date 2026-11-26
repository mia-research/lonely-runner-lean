import Fresh.FourBlockEndpoints

/-! All subjects of every positive four-block size partition. Internal native
bands are independent of the original gap sum. Endpoint use retains the
explicit original totalgap and singleton guards. -/
namespace Fresh.FourBlockArrangement
open Fresh Fresh.OneMover Fresh.FourBlockNeighbour Fresh.FourBlockEndpoints

theorem all_subjects (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 7)
    (hgpos : 0<g) (hhpos : 0<h) (hjpos : 0<j) (hsmall : g+h+j ≤ 3)
    (hleft : p=1 → 1 ≤ g) (hright : p+q+r=7 → 1 ≤ j)
    (m a b e : ℤ) (hm : 1 ≤ m)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (k : Fin 8) : Isolation (speeds c g h j p q r) k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  by_cases hk0 : k=0
  · subst k
    exact ⟨1/8,by norm_num,left_direct c g h j p q r hp hq hr hs hgpos hhpos hjpos hsmall hleft⟩
  · by_cases hk7 : k=7
    · subst k
      exact ⟨1/8,by norm_num,right_direct c g h j p q r hp hq hr hs hgpos hhpos hjpos hsmall hright⟩
    · have hn0 := Fin.val_ne_of_ne hk0
      have hn7 := Fin.val_ne_of_ne hk7
      have hi := k.isLt
      exact ⟨(m : ℝ)+1/8,by linarith,
        internal_at_reference c g h j p q r hp hq hr hs m a b e hg hh hj hsum k (by simpa using (show 1 ≤ (k : ℕ) by omega)) (by simpa using (show (k : ℕ) ≤ 6 by omega))⟩

-- STANDING: DEFINITION
def FourBlockClass (V : Fin 8 → ℝ) : Prop :=
  (∀i,0<V i) ∧ Function.Injective V ∧
  ∃(c g h j B z : ℝ)(p q r : ℕ)(m a b e : ℤ)(σ : Equiv.Perm (Fin 8)),
    1 ≤ p ∧ 1 ≤ q ∧ 1 ≤ r ∧ p+q+r ≤ 7 ∧
    0<g ∧ 0<h ∧ 0<j ∧ g+h+j ≤ 3 ∧
    (p=1 → 1 ≤ g) ∧ (p+q+r=7 → 1 ≤ j) ∧ 1 ≤ m ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j ∧
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4 ∧ z≠0 ∧
    V=(fun i=>B+z*speeds c g h j p q r (σ i))

theorem fourBlock_isolation {V : Fin 8 → ℝ} (hV : FourBlockClass V)
    (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,h,j,B,z,p,q,r,m,a,b,e,σ,hp,hq,hr,hs,hgpos,hhpos,hjpos,hsmall,hleft,hright,hm,hg,hh,hj,hsum,hz,hV⟩ := hV
  have hi := all_subjects c g h j p q r hp hq hr hs hgpos hhpos hjpos hsmall hleft hright m a b e hm hg hh hj hsum (σ k)
  rw [hV]
  exact (Fresh.isolation_comp_perm _ σ k).2 (subject_isolation_affine B z hz hi)

#print axioms all_subjects
#print axioms fourBlock_isolation
end Fresh.FourBlockArrangement
