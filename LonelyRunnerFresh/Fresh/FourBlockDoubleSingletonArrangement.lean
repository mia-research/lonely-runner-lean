import Fresh.FourBlockDoubleSingleton

/-! Two singleton endpoints have independent supplied original openings.
All six internal subjects retain the existing native reference event. -/
namespace Fresh.FourBlockDoubleSingletonArrangement
open Fresh Fresh.OneMover Fresh.FourBlockNeighbour Fresh.FourBlockDoubleSingleton

noncomputable def EndpointData (c g h j : ℝ) (q r : ℕ) (m a d e : ℤ) (right : Bool) : Prop :=
  ∃ (b : Fin 6) (u : Fin 7) (role : Fin 6) (rho unitLap window : ℤ) (L : Fin 8 → ℤ),
    Host q r b ∧ 0 < opening c g h j q r right m a d e rho u ∧
    PacketBands c g h j q r b right m a d e unitLap window role (opening c g h j q r right m a d e rho u) ∧
    RemainingBands c g h j q r b right m a d e (opening c g h j q r right m a d e rho u) L u

theorem endpoint_isolation (c g h j : ℝ) (q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a d e : ℤ) (right : Bool)
    (hd : EndpointData c g h j q r m a d e right) : Isolation (speeds c g h j 1 q r) (endpoint right) := by
  obtain ⟨b,u,role,rho,unitLap,window,L,hhost,hP,hc,hb⟩ := hd
  exact ⟨opening c g h j q r right m a d e rho u,hP,
    endpoint_clear c g h j q r b hq hr hhost hg hh hj right m a d e rho unitLap window u role L hc hb⟩

theorem all_subjects (c g h j : ℝ) (q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : q+r=6)
    (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j) (m a d e : ℤ) (hm : 1 ≤ m)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(d : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(d : ℝ)+(e : ℝ))+4)
    (hd : ∀ right : Bool, EndpointData c g h j q r m a d e right)
    (k : Fin 8) : Isolation (speeds c g h j 1 q r) k := by
  by_cases hk0 : k=0
  · subst k
    exact endpoint_isolation c g h j q r hq hr hgpos hhpos hjpos m a d e false (hd false)
  · by_cases hk7 : k=7
    · subst k
      exact endpoint_isolation c g h j q r hq hr hgpos hhpos hjpos m a d e true (hd true)
    · have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hn0 := Fin.val_ne_of_ne hk0
      have hn7 := Fin.val_ne_of_ne hk7
      have hi := k.isLt
      exact ⟨(m : ℝ)+1/8,by linarith,
        internal_at_reference c g h j 1 q r (by omega) hq hr (by omega) m a d e hg hh hj hsum k (by omega) (by omega)⟩

-- STANDING: DEFINITION
noncomputable def DoubleSingletonClassAt (V : Fin 8 → ℝ) (q r : ℕ) : Prop :=
  (∀ i,0 < V i) ∧ Function.Injective V ∧
  ∃ (c g h j B z : ℝ) (m a d e : ℤ) (σ : Equiv.Perm (Fin 8)),
    1 ≤ q ∧ 1 ≤ r ∧ q+r=6 ∧ 0 < g ∧ 0 < h ∧ 0 < j ∧ 1 ≤ m ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(d : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j ∧
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(d : ℝ)+(e : ℝ))+4 ∧
    (∀ right : Bool, EndpointData c g h j q r m a d e right) ∧ z≠0 ∧
    V=(fun i=>B+z*speeds c g h j 1 q r (σ i))

-- STANDING: DEFINITION
noncomputable def DoubleSingletonClass (V : Fin 8 → ℝ) : Prop :=
  ∃ q r : ℕ, DoubleSingletonClassAt V q r

theorem doubleSingleton_isolation {V : Fin 8 → ℝ} (hV : DoubleSingletonClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨q,r,hAt⟩ := hV
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,d,e,σ,hq,hr,hs,hg,hh,hj,hm,hga,hgd,hge,hsum,hd,hz,hrepr⟩ := hAt
  have hi := all_subjects c g h j q r hq hr hs hg hh hj m a d e hm hga hgd hge hsum hd (σ k)
  rw [hrepr]
  exact (Fresh.isolation_comp_perm _ σ k).2 (subject_isolation_affine B z hz hi)

theorem finite_normal_form {V : Fin 8 → ℝ} (hV : DoubleSingletonClass V) :
    ∃ q r : ℕ, ((q=1 ∧ r=5) ∨ (q=2 ∧ r=4) ∨ (q=3 ∧ r=3) ∨ (q=4 ∧ r=2) ∨ (q=5 ∧ r=1)) ∧
      DoubleSingletonClassAt V q r := by
  obtain ⟨q,r,hAt⟩ := hV
  have hsave := hAt
  obtain ⟨_,_,c,g,h,j,B,z,m,a,d,e,σ,hq,hr,hs,_⟩ := hAt
  exact ⟨q,r,by omega,hsave⟩

-- STANDING: DEFINITION
noncomputable def DoubleCoveredClass (V : Fin 8 → ℝ) : Prop :=
  Fresh.FourBlockMiddlePacketArrangement.MiddleCoveredClass V ∨ DoubleSingletonClass V

theorem doubleCovered_isolation {V : Fin 8 → ℝ} (hV : DoubleCoveredClass V) (k : Fin 8) : Isolation V k := by
  rcases hV with hold|hd
  · exact Fresh.FourBlockMiddlePacketArrangement.middleCovered_isolation hold k
  · exact doubleSingleton_isolation hd k

theorem middleCovered_into_doubleCovered {V : Fin 8 → ℝ}
    (hV : Fresh.FourBlockMiddlePacketArrangement.MiddleCoveredClass V) : DoubleCoveredClass V := Or.inl hV

#print axioms endpoint_isolation
#print axioms all_subjects
#print axioms doubleSingleton_isolation
#print axioms finite_normal_form
#print axioms doubleCovered_isolation
#print axioms middleCovered_into_doubleCovered
end Fresh.FourBlockDoubleSingletonArrangement
