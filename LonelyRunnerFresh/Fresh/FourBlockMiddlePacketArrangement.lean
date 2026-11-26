import Fresh.FourBlockMiddlePacket

/-! Native middle-packet families use the same six AP charts and original
opening roles, retaining explicit bands for the four outside readings. -/
namespace Fresh.FourBlockMiddlePacketArrangement
open Fresh Fresh.OneMover Fresh.FourBlockNeighbour Fresh.FourBlockShortOpening Fresh.FourBlockMiddlePacket

theorem all_subjects (c g h j : ℝ) (p q r : ℕ) (start : Fin 6)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hhost : MiddleHost p q r start)
    (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j) (m a b e rho unitLap window : ℤ)
    (u : Fin 7) (L : Fin 8 → ℤ) (role : Fin 6) (hm : 1 ≤ m) (hsmall : g+h+j ≤ 3)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hP : 0 < opening c g h j p q r m a b e rho u)
    (hf : PacketBands c g h j p q r start m a b e unitLap window role (opening c g h j p q r m a b e rho u))
    (hl : RemainingBands c g h j p q r start m a b e (opening c g h j p q r m a b e rho u) L u)
    (k : Fin 8) : Isolation (speeds c g h j p q r) k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs := hhost.1
  by_cases hk0 : k=0
  · subst k
    exact ⟨opening c g h j p q r m a b e rho u,hP,(Fresh.Localisation.isolatedAt_iff _ _ _).2
      (Fresh.FourBlockMiddlePacket.opening_clear c g h j p q r start hp hq hr hhost hgpos hhpos hjpos m a b e rho unitLap window u role L hf hl)⟩
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
def MiddlePacketClassAt (V : Fin 8 → ℝ) (p q r : ℕ) (start : Fin 6) (u : Fin 7) (role : Fin 6) : Prop :=
  (∀ i,0 < V i) ∧ Function.Injective V ∧
  ∃ (c g h j B z : ℝ) (m a b e rho unitLap window : ℤ)
    (L : Fin 8 → ℤ) (σ : Equiv.Perm (Fin 8)),
    1 ≤ p ∧ 1 ≤ q ∧ 1 ≤ r ∧ MiddleHost p q r start ∧
    0 < g ∧ 0 < h ∧ 0 < j ∧ 1 ≤ m ∧ g+h+j ≤ 3 ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j ∧
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4 ∧
    0 < opening c g h j p q r m a b e rho u ∧
    PacketBands c g h j p q r start m a b e unitLap window role (opening c g h j p q r m a b e rho u) ∧
    RemainingBands c g h j p q r start m a b e (opening c g h j p q r m a b e rho u) L u ∧ z≠0 ∧
    V=(fun i=>B+z*speeds c g h j p q r (σ i))

-- STANDING: DEFINITION
def MiddlePacketClass (V : Fin 8 → ℝ) : Prop :=
  ∃ (p q r : ℕ) (start : Fin 6) (u : Fin 7) (role : Fin 6), MiddlePacketClassAt V p q r start u role

theorem middlePacket_isolation {V : Fin 8 → ℝ} (hV : MiddlePacketClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨p,q,r,start,u,role,hAt⟩ := hV
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,rho,unitLap,window,L,σ,hp,hq,hr,hhost,hg,hh,hj,hm,hsmall,
    hga,hgb,hge,hsum,hP,hpacket,hcuts,hz,hrepr⟩ := hAt
  have hi := all_subjects c g h j p q r start hp hq hr hhost hg hh hj m a b e rho unitLap window u L role
    hm hsmall hga hgb hge hsum hP hpacket hcuts (σ k)
  rw [hrepr]
  exact (Fresh.isolation_comp_perm _ σ k).2 (subject_isolation_affine B z hz hi)

theorem finite_normal_form {V : Fin 8 → ℝ} (hV : MiddlePacketClass V) :
    ∃ (p q r : ℕ) (start : Fin 6) (u : Fin 7) (role : Fin 6),
      ((p=1 ∧ q=4 ∧ r=1 ∧ start.val=1) ∨ (p=1 ∧ q=3 ∧ r=2 ∧ start.val=1) ∨
       (p=2 ∧ q=3 ∧ r=1 ∧ start.val=2) ∨ (p=1 ∧ q=1 ∧ r=4 ∧ start.val=2) ∨
       (p=1 ∧ q=2 ∧ r=3 ∧ start.val=3) ∨ (p=2 ∧ q=1 ∧ r=3 ∧ start.val=3)) ∧
      MiddlePacketClassAt V p q r start u role := by
  obtain ⟨p,q,r,start,u,role,hAt⟩ := hV
  have hsave := hAt
  obtain ⟨_,_,c,g,h,j,B,z,m,a,b,e,rho,unitLap,window,L,σ,hp,hq,hr,hhost,_⟩ := hAt
  exact ⟨p,q,r,start,u,role,host_cases p q r start hp hq hr hhost,hsave⟩

-- STANDING: DEFINITION
def MiddleCoveredClass (V : Fin 8 → ℝ) : Prop :=
  Fresh.FourBlockShortOpeningArrangement.ShortOpeningCoveredClass V ∨ MiddlePacketClass V

theorem middleCovered_isolation {V : Fin 8 → ℝ} (hV : MiddleCoveredClass V) (k : Fin 8) : Isolation V k := by
  rcases hV with hold|hm
  · exact Fresh.FourBlockShortOpeningArrangement.shortOpeningCovered_isolation hold k
  · exact middlePacket_isolation hm k

theorem shortOpeningCovered_into_middleCovered {V : Fin 8 → ℝ}
    (hV : Fresh.FourBlockShortOpeningArrangement.ShortOpeningCoveredClass V) : MiddleCoveredClass V := by
  exact Or.inl hV

#print axioms all_subjects
#print axioms middlePacket_isolation
#print axioms finite_normal_form
#print axioms middleCovered_isolation
#print axioms shortOpeningCovered_into_middleCovered
end Fresh.FourBlockMiddlePacketArrangement
