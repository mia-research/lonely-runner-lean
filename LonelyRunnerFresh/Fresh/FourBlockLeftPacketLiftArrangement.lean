import Fresh.FourBlockLeftPacketLift

/-! All eight physical subjects for a later original left opening retaining
one original AP packet window after an explicit unit lap. -/
namespace Fresh.FourBlockLeftPacketLiftArrangement
open Fresh Fresh.OneMover Fresh.FourBlockNeighbour Fresh.FourBlockLeftOpening Fresh.FourBlockLeftPacketLift

theorem all_subjects (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j) (m a b e unitLap window : ℤ)
    (u : Fin 3) (L : Fin 3 → ℤ) (hm : 1 ≤ m) (hsmall : g+h+j ≤ 3)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hP : 0 < leftOpening c g h j p q r m a b e u (L u))
    (hf : PacketFaces c g h j p q r m a b e unitLap window (leftOpening c g h j p q r m a b e u (L u)))
    (hl : OtherLeftBandsAt c g h j p q r m a b e (leftOpening c g h j p q r m a b e u (L u)) L u)
    (k : Fin 8) : Isolation (speeds c g h j p q r) k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  by_cases hk0 : k=0
  · subst k
    exact ⟨leftOpening c g h j p q r m a b e u (L u),hP,(Fresh.Localisation.isolatedAt_iff _ _ _).2
      (left_clear c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e unitLap window u L hf hl)⟩
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
def LeftPacketClass (V : Fin 8 → ℝ) : Prop :=
  (∀ i,0 < V i) ∧ Function.Injective V ∧
  ∃ (c g h j B z : ℝ) (p q r : ℕ) (m a b e unitLap window : ℤ)
    (u : Fin 3) (L : Fin 3 → ℤ) (σ : Equiv.Perm (Fin 8)),
    1 ≤ p ∧ 1 ≤ q ∧ 1 ≤ r ∧ p+q+r ≤ 4 ∧
    0 < g ∧ 0 < h ∧ 0 < j ∧ 1 ≤ m ∧ g+h+j ≤ 3 ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j ∧
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4 ∧
    0 < leftOpening c g h j p q r m a b e u (L u) ∧
    PacketFaces c g h j p q r m a b e unitLap window (leftOpening c g h j p q r m a b e u (L u)) ∧
    OtherLeftBandsAt c g h j p q r m a b e (leftOpening c g h j p q r m a b e u (L u)) L u ∧ z≠0 ∧
    V=(fun i=>B+z*speeds c g h j p q r (σ i))

theorem leftPacketClass_isolation {V : Fin 8 → ℝ} (hV : LeftPacketClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,h,j,B,z,p,q,r,m,a,b,e,unitLap,window,u,L,σ,hp,hq,hr,hs,hgpos,hhpos,hjpos,hm,hsmall,
    hg,hh,hj,hsum,hP,hf,hl,hz,hrepr⟩ := hV
  have hi := all_subjects c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e unitLap window u L
    hm hsmall hg hh hj hsum hP hf hl (σ k)
  rw [hrepr]
  exact (Fresh.isolation_comp_perm _ σ k).2 (subject_isolation_affine B z hz hi)

-- STANDING: DEFINITION
def PacketLiftCoveredClass (V : Fin 8 → ℝ) : Prop :=
  Fresh.FourBlockAPAnchorArrangement.APAnchorCoveredClass V ∨ LeftPacketClass V

theorem packetLiftCovered_isolation {V : Fin 8 → ℝ} (hV : PacketLiftCoveredClass V) (k : Fin 8) : Isolation V k := by
  rcases hV with hold|hl
  · exact Fresh.FourBlockAPAnchorArrangement.apAnchorCovered_isolation hold k
  · exact leftPacketClass_isolation hl k

theorem frameCovered_into_packetLiftCovered {V : Fin 8 → ℝ}
    (hV : Fresh.FourBlockPacketFrameArrangement.PacketFrameCoveredClass V) : PacketLiftCoveredClass V := by
  exact Or.inl (Or.inl hV)

#print axioms frameCovered_into_packetLiftCovered
#print axioms all_subjects
#print axioms leftPacketClass_isolation
#print axioms packetLiftCovered_isolation
end Fresh.FourBlockLeftPacketLiftArrangement
