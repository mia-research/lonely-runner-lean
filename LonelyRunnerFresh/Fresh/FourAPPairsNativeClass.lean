import Fresh.FourAPPairsNativePhysical

/-! Rules:1–4,8–18. Original-input class for actual native four-pair bypass.
Positive/injective physical speeds, signed scale, drift and relabel explicit.
The cumulative original gaps and their lap labels are unbounded. Boundary
co-setters are permitted; original partner entry faces remain strict. -/
open Classical
namespace Fresh.FourAPPairsNativeClass
open Fresh Fresh.OneMover Fresh.Localisation Fresh.FourAPPairs
  Fresh.FourAPPairsNativePhysical

-- STANDING: DEFINITION
def FourPairNativeClass (V : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  (∀i,0<V i) ∧ Function.Injective V ∧
  ∃(c g h j B z : ℝ)(m a b : ℤ)(σ : Equiv.Perm (Fin 8)),
    0<g ∧ 0<h ∧ 0<j ∧ 1 ≤ m ∧
    ((σ k=1 ∧ 1<(8*(m : ℝ)+1)*g ∧ (8*(m : ℝ)-1)*g<1 ∧
       8*(a : ℝ) ≤ (8*(m : ℝ)+1)*(g+h) ∧
       (8*(m : ℝ)+1)*(g+h) ≤ 8*(a : ℝ)+5) ∨
     (σ k=6 ∧ 1<(8*(m : ℝ)+1)*j ∧ (8*(m : ℝ)-1)*j<1 ∧
       8*(a : ℝ) ≤ (8*(m : ℝ)+1)*(h+j) ∧
       (8*(m : ℝ)+1)*(h+j) ≤ 8*(a : ℝ)+5)) ∧
    8*(b : ℝ) ≤ (8*(m : ℝ)+1)*(g+h+j) ∧
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*(b : ℝ)+4 ∧ z≠0 ∧
    V=(fun i => B+z*speeds c g h j (σ i))

theorem fourPairNative_isolation {V : Fin 8 → ℝ} {k : Fin 8}
    (h : FourPairNativeClass V k) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,σ,hg,hh,hj,hm,hrole,hR1,hR2,hz,hV⟩ := h
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hbase : Isolation (speeds c g h j) (σ k) := by
    rcases hrole with ⟨hk,he1,he2,hS1,hS2⟩|⟨hk,he1,he2,hS1,hS2⟩
    · rw [hk]
      obtain ⟨hleast,hw,hmv,hclear⟩ := physical_left_native_bypass c g h j m a b hm hg hh hj he1 he2 hS1 hS2 hR1 hR2
      exact ⟨(m : ℝ)+1/8,by linarith,(isolatedAt_iff _ _ _).2 hclear⟩
    · rw [hk]
      obtain ⟨hleast,hw,hmv,hclear⟩ := physical_right_native_bypass c g h j m a b hm hg hh hj he1 he2 hS1 hS2 hR1 hR2
      exact ⟨(m : ℝ)+1/8,by linarith,(isolatedAt_iff _ _ _).2 hclear⟩
  rw [hV]
  have hi := subject_isolation_affine B z hz hbase
  exact (Fresh.isolation_comp_perm _ σ k).2 hi

#print axioms fourPairNative_isolation
end Fresh.FourAPPairsNativeClass
