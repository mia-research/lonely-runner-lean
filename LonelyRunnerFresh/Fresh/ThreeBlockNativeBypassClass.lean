import Fresh.ThreeBlockNativeMirror

/-! Rules:1–4,8–18. Subject-specific physical native bypass class from
original gap strips; explicit positivity/injectivity and signed affine
scale, drift and relabel transport. Original opposite gap and lap n are
unbounded. Entry faces remain strict, output gap faces closed. This class
can overlap the all-subject grid classes and earlier types; no disjointness
or complete old-class exclusion is asserted. -/
open Classical
namespace Fresh.ThreeBlockNativeBypassClass
open Fresh Fresh.OneMover Fresh.Cascade Fresh.Localisation Fresh.ThreeBlockCarry
  Fresh.ThreeBlockNativePhysical Fresh.ThreeBlockNativeMirror

-- STANDING: DEFINITION
def NativeBypassClass (V : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  (∀i,0<V i) ∧ Function.Injective V ∧
  ∃(c g h B z : ℝ)(m n : ℤ)(σ : Equiv.Perm (Fin 8)),
    0<g ∧ 0<h ∧ 1 ≤ m ∧
    ((σ k=1 ∧ 1<(8*(m : ℝ)+1)*g ∧ (8*(m : ℝ)-1)*g<1) ∨
     (σ k=6 ∧ 1<(8*(m : ℝ)+1)*h ∧ (8*(m : ℝ)-1)*h<1)) ∧
    8*(n : ℝ) ≤ (8*(m : ℝ)+1)*(g+h) ∧
    (8*(m : ℝ)+1)*(g+h) ≤ 8*(n : ℝ)+3 ∧ z≠0 ∧
    V=(fun i => B+z*speeds c g h (σ i))

theorem nativeBypass_isolation {V : Fin 8 → ℝ} {k : Fin 8}
    (h : NativeBypassClass V k) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,h,B,z,m,n,σ,hg,hh,hm,hrole,hlo,hhi,hz,hV⟩ := h
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hbase : Isolation (speeds c g h) (σ k) := by
    rcases hrole with ⟨hk,hentry1,hentry2⟩|⟨hk,hentry1,hentry2⟩
    · rw [hk]
      obtain ⟨hleast,hw,hmove,hclear⟩ := physical_native_opposite_pair_bypass c g h m n hm hg hh hentry1 hentry2 hlo hhi
      exact ⟨(m : ℝ)+1/8,by linarith,(isolatedAt_iff _ _ _).2 hclear⟩
    · rw [hk]
      obtain ⟨hleast,hw,hmove,hclear⟩ := physical_native_reflected_bypass c g h m n hm hg hh hentry1 hentry2 hlo hhi
      exact ⟨(m : ℝ)+1/8,by linarith,(isolatedAt_iff _ _ _).2 hclear⟩
  rw [hV]
  have hi := subject_isolation_affine B z hz hbase
  exact (Fresh.isolation_comp_perm _ σ k).2 hi

#print axioms nativeBypass_isolation
end Fresh.ThreeBlockNativeBypassClass
