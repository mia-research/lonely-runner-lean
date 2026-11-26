import Fresh.ThreeBlockBypassPartitionMirror
import Fresh.ThreeBlockNativeBypassClass

/-! Rules:1–4,8–18. Physical subject-specific native bypass across all ten
left-gap dimensions and their reflections. Original positivity/injectivity,
signed scale, drift and relabel are explicit; no output clearance premise.
Co-setters on closed gap faces remain permitted. The earlier2+4+2 class
is included explicitly, preventing double counting of that subfamily. -/
open Classical
namespace Fresh.ThreeBlockPartitionBypassClass
open Fresh Fresh.OneMover Fresh.Cascade Fresh.Localisation Fresh.ThreeBlockPartitions
  Fresh.ThreeBlockBypassPartitions Fresh.ThreeBlockBypassPartitionMirror
  Fresh.ThreeBlockNativeBypassClass

-- STANDING: DEFINITION
def PartitionNativeBypassClass (V : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  (∀i,0<V i) ∧ Function.Injective V ∧
  ∃(c g h B z : ℝ)(p q : ℕ)(m n : ℤ)(σ : Equiv.Perm (Fin 8)),
    0<g ∧ 0<h ∧ 2 ≤ q ∧ 1 ≤ m ∧
    ((2 ≤ p ∧ p+q ≤ 7 ∧ ((σ k : Fin 8) : ℕ)=p-1 ∧
       1<(8*(m : ℝ)+1)*g ∧ (8*(m : ℝ)-1)*g<1) ∨
     (1 ≤ p ∧ p+q ≤ 6 ∧ ((σ k : Fin 8) : ℕ)=p+q ∧
       1<(8*(m : ℝ)+1)*h ∧ (8*(m : ℝ)-1)*h<1)) ∧
    8*(n : ℝ) ≤ (8*(m : ℝ)+1)*(g+h) ∧
    (8*(m : ℝ)+1)*(g+h) ≤ 8*(n : ℝ)+3 ∧ z≠0 ∧
    V=(fun i => B+z*speeds c g h p q (σ i))

theorem partitionNativeBypass_isolation {V : Fin 8 → ℝ} {k : Fin 8}
    (h : PartitionNativeBypassClass V k) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,h,B,z,p,q,m,n,σ,hg,hh,hq,hm,hrole,hlo,hhi,hz,hV⟩ := h
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hbase : Isolation (speeds c g h p q) (σ k) := by
    rcases hrole with ⟨hp,hsizes,hk,hentry1,hentry2⟩|⟨hp,hsizes,hk,hentry1,hentry2⟩
    · obtain ⟨hleast,hw,hmv,hclear⟩ := physical_partition_native_bypass c g h p q hp hq hsizes
        m n hm hg hh hentry1 hentry2 hlo hhi (σ k) hk
      exact ⟨(m : ℝ)+1/8,by linarith,(isolatedAt_iff _ _ _).2 hclear⟩
    · obtain ⟨hleast,hw,hmv,hclear⟩ := reflected_partition_native_bypass c g h p q hp hq hsizes
        m n hm hg hh hentry1 hentry2 hlo hhi (σ k) hk
      exact ⟨(m : ℝ)+1/8,by linarith,(isolatedAt_iff _ _ _).2 hclear⟩
  rw [hV]
  have hi := subject_isolation_affine B z hz hbase
  exact (Fresh.isolation_comp_perm _ σ k).2 hi

theorem old_native_into_partition {V : Fin 8 → ℝ} {k : Fin 8}
    (h : NativeBypassClass V k) : PartitionNativeBypassClass V k := by
  obtain ⟨hpos,hinj,c,g,h,B,z,m,n,σ,hg,hh,hm,hrole,hlo,hhi,hz,hV⟩ := h
  refine ⟨hpos,hinj,c,g,h,B,z,2,4,m,n,σ,hg,hh,by norm_num,hm,?_,hlo,hhi,hz,?_⟩
  · rcases hrole with ⟨hk,he1,he2⟩|⟨hk,he1,he2⟩
    · refine Or.inl ⟨by norm_num,by norm_num,?_,he1,he2⟩
      rw [hk]
      norm_num
    · refine Or.inr ⟨by norm_num,by norm_num,?_,he1,he2⟩
      rw [hk]
      norm_num
  · simpa only [Fresh.ThreeBlockCarry.speeds,Fresh.ThreeBlockPartitions.speeds] using hV

#print axioms partitionNativeBypass_isolation
#print axioms old_native_into_partition
end Fresh.ThreeBlockPartitionBypassClass
