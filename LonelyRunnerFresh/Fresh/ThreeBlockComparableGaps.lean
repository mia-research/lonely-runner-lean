import Fresh.ThreeBlockGridTriangle

/-! Rules:1–4,8–18. Continuous independent-gap consumer of native grid
triangles. Both gaps are positive and comparable, with sum ≤ 1/16. The
canonical grid index is derived from the smaller gap, never supplied as an
isolation assumption. [PROVISIONAL: counting tool] Int.ceil selects the
native AP reference q=8m+1; no global move or isolation-time cap is claimed. -/
open Classical
namespace Fresh.ThreeBlockComparableGaps
open Fresh Fresh.OneMover Fresh.ThreeBlockCarry Fresh.ThreeBlockGridTriangle

theorem canonical_grid (g h : ℝ) (hg : 0 < g) (hh : 0 < h)
    (hcomp : max g h  ≤  (3/2 : ℝ)*min g h) (hsmall : g+h  ≤  1/16) :
    ∃m : ℤ, 1  ≤  m ∧ 1  ≤  (8*(m : ℝ)+1)*g ∧
      1  ≤  (8*(m : ℝ)+1)*h ∧ (8*(m : ℝ)+1)*(g+h)  ≤  3 := by
  let s := min g h
  have hs : 0 < s := lt_min hg hh
  have hsg : s ≤ g := min_le_left _ _
  have hsh : s ≤ h := min_le_right _ _
  have hsb : s ≤ 1/32 := by linarith
  have hinv : (32 : ℝ)  ≤  1/s := by
    apply (le_div_iff₀ hs).2
    linarith
  let m : ℤ := ⌈(1/s-1)/8⌉
  have hmlo : (1/s-1)/8  ≤  (m : ℝ) := Int.le_ceil _
  have hmhi : (m : ℝ)  <  (1/s-1)/8+1 := Int.ceil_lt_add_one _
  have hmp : (0 : ℝ) < m := by linarith
  have hm : 1 ≤ m := by
    have hi : (0 : ℤ) < m := by exact_mod_cast hmp
    omega
  have hq : 0 < 8*(m : ℝ)+1 := by linarith
  have hqs : 1  ≤  (8*(m : ℝ)+1)*s := by
    have hh := mul_le_mul_of_nonneg_right hmlo hs.le
    have he : ((1/s-1)/8)*s=(1-s)/8 := by field_simp <;> ring
    rw [he] at hh
    nlinarith
  have hsumratio : (g+h)/s  ≤  (5/2 : ℝ) := by
    apply (div_le_iff₀ hs).2
    have he : min g h+max g h=g+h := min_add_max g h
    dsimp [s]
    linarith
  have hqu : 8*(m : ℝ)+1 < 1/s+8 := by linarith
  have hprod := mul_lt_mul_of_pos_right hqu (by linarith : 0 < g+h)
  have he : (1/s+8)*(g+h)=(g+h)/s+8*(g+h) := by ring
  rw [he] at hprod
  refine ⟨m,hm,?_,?_,by linarith⟩
  · have hmulg := mul_le_mul_of_nonneg_left hsg hq.le
    linarith
  · have hmulh := mul_le_mul_of_nonneg_left hsh hq.le
    linarith

theorem comparable_all_subjects (c g h : ℝ) (hg : 0 < g) (hh : 0 < h)
    (hcomp : max g h  ≤  (3/2 : ℝ)*min g h) (hsmall : g+h  ≤  1/16) :
    ∀k : Fin 8, Isolation (speeds c g h) k := by
  obtain ⟨m,hm,hgq,hhq,hsumq⟩ := canonical_grid g h hg hh hcomp hsmall
  exact grid_triangle_all_subjects c g h m hm hgq hhq hsumq

-- STANDING: DEFINITION
def ThreeBlockComparableGapsClass (V : Fin 8 → ℝ) : Prop :=
  (∀i,0 < V i) ∧ Function.Injective V ∧
  ∃(c g h B a : ℝ)(σ : Equiv.Perm (Fin 8)),
    0 < g ∧ 0 < h ∧ max g h  ≤  (3/2 : ℝ)*min g h ∧ g+h  ≤  1/16 ∧ a≠0 ∧
    V=(fun i => B+a*speeds c g h (σ i))

theorem threeBlockComparableGaps_isolation {V : Fin 8 → ℝ}
    (h : ThreeBlockComparableGapsClass V)(k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,h,B,a,σ,hg,hh,hcomp,hsmall,ha,hV⟩ := h
  rw [hV]
  have hi := comparable_all_subjects c g h hg hh hcomp hsmall (σ k)
  have hi' := subject_isolation_affine B a ha hi
  exact (Fresh.isolation_comp_perm _ σ k).2 hi'

#print axioms canonical_grid
#print axioms comparable_all_subjects
#print axioms threeBlockComparableGaps_isolation
end Fresh.ThreeBlockComparableGaps
