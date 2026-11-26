import Fresh.ThreeBlockGridTriangle
import Fresh.ThreeBlockComparableGaps

/-! A polynomial input region for two independent near-coalescent gaps.
The canonical AP index is derived from the smaller gap. Both real gaps
remain strictly positive; their ratio and size need not be fixed.
[PROVISIONAL: counting tool] the ceiling places the native AP grid carry.
Actual original cascade controls: three_block_polynomial_v1.py.
-/
open Classical
namespace Fresh.ThreeBlockPolynomialGaps
open Fresh Fresh.OneMover Fresh.ThreeBlockCarry Fresh.ThreeBlockGridTriangle

theorem polynomial_grid (g h : ℝ) (hg : 0 < g) (hh : 0 < h)
    (hpoly : (g+h)*(1+8*min g h) ≤ 3*min g h) :
    ∃ m : ℤ, 1 ≤ m ∧ 1 ≤ (8*(m : ℝ)+1)*g ∧
      1 ≤ (8*(m : ℝ)+1)*h ∧ (8*(m : ℝ)+1)*(g+h) ≤ 3 := by
  let a := min g h
  have ha : 0 < a := lt_min hg hh
  have hag : a ≤ g := min_le_left _ _
  have hah : a ≤ h := min_le_right _ _
  have hsum : 2*a ≤ g+h := by linarith
  have hpoly' : (g+h)*(1+8*a) ≤ 3*a := hpoly
  have ha16 : a ≤ 1/16 := by
    by_contra hn
    have hp : 0 < a*(16*a-1) := mul_pos ha (by linarith)
    have hm := mul_le_mul_of_nonneg_right hsum (by positivity : 0 ≤ 1+8*a)
    nlinarith
  have hinv : (16 : ℝ) ≤ 1/a := by
    apply (le_div_iff₀ ha).2
    linarith
  let m : ℤ := ⌈(1/a-1)/8⌉
  have hmlo : (1/a-1)/8 ≤ (m : ℝ) := Int.le_ceil _
  have hmhi : (m : ℝ) < (1/a-1)/8+1 := Int.ceil_lt_add_one _
  have hmp : (0 : ℝ) < m := by linarith
  have hm : 1 ≤ m := by
    have hi : (0 : ℤ) < m := by exact_mod_cast hmp
    omega
  have hq : 0 < 8*(m : ℝ)+1 := by linarith
  have hqa : 1 ≤ (8*(m : ℝ)+1)*a := by
    have hm := mul_le_mul_of_nonneg_right hmlo ha.le
    have he : ((1/a-1)/8)*a=(1-a)/8 := by field_simp <;> ring
    rw [he] at hm
    nlinarith
  have hqu : 8*(m : ℝ)+1 < 1/a+8 := by linarith
  have hprod := mul_lt_mul_of_pos_right hqu (by linarith : 0 < g+h)
  have hratio : (g+h)/a+8*(g+h) ≤ 3 := by
    have he : (g+h)/a+8*(g+h)=((g+h)*(1+8*a))/a := by field_simp <;> ring
    rw [he,div_le_iff₀ ha]
    exact hpoly'
  have he : (1/a+8)*(g+h)=(g+h)/a+8*(g+h) := by ring
  rw [he] at hprod
  refine ⟨m,hm,?_,?_,by linarith⟩
  · have hmulg := mul_le_mul_of_nonneg_left hag hq.le
    linarith
  · have hmulh := mul_le_mul_of_nonneg_left hah hq.le
    linarith

theorem polynomial_all_subjects (c g h : ℝ) (hg : 0 < g) (hh : 0 < h)
    (hpoly : (g+h)*(1+8*min g h) ≤ 3*min g h) :
    ∀ k : Fin 8, Isolation (speeds c g h) k := by
  obtain ⟨m,hm,hgq,hhq,hsum⟩ := polynomial_grid g h hg hh hpoly
  exact grid_triangle_all_subjects c g h m hm hgq hhq hsum

-- STANDING: DEFINITION
def ThreeBlockPolynomialGapsClass (V : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < V i) ∧ Function.Injective V ∧
  ∃ (c g h B a : ℝ) (σ : Equiv.Perm (Fin 8)),
    0 < g ∧ 0 < h ∧ (g+h)*(1+8*min g h) ≤ 3*min g h ∧ a ≠ 0 ∧
    V=(fun i => B+a*speeds c g h (σ i))

theorem threeBlockPolynomialGaps_isolation {V : Fin 8 → ℝ}
    (h : ThreeBlockPolynomialGapsClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,h,B,a,σ,hg,hh,hpoly,ha,hV⟩ := h
  rw [hV]
  have hi := polynomial_all_subjects c g h hg hh hpoly (σ k)
  have hi' := subject_isolation_affine B a ha hi
  exact (Fresh.isolation_comp_perm _ σ k).2 hi'

theorem comparable_imp_polynomial {V : Fin 8 → ℝ}
    (h : Fresh.ThreeBlockComparableGaps.ThreeBlockComparableGapsClass V) :
    ThreeBlockPolynomialGapsClass V := by
  obtain ⟨hpos,hinj,c,g,h,B,a,σ,hg,hh,hcomp,hsmall,ha,hV⟩ := h
  refine ⟨hpos,hinj,c,g,h,B,a,σ,hg,hh,?_,ha,hV⟩
  have hs : 0 < min g h := lt_min hg hh
  have hm := min_add_max g h
  have hsum : g+h ≤ (5/2 : ℝ)*min g h := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsmall (le_of_lt hs)
  nlinarith

#print axioms polynomial_grid
#print axioms polynomial_all_subjects
#print axioms threeBlockPolynomialGaps_isolation
#print axioms comparable_imp_polynomial
end Fresh.ThreeBlockPolynomialGaps
