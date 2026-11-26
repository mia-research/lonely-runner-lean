import Fresh.FourAPPairs

/-! A direct original-input region with three independent positive gaps.
[PROVISIONAL: counting tool] the canonical ceiling derives the native AP index.
All exact original-subject controls: four_pair_polynomial_v1.py/json.
-/
namespace Fresh.FourPairPolynomialGaps
open Fresh Fresh.OneMover Fresh.FourAPPairs

theorem polynomial_grid (g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (hpoly : (g+h+j)*(1+8*min g (min h j)) ≤ 4*min g (min h j)) :
    ∃ m : ℤ, 1 ≤ m ∧ 1 ≤ (8*(m : ℝ)+1)*g ∧
      1 ≤ (8*(m : ℝ)+1)*h ∧ 1 ≤ (8*(m : ℝ)+1)*j ∧
      (8*(m : ℝ)+1)*(g+h+j) ≤ 4 ∧ g+h+j ≤ 3 := by
  let a := min g (min h j)
  have ha : 0 < a := lt_min hg (lt_min hh hj)
  have hag : a ≤ g := min_le_left _ _
  have hah : a ≤ h := le_trans (min_le_right _ _) (min_le_left _ _)
  have haj : a ≤ j := le_trans (min_le_right _ _) (min_le_right _ _)
  have hS : 0 < g+h+j := by linarith
  have hsum : 3*a ≤ g+h+j := by linarith
  have hpoly' : (g+h+j)*(1+8*a) ≤ 4*a := hpoly
  have ha24 : a ≤ 1/24 := by
    by_contra hn
    have hp : 0 < a*(24*a-1) := mul_pos ha (by linarith)
    have hm := mul_le_mul_of_nonneg_right hsum (by positivity : 0 ≤ 1+8*a)
    nlinarith
  have hinv : (24 : ℝ) ≤ 1/a := by
    apply (le_div_iff₀ ha).2
    linarith
  let m : ℤ := ⌈(1/a-1)/8⌉
  have hmlo : (1/a-1)/8 ≤ (m : ℝ) := Int.le_ceil _
  have hmhi : (m : ℝ) < (1/a-1)/8+1 := Int.ceil_lt_add_one _
  have hmp : (0 : ℝ) < m := by linarith
  have hm : 1 ≤ m := by
    have hi : (0 : ℤ) < m := by exact_mod_cast hmp
    omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 0 < 8*(m : ℝ)+1 := by linarith
  have hqa : 1 ≤ (8*(m : ℝ)+1)*a := by
    have ht := mul_le_mul_of_nonneg_right hmlo ha.le
    have he : ((1/a-1)/8)*a=(1-a)/8 := by field_simp
    rw [he] at ht
    nlinarith
  have hqu : 8*(m : ℝ)+1 < 1/a+8 := by linarith
  have hprod := mul_lt_mul_of_pos_right hqu hS
  have hratio : (g+h+j)/a+8*(g+h+j) ≤ 4 := by
    have he : (g+h+j)/a+8*(g+h+j)=((g+h+j)*(1+8*a))/a := by field_simp
    rw [he,div_le_iff₀ ha]
    exact hpoly'
  have he : (1/a+8)*(g+h+j)=(g+h+j)/a+8*(g+h+j) := by ring
  rw [he] at hprod
  have hqS : (8*(m : ℝ)+1)*(g+h+j) ≤ 4 := by linarith
  refine ⟨m,hm,?_,?_,?_,hqS,?_⟩
  · have ht := mul_le_mul_of_nonneg_left hag hq.le
    linarith
  · have ht := mul_le_mul_of_nonneg_left hah hq.le
    linarith
  · have ht := mul_le_mul_of_nonneg_left haj hq.le
    linarith
  · nlinarith

theorem polynomial_all_subjects (c g h j : ℝ) (hg : 0 < g) (hh : 0 < h) (hj : 0 < j)
    (hpoly : (g+h+j)*(1+8*min g (min h j)) ≤ 4*min g (min h j)) :
    ∀ k : Fin 8, Isolation (speeds c g h j) k := by
  obtain ⟨m,hm,hgq,hhq,hjq,hsum,hsmall⟩ := polynomial_grid g h j hg hh hj hpoly
  exact four_pairs_all_subjects c g h j m 0 0 0 hm hg hh hj hsmall
    (by simpa using hgq) (by simpa using hhq) (by simpa using hjq) (by simpa using hsum)

-- STANDING: DEFINITION
def FourPairPolynomialClass (V : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < V i) ∧ Function.Injective V ∧
  ∃ (c g h j B z : ℝ) (σ : Equiv.Perm (Fin 8)),
    0 < g ∧ 0 < h ∧ 0 < j ∧
    (g+h+j)*(1+8*min g (min h j)) ≤ 4*min g (min h j) ∧ z ≠ 0 ∧
    V=(fun i => B+z*speeds c g h j (σ i))

theorem polynomial_into_fourPairs {V : Fin 8 → ℝ} (h : FourPairPolynomialClass V) :
    FourAPPairsClass V := by
  obtain ⟨hpos,hinj,c,g,h,j,B,z,σ,hg,hh,hj,hpoly,hz,hV⟩ := h
  obtain ⟨m,hm,hgq,hhq,hjq,hsum,hsmall⟩ := polynomial_grid g h j hg hh hj hpoly
  exact ⟨hpos,hinj,c,g,h,j,B,z,m,0,0,0,σ,hg,hh,hj,hsmall,hm,
    by simpa using hgq,by simpa using hhq,by simpa using hjq,by simpa using hsum,hz,hV⟩

theorem fourPairPolynomial_isolation {V : Fin 8 → ℝ}
    (h : FourPairPolynomialClass V) (k : Fin 8) : Isolation V k :=
  fourAPPairs_isolation (polynomial_into_fourPairs h) k

#print axioms polynomial_grid
#print axioms polynomial_all_subjects
#print axioms polynomial_into_fourPairs
#print axioms fourPairPolynomial_isolation
end Fresh.FourPairPolynomialGaps
