import Fresh.SplitAPBands
import Fresh.TwoMoverSubjectTransport

/-!
Rules: 1–4, 8–18. Physical realization of two disjoint AP blocks of the
same positive step, total length eight, both lengths at least two.
The current theorem is explicitly conditional on the positive splitTrain
family for r=1,...,5; it does not assert that supplied family theorem.
An interior subject has fewer fixed integer disparities, hence its actual
readings fit a splitTrain superset with r the farther own-block endpoint.
-/
open Classical
namespace Fresh.SplitAPArrangement
open Fresh Fresh.OneMover Fresh.SplitAPBands

noncomputable def speeds (c A : ℝ) (p : ℕ) (i : Fin 8) : ℝ :=
  if (i : ℕ) < p then c+(i : ℕ) else c+A+((i : ℕ)-p : ℕ)

theorem fixed_mem (r : ℕ) (a : ℝ) (i k : Fin 8) (hik : i ≠ k)
    (hr : (((i : ℕ) : ℤ)-((k : ℕ) : ℤ)).natAbs ≤ r) :
    |((i : ℕ) : ℝ)-((k : ℕ) : ℝ)| ∈ splitTrain r a := by
  set n := (((i : ℕ) : ℤ)-((k : ℕ) : ℤ)).natAbs with hn
  have hn1 : 1 ≤ n := by rw [hn]; have := Fin.val_ne_of_ne hik; omega
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨n-1,Finset.mem_range.mpr (by omega),?_⟩
  have hnn : n-1+1=n := by omega
  rw [hnn,hn]
  exact natAbs_cast_abs i k

theorem translated_mem (r j : ℕ) (a : ℝ) (hj : j+r ≤ 6) :
    a+(j : ℝ) ∈ splitTrain r a := by
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  exact ⟨j,Finset.mem_range.mpr (by omega),rfl⟩

/-- Conditional assembly, to be discharged by the positive splitTrain
family theorems. The gap parameter need only order the two physical blocks. -/
theorem two_block_all_of_split
    (H : ∀ r : ℕ, 1 ≤ r → r ≤ 5 → ∀ a : ℝ, 0 < a →
      ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain r a, (1/8 : ℝ) ≤ distInt (d*t))
    (c A : ℝ) (p : ℕ) (hp2 : 2 ≤ p) (hp6 : p ≤ 6)
    (hgap : (p : ℝ)-1 < A) : ∀ k : Fin 8, Isolation (speeds c A p) k := by
  intro k
  by_cases hkp : (k : ℕ) < p
  · let r := max (k : ℕ) (p-1-(k : ℕ))
    have hr1 : 1 ≤ r := by dsimp [r]; omega
    have hrp : r ≤ p-1 := by dsimp [r]; omega
    have hr5 : r ≤ 5 := by omega
    have hkR : ((k : ℕ) : ℝ) ≤ (p : ℝ)-1 := by
      have hc : ((k : ℕ) : ℝ)+1 ≤ (p : ℝ) := by exact_mod_cast (show (k : ℕ)+1 ≤ p by omega)
      linarith
    have hapos : 0 < A-((k : ℕ) : ℝ) := by linarith
    obtain ⟨t,ht,hclear⟩ := H r hr1 hr5 (A-((k : ℕ) : ℝ)) hapos
    refine ⟨t,ht,fun i hik => ?_⟩
    rw [← Fresh.Localisation.distInt_abs_mul]
    apply hclear
    by_cases hip : (i : ℕ) < p
    · have hd : speeds c A p i-speeds c A p k = ((i : ℕ) : ℝ)-((k : ℕ) : ℝ) := by simp [speeds,hip,hkp]
      rw [hd]
      apply fixed_mem r _ i k hik
      dsimp [r]
      omega
    · have hj : (i : ℕ)-p+r ≤ 6 := by have := i.isLt; omega
      have hj0 : (0 : ℝ) ≤ (((i : ℕ)-p : ℕ) : ℝ) := Nat.cast_nonneg _
      have hd : speeds c A p i-speeds c A p k = (A-((k : ℕ) : ℝ))+(((i : ℕ)-p : ℕ) : ℝ) := by simp [speeds,hip,hkp]; ring
      rw [hd,abs_of_pos (by linarith)]
      exact translated_mem r ((i : ℕ)-p) _ hj
  · let r := max ((k : ℕ)-p) (7-(k : ℕ))
    have hk8 := k.isLt
    have hr1 : 1 ≤ r := by dsimp [r]; omega
    have hrq : r ≤ 7-p := by dsimp [r]; omega
    have hr5 : r ≤ 5 := by omega
    have hpR : ((p-1 : ℕ) : ℝ) = (p : ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ p)]; norm_num
    have hapos : 0 < A+(((k : ℕ)-p : ℕ) : ℝ)-((p-1 : ℕ) : ℝ) := by
      rw [hpR]
      have := Nat.cast_nonneg (α := ℝ) ((k : ℕ)-p)
      linarith
    obtain ⟨t,ht,hclear⟩ := H r hr1 hr5 (A+(((k : ℕ)-p : ℕ) : ℝ)-((p-1 : ℕ) : ℝ)) hapos
    refine ⟨t,ht,fun i hik => ?_⟩
    rw [← Fresh.Localisation.distInt_abs_mul]
    apply hclear
    by_cases hip : (i : ℕ) < p
    · have hj : p-1-(i : ℕ)+r ≤ 6 := by omega
      have hjcast : (((p-1-(i : ℕ) : ℕ)) : ℝ) = ((p-1 : ℕ) : ℝ)-((i : ℕ) : ℝ) := by rw [Nat.cast_sub (by omega : (i : ℕ) ≤ p-1)]
      have hd : speeds c A p i-speeds c A p k = -((A+(((k : ℕ)-p : ℕ) : ℝ)-((p-1 : ℕ) : ℝ))+(((p-1-(i : ℕ) : ℕ)) : ℝ)) := by
        rw [hjcast]
        simp [speeds,hip,hkp]
        ring
      have hj0 := Nat.cast_nonneg (α := ℝ) (p-1-(i : ℕ))
      rw [hd,abs_neg,abs_of_pos (by linarith)]
      exact translated_mem r (p-1-(i : ℕ)) _ hj
    · have hip' : p ≤ (i : ℕ) := by omega
      have hkp' : p ≤ (k : ℕ) := by omega
      have hicas : (((i : ℕ)-p : ℕ) : ℝ) = ((i : ℕ) : ℝ)-(p : ℝ) := by norm_cast
      have hkcas : (((k : ℕ)-p : ℕ) : ℝ) = ((k : ℕ) : ℝ)-(p : ℝ) := by norm_cast
      have hd : speeds c A p i-speeds c A p k = ((i : ℕ) : ℝ)-((k : ℕ) : ℝ) := by
        simp only [speeds,if_neg hip,if_neg hkp]
        rw [hicas,hkcas]
        ring
      rw [hd]
      apply fixed_mem r _ i k hik
      dsimp [r]
      omega

/-- Physical two-block arrangements, including scale, mirror, drift and labels.
Its isolation consumer remains explicitly conditional until splitTrain's
positive parameter theorems are supplied. -/
-- STANDING: DEFINITION
def TwoAPBlockClass (v : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < v i) ∧ Function.Injective v ∧
  ∃ (c A B s : ℝ) (p : ℕ) (σ : Equiv.Perm (Fin 8)),
    2 ≤ p ∧ p ≤ 6 ∧ (p : ℝ)-1 < A ∧ s ≠ 0 ∧
    v = (fun i => B+s*speeds c A p (σ i))

theorem twoAPBlock_isolation_of_split
    (H : ∀ r : ℕ, 1 ≤ r → r ≤ 5 → ∀ a : ℝ, 0 < a →
      ∃ t : ℝ, 0 < t ∧ ∀ d ∈ splitTrain r a, (1/8 : ℝ) ≤ distInt (d*t))
    {v : Fin 8 → ℝ} (h : TwoAPBlockClass v) (k : Fin 8) : Isolation v k := by
  obtain ⟨hpos,hinj,c,A,B,s,p,σ,hp2,hp6,hgap,hs,hv⟩ := h
  rw [hv]
  have hi := two_block_all_of_split H c A p hp2 hp6 hgap (σ k)
  have ha := subject_isolation_affine B s hs hi
  exact (Fresh.isolation_comp_perm _ σ k).2 ha

#print axioms fixed_mem
#print axioms translated_mem
#print axioms two_block_all_of_split
#print axioms twoAPBlock_isolation_of_split
end Fresh.SplitAPArrangement
