import Fresh.SplitAPArrangement

/-!
Rules: 1–4, 8–18. Physical realization of two same-step AP blocks at ANY
noninteger relative offset, including interleaving and either placement.
The theorem is explicitly conditional on the signed splitTrain family.
Physical positivity/injectivity remain explicit in the arrangement class.
-/
open Classical
namespace Fresh.SplitAPArrangement
open Fresh Fresh.OneMover Fresh.SplitAPBands

theorem two_block_all_of_signed
    (H : ∀ r : ℕ, 1 ≤ r → r ≤ 5 → ∀ B : ℝ, (∀ m : ℤ, B ≠ m) →
      ∃ t : ℝ, 0<t ∧ ∀ d ∈ splitTrain r B, (1/8 : ℝ) ≤ distInt (d*t))
    (c A : ℝ) (p : ℕ) (hp2 : 2 ≤ p) (hp6 : p ≤ 6)
    (hA : ∀ m : ℤ, A ≠ m) : ∀ k : Fin 8, Isolation (speeds c A p) k := by
  intro k
  by_cases hkp : (k : ℕ) < p
  · let r := max (k : ℕ) (p-1-(k : ℕ))
    have hr1 : 1 ≤ r := by dsimp [r]; omega
    have hrp : r ≤ p-1 := by dsimp [r]; omega
    have hr5 : r ≤ 5 := by omega
    have hB : ∀ m : ℤ, A-((k : ℕ) : ℝ) ≠ m := by
      intro m he
      apply hA (m+((k : ℕ) : ℤ))
      push_cast
      linarith
    obtain ⟨t,ht,hclear⟩ := H r hr1 hr5 (A-((k : ℕ) : ℝ)) hB
    refine ⟨t,ht,fun i hik => ?_⟩
    by_cases hip : (i : ℕ) < p
    · have hd : speeds c A p i-speeds c A p k = ((i : ℕ) : ℝ)-((k : ℕ) : ℝ) := by simp [speeds,hip,hkp]
      rw [hd,← Fresh.Localisation.distInt_abs_mul]
      apply hclear
      apply fixed_mem r _ i k hik
      dsimp [r]
      omega
    · have hj : (i : ℕ)-p+r ≤ 6 := by have := i.isLt; omega
      have hd : speeds c A p i-speeds c A p k = (A-((k : ℕ) : ℝ))+(((i : ℕ)-p : ℕ) : ℝ) := by simp [speeds,hip,hkp]; ring
      rw [hd]
      exact hclear _ (translated_mem r ((i : ℕ)-p) _ hj)
  · let r := max ((k : ℕ)-p) (7-(k : ℕ))
    have hk8 := k.isLt
    have hr1 : 1 ≤ r := by dsimp [r]; omega
    have hrq : r ≤ 7-p := by dsimp [r]; omega
    have hr5 : r ≤ 5 := by omega
    have hB : ∀ m : ℤ, -A-(((k : ℕ)-p : ℕ) : ℝ) ≠ m := by
      intro m he
      apply hA (-m-(((k : ℕ)-p : ℕ) : ℤ))
      push_cast
      linarith
    obtain ⟨t,ht,hclear⟩ := H r hr1 hr5 (-A-(((k : ℕ)-p : ℕ) : ℝ)) hB
    refine ⟨t,ht,fun i hik => ?_⟩
    by_cases hip : (i : ℕ) < p
    · have hj : (i : ℕ)+r ≤ 6 := by omega
      have hd : speeds c A p i-speeds c A p k = (-A-(((k : ℕ)-p : ℕ) : ℝ))+((i : ℕ) : ℝ) := by simp [speeds,hip,hkp]; ring
      rw [hd]
      exact hclear _ (translated_mem r (i : ℕ) _ hj)
    · have hip' : p ≤ (i : ℕ) := by omega
      have hkp' : p ≤ (k : ℕ) := by omega
      have hicas : (((i : ℕ)-p : ℕ) : ℝ) = ((i : ℕ) : ℝ)-(p : ℝ) := by norm_cast
      have hkcas : (((k : ℕ)-p : ℕ) : ℝ) = ((k : ℕ) : ℝ)-(p : ℝ) := by norm_cast
      have hd : speeds c A p i-speeds c A p k = ((i : ℕ) : ℝ)-((k : ℕ) : ℝ) := by
        simp only [speeds,if_neg hip,if_neg hkp]
        rw [hicas,hkcas]
        ring
      rw [hd,← Fresh.Localisation.distInt_abs_mul]
      apply hclear
      apply fixed_mem r _ i k hik
      dsimp [r]
      omega

/-- Interleaved or separated blocks; the common relative offset is noninteger.
No ordering or gap threshold is part of this physical class. -/
-- STANDING: DEFINITION
def NonintegerTwoAPBlockClass (v : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < v i) ∧ Function.Injective v ∧
  ∃ (c A B s : ℝ) (p : ℕ) (σ : Equiv.Perm (Fin 8)),
    2 ≤ p ∧ p ≤ 6 ∧ (∀ m : ℤ, A ≠ m) ∧ s ≠ 0 ∧
    v = (fun i => B+s*speeds c A p (σ i))

theorem nonintegerTwoAPBlock_isolation_of_signed
    (H : ∀ r : ℕ, 1 ≤ r → r ≤ 5 → ∀ B : ℝ, (∀ m : ℤ, B ≠ m) →
      ∃ t : ℝ, 0<t ∧ ∀ d ∈ splitTrain r B, (1/8 : ℝ) ≤ distInt (d*t))
    {v : Fin 8 → ℝ} (h : NonintegerTwoAPBlockClass v) (k : Fin 8) : Isolation v k := by
  obtain ⟨hpos,hinj,c,A,B,s,p,σ,hp2,hp6,hA,hs,hv⟩ := h
  rw [hv]
  have hi := two_block_all_of_signed H c A p hp2 hp6 hA (σ k)
  have ha := subject_isolation_affine B s hs hi
  exact (Fresh.isolation_comp_perm _ σ k).2 ha

#print axioms two_block_all_of_signed
#print axioms nonintegerTwoAPBlock_isolation_of_signed
end Fresh.SplitAPArrangement
