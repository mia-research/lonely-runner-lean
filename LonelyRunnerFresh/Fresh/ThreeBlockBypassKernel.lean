import Fresh.ThreeBlockNativeBypass

/-! Rules:1–4,8–18. Native bypass kernel for the three original integer
part ranges in ordered AP blocks. The maximum index4 follows from the
physical eight-runner dimensions, not a cascade move bound. Co-setters at
closed gap faces are allowed; no unique-setter hypothesis is used. -/
open Classical
namespace Fresh.ThreeBlockBypassKernel
open Fresh Fresh.Cascade Fresh.Localisation

theorem shape_output_clear {D : Finset ℝ} (g h : ℝ) (m n : ℤ) (hm : 1 ≤ m)
    (hg : 0 < g) (hh : 0 < h)
    (hentry1 : 1 < (8*(m : ℝ)+1)*g)
    (hentry2 : (8*(m : ℝ)-1)*g < 1)
    (hlo : 8*(n : ℝ) ≤ (8*(m : ℝ)+1)*(g+h))
    (hhi : (8*(m : ℝ)+1)*(g+h) ≤ 8*(n : ℝ)+3)
    (hshape : ∀d∈D,
      (∃j : ℕ, 1 ≤ j ∧ j ≤ 4 ∧ d=(j : ℝ)) ∨
      (∃j : ℕ, j ≤ 4 ∧ d=g+(j : ℝ)) ∨
      (∃j : ℕ, 1 ≤ j ∧ j ≤ 4 ∧ d=g+h+(j : ℝ))) :
    LonelyAt D ((m : ℝ)+1/8) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hgmax : g < 1/7 := by nlinarith
  have hgl : (1/8 : ℝ) ≤ g*((m : ℝ)+1/8) := by nlinarith
  have hgu : g*((m : ℝ)+1/8) ≤ 3/8 := by nlinarith
  intro d hd
  rcases hshape d hd with ⟨j,hj1,hj4,rfl⟩|⟨j,hj4,rfl⟩|⟨j,hj1,hj4,rfl⟩
  · have hj1R : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have hj4R : (j : ℝ) ≤ 4 := by exact_mod_cast hj4
    apply clear_of_window ((j : ℤ)*m) <;> push_cast <;> nlinarith
  · have hj0R : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have hj4R : (j : ℝ) ≤ 4 := by exact_mod_cast hj4
    apply clear_of_window ((j : ℤ)*m) <;> push_cast <;> nlinarith
  · have hj1R : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have hj4R : (j : ℝ) ≤ 4 := by exact_mod_cast hj4
    apply clear_of_window ((j : ℤ)*m+n) <;> push_cast <;> nlinarith

theorem native_shape_bypass {D : Finset ℝ} (g h : ℝ) (m n : ℤ) (hm : 1 ≤ m)
    (hg : 0 < g) (hh : 0 < h)
    (hentry1 : 1 < (8*(m : ℝ)+1)*g)
    (hentry2 : (8*(m : ℝ)-1)*g < 1)
    (hlo : 8*(n : ℝ) ≤ (8*(m : ℝ)+1)*(g+h))
    (hhi : (8*(m : ℝ)+1)*(g+h) ≤ 8*(n : ℝ)+3)
    (hgmem : g∈D) (h1mem : (1 : ℝ)∈D)
    (hshape : ∀d∈D,
      (∃j : ℕ, 1 ≤ j ∧ j ≤ 4 ∧ d=(j : ℝ)) ∨
      (∃j : ℕ, j ≤ 4 ∧ d=g+(j : ℝ)) ∨
      (∃j : ℕ, 1 ≤ j ∧ j ≤ 4 ∧ d=g+h+(j : ℝ))) :
    IsLeast (D : Set ℝ) g ∧ InWay 1 (1/(8*g)) ∧
    IsMove D (1/(8*g)) ((m : ℝ)+1/8) ∧ LonelyAt D ((m : ℝ)+1/8) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hgmax : g < 1/7 := by nlinarith
  have hleast : IsLeast (D : Set ℝ) g := by
    refine ⟨hgmem,?_⟩
    intro d hd
    rcases hshape d hd with ⟨j,hj1,hj4,rfl⟩|⟨j,hj4,rfl⟩|⟨j,hj1,hj4,rfl⟩
    · have hj1R : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      linarith
    · have hj0R : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      linarith
    · have hj1R : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      linarith
  have hpos : ∀d∈D,0 < d := fun d hd => lt_of_lt_of_le hg (hleast.2 hd)
  have hden : (0 : ℝ) < 8*g := by positivity
  have htl : (m : ℝ)-1/8 < 1/(8*g) := by
    apply (lt_div_iff₀ hden).2
    nlinarith
  have htu : 1/(8*g) < (m : ℝ)+1/8 := by
    apply (div_lt_iff₀ hden).2
    nlinarith
  have habs : |(1 : ℝ)*(1/(8*g))-(m : ℝ)| < 1/8 := by
    rw [abs_lt]
    constructor <;> nlinarith
  have hw : InWay 1 (1/(8*g)) :=
    lt_of_le_of_lt (Fresh.Cascade.distInt_le _ m) habs
  have hop : nextOpening 1 (1/(8*g))=(m : ℝ)+1/8 := by
    simpa using (nextOpening_eq habs)
  have hclear := shape_output_clear g h m n hm hg hh hentry1 hentry2 hlo hhi hshape
  refine ⟨hleast,hw,?_,hclear⟩
  refine Or.inr ⟨1,h1mem,hw,hop.symm,?_⟩
  intro d hd hdw
  exact nextOpening_le_of_lonely hpos hclear htu.le hd hdw

#print axioms shape_output_clear
#print axioms native_shape_bypass
end Fresh.ThreeBlockBypassKernel
