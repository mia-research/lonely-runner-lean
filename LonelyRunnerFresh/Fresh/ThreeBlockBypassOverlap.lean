import Fresh.ThreeBlockNativeBypassClass

/-! Rules:1–4,8–18. Explicit original-input overlap and extension checks.
The seed belongs to two reference-band input descriptions. A separate
unbounded opposite-gap family violates the earlier kernel's original
sum≤1/3 condition; this does not assert nonmembership after every possible
physical reparameterization or in every earlier proved arrangement class. -/
open Classical
namespace Fresh.ThreeBlockBypassOverlap
open Fresh Fresh.OneMover Fresh.Localisation Fresh.ThreeBlockCarry
  Fresh.ThreeBlockNativePhysical

theorem seed_input_overlap :
    (1 < (25 : ℝ)*(1/24) ∧ (23 : ℝ)*(1/24) < 1 ∧
      (8 : ℝ) ≤ 25*(1/24+25/88) ∧ 25*(1/24+25/88) ≤ 11) ∧
    ((1/24 : ℝ)+25/88 ≤ 1/3 ∧
      (1 : ℝ) ≤ 33*(1/24) ∧ (9 : ℝ) ≤ 33*(25/88) ∧
      33*((1/24 : ℝ)+25/88) ≤ 11) := by norm_num

theorem unbounded_native_input (n : ℤ) (hn : 1 ≤ n) :
    let g : ℝ := 1/24
    let h : ℝ := (8*(n : ℝ)+1)/25-1/24
    0<g ∧ 0<h ∧ 1<(25 : ℝ)*g ∧ (23 : ℝ)*g<1 ∧
      8*(n : ℝ) ≤ 25*(g+h) ∧ 25*(g+h) ≤ 8*(n : ℝ)+3 ∧
      (1/3 : ℝ)<g+h := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  dsimp
  constructor
  · norm_num
  constructor
  · linarith
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · linarith
  constructor <;> linarith

theorem unbounded_native_subject_isolation (c : ℝ) (n : ℤ) (hn : 1 ≤ n) :
    Isolation (speeds c (1/24) ((8*(n : ℝ)+1)/25-1/24)) (1 : Fin 8) := by
  obtain ⟨hg,hh,he1,he2,hlo,hhi,hsum⟩ := unbounded_native_input n hn
  obtain ⟨hleast,hw,hmv,hclear⟩ := physical_native_opposite_pair_bypass c (1/24)
    ((8*(n : ℝ)+1)/25-1/24) 3 n (by norm_num) hg hh
    (by norm_num) (by norm_num)
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)
  refine ⟨25/8,by norm_num,?_⟩
  apply (isolatedAt_iff _ _ _).2
  norm_num at hclear
  exact hclear

#print axioms seed_input_overlap
#print axioms unbounded_native_input
#print axioms unbounded_native_subject_isolation
end Fresh.ThreeBlockBypassOverlap
