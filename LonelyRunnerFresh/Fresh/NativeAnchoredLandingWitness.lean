import Fresh.NativeAnchoredLanding

/-!
First in-tree instantiation of `NativeAnchoredLanding.first_landing_of_faces`.
The arrangement below is explicit: seven distinct positive rational readings
x = ![1, 4/3, 2, 3, 10, 12, 16]. The anchor chain mirrors the opening move of
the J2 route tables (`move1_0 : <0, 1/8> -> <6, 17/8>`, reading 6 captured at
lap 2): from the standard opening (1/8)/x 0 the cascade rises strictly once
and fixes at 17/128 = (17/8)/x 6, where every reading is clear. All four
hypothesis groups of the skeleton (anchor, time, phase, order) fire at
n = 0 < N = 1, and the final band fires for all seven readings.
-/

namespace Fresh.NativeAnchoredLandingWitness

open Fresh Cascade Localisation NativeAnchoredLanding

/-- The witness arrangement. -/
private noncomputable def x : Fin 7 → ℝ :=
  fun i => if i.val = 0 then 1 else if i.val = 1 then 4 / 3 else if i.val = 2 then 2
    else if i.val = 3 then 3 else if i.val = 4 then 10 else if i.val = 5 then 12 else 16

private theorem hx : ∀ i, 0 < x i := by
  intro i
  fin_cases i <;> simp [x] 

/-- Anchor chain: the opening sits on reading 0, the landing on reading 6. -/
private def a : ℕ → Fin 7 := fun n => if n = 0 then 0 else 6

/-- Anchor numerators: the standard opening numerator 1/8, then 17/8. -/
private noncomputable def A : ℕ → ℝ := fun n => if n = 0 then 1 / 8 else 17 / 8

/-- Lap labels at the opening: readings 4 and 5 at lap 1, reading 6 at lap 2. -/
private def J : ℕ → Fin 7 → ℤ :=
  fun n i => if n = 0 then
    (if i.val = 4 then 1 else if i.val = 5 then 1 else if i.val = 6 then 2 else 0) else 0

/-- Final clear laps at the landing time 17/128. -/
private def K : Fin 7 → ℤ :=
  fun i => if i.val = 4 then 1 else if i.val = 5 then 1 else if i.val = 6 then 2 else 0

private theorem hanchor : ∀ n < 1,
    A (n + 1) = ((J n (a (n + 1)) : ℝ) + 1 / 8) := by
  intro n hn
  rcases Nat.lt_one_iff.mp hn with rfl
  simp only [A, J, a, if_true]
  norm_num

private theorem htime : ∀ n < 1,
    A n * x (a (n + 1)) < A (n + 1) * x (a n) := by
  intro n hn
  rcases Nat.lt_one_iff.mp hn with rfl
  simp only [A, a, x, if_true]
  norm_num

private theorem hphase : ∀ n < 1, ∀ i,
    ((J n i : ℝ) - 1 / 8) * x (a n) < A n * x i ∧
      A n * x i ≤ ((J n i : ℝ) + 7 / 8) * x (a n) := by
  intro n hn
  rcases Nat.lt_one_iff.mp hn with rfl
  intro i
  constructor <;> (fin_cases i <;> simp only [J, a, A, x, if_true] <;> norm_num)

private theorem horder : ∀ n < 1, ∀ i,
    ((J n i : ℝ) + 1 / 8) * x (a (n + 1)) ≤ A (n + 1) * x i := by
  intro n hn
  rcases Nat.lt_one_iff.mp hn with rfl
  intro i
  fin_cases i <;> simp only [J, a, A, x, if_true] <;> norm_num

private theorem hfinal : ∀ i,
    ((K i : ℝ) + 1 / 8) * x (a 1) ≤ A 1 * x i ∧
      A 1 * x i ≤ ((K i : ℝ) + 7 / 8) * x (a 1) := by
  intro i
  constructor <;> (fin_cases i <;> simp only [K, a, A, x, if_true] <;> norm_num)

/-- The skeleton fires: from `A 0 / x (a 0)` the reading cascade rises
strictly at step 0, reaches `A 1 / x (a 1)` at step 1, and fixes there. -/
private theorem witness_firing :
    (∀ n < 1, cascadeSeq (Finset.univ.image x) (A 0 / x (a 0)) n <
        cascadeSeq (Finset.univ.image x) (A 0 / x (a 0)) (n + 1)) ∧
    cascadeSeq (Finset.univ.image x) (A 0 / x (a 0)) 1 = A 1 / x (a 1) ∧
    cascadeSeq (Finset.univ.image x) (A 0 / x (a 0)) 2 = A 1 / x (a 1) := by
  have h := first_landing_of_faces x hx a A J 1 hanchor htime hphase horder K hfinal
  dsimp only at h
  have h3 := h.2.2
  norm_num at h3
  exact ⟨h.1, h.2.1, h3.trans h.2.1⟩

private theorem hconv : (1 / 8 : ℝ) / x 0 = A 0 / x (a 0) := by
  simp only [A, a, x, if_true]

private theorem hland : A 1 / x (a 1) = 17 / 128 := by
  simp only [A, a, x]
  norm_num

/-- First certified firing of `first_landing_of_faces` on an explicit
arrangement: the cascade from the standard opening `(1/8)/x 0` makes exactly
one strict move and lands lonely at `17/128`. -/
theorem anchored_landing_witness :
    (∀ n < 1, cascadeSeq (Finset.univ.image x) ((1 / 8) / x 0) n <
        cascadeSeq (Finset.univ.image x) ((1 / 8) / x 0) (n + 1)) ∧
    cascadeSeq (Finset.univ.image x) ((1 / 8) / x 0) 1 = 17 / 128 ∧
    cascadeSeq (Finset.univ.image x) ((1 / 8) / x 0) 2 = 17 / 128 ∧
    LonelyAt (Finset.univ.image x) (17 / 128) := by
  obtain ⟨hinc, heq, hfix⟩ := witness_firing
  rw [hconv]
  refine ⟨hinc, ?_, ?_, ?_⟩
  · rw [heq]
    exact hland
  · rw [hfix]
    exact hland
  · intro d hd
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
    have h1 : ((K i : ℝ) + 1 / 8) ≤ x i * (A 1 / x (a 1)) := by
      rw [← mul_div_assoc, le_div_iff₀ (hx (a 1)), mul_comm (x i)]
      exact (hfinal i).1
    have h2 : x i * (A 1 / x (a 1)) ≤ ((K i : ℝ) + 7 / 8) := by
      rw [← mul_div_assoc, div_le_iff₀ (hx (a 1)), mul_comm (x i)]
      exact (hfinal i).2
    have h := clear_of_window (K i) h1 h2
    rwa [hland] at h

#print axioms anchored_landing_witness

end Fresh.NativeAnchoredLandingWitness
