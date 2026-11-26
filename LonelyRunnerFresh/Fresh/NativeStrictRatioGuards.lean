import Fresh.NativeHistoryRatioPaths

namespace Fresh.NativeStrictRatioGuards

/-- A comparison records whether its boundary is included. -/
-- STANDING: DEFINITION
def Holds (strict : Bool) (x y : ℝ) : Prop :=
  if strict then x < y else x ≤ y

/-- A product of two positive-ratio guards is strict when either
factor guard is strict. -/
theorem compose {x y z a b : ℝ} (hb : 0 < b)
    (p q : Bool) (h₁ : Holds p y (a * x)) (h₂ : Holds q z (b * y)) :
    Holds (p || q) z ((b * a) * x) := by
  cases p <;> cases q <;> simp [Holds] at h₁ h₂ ⊢
  · exact h₂.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h₁ hb.le)
  · exact h₂.trans_le (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h₁ hb.le)
  · exact h₂.trans_lt (by simpa only [mul_assoc] using mul_lt_mul_of_pos_left h₁ hb)
  · exact h₂.trans (by simpa only [mul_assoc] using mul_lt_mul_of_pos_left h₁ hb)

/-- A smaller factor implies either kind of guard on positive
readings. At equal factors, only the strict guard implies strictness. -/
theorem weaken {x y a b : ℝ} (hx : 0 < x) (p q : Bool)
    (h : Holds p y (a * x))
    (hf : a < b ∨ a = b ∧ (q = true → p = true)) :
    Holds q y (b * x) := by
  rcases hf with hlt | ⟨rfl, he⟩
  · have hle : y ≤ a * x := by cases p <;> simp [Holds] at h <;> linarith
    have ht := hle.trans_lt (mul_lt_mul_of_pos_right hlt hx)
    cases q <;> simp [Holds, ht, ht.le]
  · cases q
    · cases p <;> simp [Holds] at h ⊢ <;> linarith
    · have hp : p = true := he rfl
      subst p
      exact h

/-- A path retains its positive product and whether any factor
comparison was strict. -/
inductive Path {ι : Type*} (edge : ι → ι → ℝ → Bool → Prop) :
    ι → ι → ℝ → Bool → Prop where
  | refl (i : ι) : Path edge i i 1 false
  | edge {i j a p} (ha : 0 < a) (h : edge i j a p) : Path edge i j a p
  | trans {i j k a b p q} (h₁ : Path edge i j a p) (h₂ : Path edge j k b q) :
      Path edge i k (b * a) (p || q)

/-- Every retained path proves the corresponding guard, including
the strictness required to distinguish closed capture boundaries. -/
theorem path_sound {ι : Type*} {edge : ι → ι → ℝ → Bool → Prop}
    (r : ι → ℝ) (he : ∀ i j a p, edge i j a p → Holds p (r j) (a * r i))
    {i j a p} (h : Path edge i j a p) :
    0 < a ∧ Holds p (r j) (a * r i) := by
  induction h with
  | refl i => simp [Holds]
  | edge hp h => exact ⟨hp, he _ _ _ _ h⟩
  | trans _ _ h₁ h₂ => exact ⟨mul_pos h₂.1 h₁.1, compose h₂.1 _ _ h₁.2 h₂.2⟩

/-- A retained path permits deletion of a guard with a weaker factor
or an included equality face. -/
theorem entailed {ι : Type*} {edge : ι → ι → ℝ → Bool → Prop}
    (r : ι → ℝ) (he : ∀ i j a p, edge i j a p → Holds p (r j) (a * r i))
    {i j : ι} {a b : ℝ} {p q : Bool} (hi : 0 < r i)
    (h : Path edge i j a p) (hf : a < b ∨ a = b ∧ (q = true → p = true)) :
    Holds q (r j) (b * r i) :=
  weaken hi p q (path_sound r he h).2 hf

#print axioms entailed
#print axioms path_sound
#print axioms compose
#print axioms weaken

end Fresh.NativeStrictRatioGuards
