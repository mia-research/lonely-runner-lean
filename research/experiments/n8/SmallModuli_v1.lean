import Mathlib

/-!
# The small-modulus end, and the reach of a single candidate

`DivisorOrder6` closes divisor-closed profiles whose every quotient is at least `10`, leaving
`b ∈ {8,9}` as the residual of the old `8 ≤ b ≤ 27` band. The other end closes outright.

A candidate `q` clears modulus `b` when `b ≤ 8*(q mod b) + 1 ≤ 7b`. Since
`L(b) = ⌈(b-1)/8⌉ = 1` for every `2 ≤ b ≤ 9`, the single candidate **`q = 1`** clears every
modulus in that range at once — so a profile all of whose quotients are at most `9` needs no
witness search at all.

More generally a single `q` reaches a **ratio-7 window** of moduli: taking `0 < q < b`, the
clear condition is `b ≤ 8q+1 ≤ 7b`, i.e.

```
    (8q+1)/7  ≤  b  ≤  8q+1 .
```

That is the `n-1 = 7` constant appearing as the reach of one candidate, and it is why profiles
whose moduli span more than a factor of seven are the ones that need a witness argument.
-/

namespace SmallModuli

/-- The clear window at modulus `b`, in the residue `r`. -/
def clearAt (b r : ℤ) : Prop := b ≤ 8 * r + 1 ∧ 8 * r + 1 ≤ 7 * b

/-- `q = 1` has residue `1` at every modulus `b ≥ 2`. -/
theorem one_emod {b : ℤ} (hb : 2 ≤ b) : (1 : ℤ) % b = 1 :=
  Int.emod_eq_of_lt (by omega) (by omega)

/-- **`q = 1` clears every modulus up to 9.**  This is exactly the range where `L(b) = 1`. -/
theorem clear_one {b : ℤ} (h2 : 2 ≤ b) (h9 : b ≤ 9) : clearAt b (1 % b) := by
  rw [one_emod h2]
  constructor <;> omega

/-- **And it fails from 10 on**, so the bound `9` is the exact reach of `q = 1`. -/
theorem clear_one_fails {b : ℤ} (hb : 10 ≤ b) : ¬ clearAt b (1 % b) := by
  rw [one_emod (by omega)]
  unfold clearAt
  omega

/-- **A homogeneous small profile needs no search.**  If every modulus of the profile is at
most `9`, the single candidate `q = 1` clears all of them. -/
theorem profile_clear_one {bs : List ℤ} (h : ∀ b ∈ bs, 2 ≤ b ∧ b ≤ 9) :
    ∀ b ∈ bs, clearAt b (1 % b) := by
  intro b hb
  exact clear_one (h b hb).1 (h b hb).2

/-- **The reach of one candidate is a ratio-7 window.**  For `0 < q < b` the residue is `q`
itself, so clearing is the two-sided bound `(8q+1)/7 ≤ b ≤ 8q+1`, stated without division. -/
theorem reach_window {b q : ℤ} (hq : 0 < q) (hqb : q < b) :
    clearAt b (q % b) ↔ (b ≤ 8 * q + 1 ∧ 8 * q + 1 ≤ 7 * b) := by
  rw [Int.emod_eq_of_lt (by omega) hqb]
  rfl

/-- **One candidate covers every modulus in its window.**  If all moduli lie between
`(8q+1)/7` and `8q+1` — written multiplicatively — then `q` clears the whole profile. -/
theorem profile_clear_of_window {bs : List ℤ} {q : ℤ} (hq : 0 < q)
    (h : ∀ b ∈ bs, q < b ∧ b ≤ 8 * q + 1 ∧ 8 * q + 1 ≤ 7 * b) :
    ∀ b ∈ bs, clearAt b (q % b) := by
  intro b hb
  obtain ⟨hlt, h1, h2⟩ := h b hb
  exact (reach_window hq hlt).mpr ⟨h1, h2⟩

end SmallModuli

#print axioms SmallModuli.one_emod
#print axioms SmallModuli.clear_one
#print axioms SmallModuli.clear_one_fails
#print axioms SmallModuli.profile_clear_one
#print axioms SmallModuli.reach_window
#print axioms SmallModuli.profile_clear_of_window
