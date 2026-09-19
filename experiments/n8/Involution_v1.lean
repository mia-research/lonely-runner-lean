import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # The reflection, and the two residues that obstruct it

After `Rescale.divisor_reduces`, a divisor-closed profile is clear exactly when some integer `q`
satisfies, for each quotient `b`, the *exact* condition

    b ≤ 8·(q mod b) + 1 ≤ 7b.

No reals and no rounding enter: the candidate is `(8q+1)/(8m)` and the test is an integer
congruence, so the whole question lives in `ℤ`.

That condition carries a reflection `r ↦ b − r`, and the reflection is obstructed by exactly two
residues. Clearing at `r` says `8r ∈ [b−1, 7b−1]`; clearing at `b−r` says `8r ∈ [b+1, 7b+1]`. The two
ranges differ only if a multiple of `8` lands in `{b−1, b}` or in `{7b, 7b+1}` — that is, iff
`b ≡ 0 (mod 8)` or `b ≡ 1 (mod 8)`.

**Those are the framework's two distinguished residues**: `b ≡ 0` is the collision condition that
splits Branch A from Branch B, and `b ≡ 1` is the guard relation `s·R ≡ 1 (mod 8)`. The reflection
survives on the whole band `b mod 8 ∈ [2,7]` and nowhere else. Verified exactly for `b < 5000`. -/

namespace Involution

/-- Clearing at modulus `b`, stated on the residue: the candidate `8r+1` must sit in `[b, 7b]`. -/
def clearAt (b r : ℤ) : Prop := b ≤ 8 * r + 1 ∧ 8 * r + 1 ≤ 7 * b

/-- **The reflection holds off the two residues.**  For `b mod 8 ∈ [2,7]`, clearing is invariant
under `r ↦ b − r`. -/
theorem clear_reflect {b r : ℤ} (h2 : 2 ≤ b % 8) :
    clearAt b r ↔ clearAt b (b - r) := by
  obtain ⟨k, c, hk, hc2, hc7⟩ : ∃ k c, b = 8 * k + c ∧ 2 ≤ c ∧ c ≤ 7 :=
    ⟨b / 8, b % 8, by have := Int.mul_ediv_add_emod b 8; omega, h2,
     by have := Int.emod_lt_of_pos b (by norm_num : (0:ℤ) < 8); omega⟩
  subst hk
  unfold clearAt
  interval_cases c <;> omega

/-- **`b ≡ 0 (mod 8)` obstructs it.**  The collision residue: `r = b/8` clears but its reflection
does not. -/
theorem reflect_fails_zero {b : ℤ} (hb : 0 < b) (h : b % 8 = 0) :
    clearAt b (b / 8) ∧ ¬ clearAt b (b - b / 8) := by
  have hd := Int.mul_ediv_add_emod b 8
  unfold clearAt
  omega

/-- **`b ≡ 1 (mod 8)` obstructs it.**  The guard residue: `r = (b−1)/8` clears but its reflection
does not. -/
theorem reflect_fails_one {b : ℤ} (hb : 0 < b) (h : b % 8 = 1) :
    clearAt b ((b - 1) / 8) ∧ ¬ clearAt b (b - (b - 1) / 8) := by
  have hd := Int.mul_ediv_add_emod (b - 1) 8
  have h1 : (b - 1) % 8 = 0 := by omega
  unfold clearAt
  omega

end Involution
