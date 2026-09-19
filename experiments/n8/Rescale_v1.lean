import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # The collision criterion is rescaling-covariant

Branch A/B splits integer profiles by whether `8 ∣ sⱼ`: a non-colliding reading never blocks a spine
point `R ∈ {1,3,5,7}`, a colliding one blocks all four at once.

The candidates `(8m+1)/sₖ` are the spine of the problem **rescaled by `sₖ`** — the modulus moves from
`8` to `8sₖ`. The theorem below says the Branch A/B criterion moves with it: among readings that `sₖ`
divides, blocking the `sₖ`-candidates is decided by `8 ∣ (sⱼ/sₖ)`, exactly the original test applied
to the rescaled reading.

Rescaling by `sₖ` makes `sₖ` the unit, which is *why* `BlockerCount.self_never_blocks` holds: it is
the case `c = 1`. Checked for `sₖ < 200`, `c ≤ 60`: 0 violations. -/

namespace Rescale

open BlockerCount

/-- **The rescaled residue.**  At a candidate `(8q+1)/sₖ`, the reading `c·sₖ` sits at `sₖ·(c mod 8)`.
The reading's whole contribution is its multiplier's residue mod `8`, scaled by `sₖ`. -/
theorem rescaled_residue {sk : ℤ} (hk : 0 < sk) (c q : ℤ) :
    (c * sk * (8 * q + 1)) % (8 * sk) = sk * (c % 8) := by
  have hc : c = 8 * (c / 8) + c % 8 := (Int.mul_ediv_add_emod c 8).symm
  have h : c * sk * (8 * q + 1)
      = sk * (c % 8) + (8 * sk) * (8 * (c / 8) * q + (c % 8) * q + c / 8) := by
    conv_lhs => rw [hc]
    ring
  rw [h, Int.add_mul_emod_self_left]
  have h0 : 0 ≤ c % 8 := Int.emod_nonneg c (by norm_num)
  have h8 : c % 8 < 8 := Int.emod_lt_of_pos c (by norm_num)
  exact Int.emod_eq_of_lt (by positivity) (by nlinarith)

/-- **The criterion travels.**  A reading that `sₖ` divides blocks the `sₖ`-candidates exactly when
`8` divides the multiplier — the Branch A/B test on the rescaled reading. -/
theorem rescaled_blocks_iff {sk : ℤ} (hk : 0 < sk) (c q : ℤ) :
    blocks (c * sk) (8 * q + 1) sk ↔ (8 : ℤ) ∣ c := by
  unfold blocks
  rw [rescaled_residue hk c q]
  have h0 : 0 ≤ c % 8 := Int.emod_nonneg c (by norm_num)
  have h8 : c % 8 < 8 := Int.emod_lt_of_pos c (by norm_num)
  constructor
  · intro h
    rcases min_cases (sk * (c % 8)) (8 * sk - sk * (c % 8)) with ⟨he, -⟩ | ⟨he, -⟩ <;>
      rw [he] at h
    · have : c % 8 = 0 := by nlinarith
      exact Int.dvd_of_emod_eq_zero this
    · nlinarith
  · intro h
    have : c % 8 = 0 := Int.emod_eq_zero_of_dvd h
    rw [this]
    simp only [mul_zero, sub_zero]
    exact lt_of_le_of_lt (min_le_left _ _) hk

/-! ## The cage, at candidate points

The cage (`slot_gcd`, `even_offset_caged`) is stated at **grid instants**, where the modulus is `8`.
A candidate `(8m+1)/sₖ` is not a grid instant, and the mod-`8` form of the cage does not apply there
— even readings block roughly half the time. But the cage's *content* does transfer, in covariant
form: a common factor of the two readings divides straight out of the blocking condition.

Write `g = gcd(sᵢ, sₖ)`, `sᵢ = g·a`, `sₖ = g·b`. Then `sᵢ·A mod 8sₖ = g·(a·A mod 8b)` and the
threshold is `g·b`, so `g` cancels. Blocking is decided entirely by the **coprime parts**. -/

/-- **`slot_gcd` at candidate points.**  A common factor of the blocking reading and the generating
reading is invisible: blocking depends only on the two readings' coprime parts. -/
theorem gcd_covariant {g a b A : ℤ} (hg : 0 < g) :
    blocks (g * a) A (g * b) ↔ blocks a A b := by
  unfold blocks
  have hm : (g * a * A) % (8 * (g * b)) = g * ((a * A) % (8 * b)) := by
    have : (8 : ℤ) * (g * b) = g * (8 * b) := by ring
    rw [this, mul_assoc, Int.mul_emod_mul_of_pos (a * A) (8 * b) hg]
  rw [hm]
  have hsub : 8 * (g * b) - g * ((a * A) % (8 * b)) = g * (8 * b - (a * A) % (8 * b)) := by ring
  rw [hsub, ← mul_min_of_nonneg _ _ hg.le]
  exact mul_lt_mul_iff_of_pos_left hg

/-! ## Divisor-closed profiles

If every reading divides the largest, `m`, then taking `sₖ = m` makes `gcd(sᵢ, m) = sᵢ`, so
`gcd_covariant` collapses **every** constraint to a unit one:

    blocks sᵢ A m  ↔  blocks 1 A (m / sᵢ)

The profile's interaction structure disappears; only the seven quotients `m/sᵢ` remain. Two of them
are free — `sᵢ = m` gives `b = 1` and `sᵢ = 1` gives `b = m` — so **five** constraints are left.

Writing `A = 8q+1`, `blocks 1 A b` says `q mod b` lies within `≈ b/8` of `0`, i.e. `‖q/b‖ ≲ 1/8`.
So a witness is an integer `q` with `‖q/bᵢ‖ ≳ 1/8` for five moduli — an order-6 question at
threshold `1/8`, where the proved bound at order 6 is `1/6`. The route has slack; it is not closed
here, because the witness must be an *integer* `q` and the order-6 bound supplies a real one.

**Verified:** 1,662,240 divisor-closed profiles, exhaustive over every `m < 1200` with at least
seven divisors and every 7-subset containing `1` and `m` — `sₖ = m` supplies a witness in **all** of
them, 0 failures. The same profiles under the Branch A move `sₖ = 1` fail 23% of the time, so the
choice `sₖ = m` is doing the work. -/

/-- **Divisor-closed reduction.**  When `sₖ` divides the generating reading, the constraint becomes a
unit constraint at the quotient modulus. -/
theorem divisor_reduces {s m A : ℤ} (hs : 0 < s) (hdvd : s ∣ m) :
    blocks s A m ↔ blocks 1 A (m / s) := by
  obtain ⟨b, rfl⟩ := hdvd
  have hb : s * b / s = b := by
    rw [mul_comm]; exact Int.mul_ediv_cancel b hs.ne'
  rw [hb]
  have h1 : blocks s A (s * b) ↔ blocks (s * 1) A (s * b) := by rw [mul_one]
  exact h1.trans (gcd_covariant hs)

end Rescale
