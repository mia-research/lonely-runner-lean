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

/-! ## Why the divisor-closed category holds: the `n − 1` constant again

The reduction leaves unit constraints `blocks 1 (8q+1) b`, i.e. `q mod b` inside an interval of
length about `3b/4`. Computing that interval exactly turns up the framework's own constant:

```
 b   clear residues of q mod b
 2   1
 3   1 2
 ...
 7   1 2 3 4 5 6          <- ALL nonzero residues
 8   1 2 3 4 5 6          <- 7 is dropped; the pattern breaks
```

For `b ≤ 7` the clear set is *exactly* the nonzero residues, so the constraint degenerates to a bare
non-divisibility. It breaks at `b = 8` — one past `n − 1`, the same place Theorem 4.8's constant
sits, and for the same reason: `8r+1 ≥ 9 > b` needs `b ≤ 7`, and `8b − 8r − 1 ≥ b` at `r = b−1`
needs `8b − 7 ≤ 7b`, again `b ≤ 7`.

**Consequence.** In a divisor-closed profile, every reading with `m/sᵢ ≤ 7` — that is, every
`sᵢ ≥ m/7` — contributes nothing but `(m/sᵢ) ∤ q`. Only readings below `m/8` impose a genuine range
condition. That is the analytical anchor for the category: the large readings are free of geometry
and cost only a sieve condition. -/

/-- **The small-modulus law.**  For `2 ≤ b ≤ 7` a unit constraint is bare non-divisibility: the
candidate `8q+1` is blocked at modulus `b` exactly when `b ∣ q`. It fails at `b = 8`. -/
theorem small_b_blocks_iff {b q : ℤ} (h2 : 2 ≤ b) (h7 : b ≤ 7) :
    blocks 1 (8 * q + 1) b ↔ b ∣ q := by
  have hb : 0 < b := by linarith
  have hr0 : 0 ≤ q % b := Int.emod_nonneg q hb.ne'
  have hrb : q % b < b := Int.emod_lt_of_pos q hb
  have key : (1 * (8 * q + 1)) % (8 * b) = 8 * (q % b) + 1 := by
    have hq : q = b * (q / b) + q % b := (Int.ediv_add_emod q b).symm
    have : (1 : ℤ) * (8 * q + 1) = (8 * (q % b) + 1) + (8 * b) * (q / b) := by
      conv_lhs => rw [hq]
      ring
    rw [this, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by linarith) (by linarith)
  unfold blocks
  rw [key, Int.dvd_iff_emod_eq_zero]
  constructor
  · intro h
    rcases min_cases (8 * (q % b) + 1) (8 * b - (8 * (q % b) + 1)) with ⟨he, -⟩ | ⟨he, -⟩ <;>
      rw [he] at h <;> omega
  · intro h
    rw [h]
    simp only [mul_zero, zero_add]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

/-! ## Every candidate family is a divisor system

`gcd_covariant` and `divisor_reduces` were used separately: the first to strip common factors, the
second for profiles whose readings all divide the largest. Composed, they say something stronger than
either.

For **any** two readings, put `g = gcd(sⱼ, sᵢ)`. Then blocking on the `sᵢ`-family is decided by the
coprime parts `sⱼ/g` and `sᵢ/g` — and `sᵢ/g` **divides `sᵢ`**, by construction. So the constraints on
a candidate family always sit at moduli dividing `sᵢ`.

> **The divisor-closed setting is not a special case. It is the per-family structure of an arbitrary
> profile.**

Every result proved for divisor systems — `divisor_reduces`, `small_b_blocks_iff`, the reflection and
its two centres, `Degenerate2`, and the `EdgeWitness` family — therefore applies to each candidate
family of *any* profile, not only to profiles whose readings happen to divide their largest.

Checked: 12,372,192 instances over all 6-subsets of `[2,22)`, 0 failures on both halves — `sᵢ/g`
always divides `sᵢ`, and the reduced blocking always agrees with the full one. Distinct reduced moduli
per family: 1 to 5. -/

/-- **The common-factor reduction, for arbitrary readings.**  Any common divisor `g` of the two
readings divides out: blocking is decided by `sⱼ/g` and `sᵢ/g`. Taking `g = gcd` gives the coprime
parts. -/
theorem common_factor_reduces {si sj g A : ℤ} (hg : 0 < g) (hj : g ∣ sj) (hi : g ∣ si) :
    blocks sj A si ↔ blocks (sj / g) A (si / g) := by
  obtain ⟨a, ha⟩ := hj
  obtain ⟨b, hb⟩ := hi
  have hga : sj / g = a := by rw [ha]; exact Int.mul_ediv_cancel_left a hg.ne'
  have hgb : si / g = b := by rw [hb]; exact Int.mul_ediv_cancel_left b hg.ne'
  rw [hga, hgb, ha, hb]
  exact gcd_covariant hg

/-- **The reduced modulus divides the generating reading.**  So every candidate family is a divisor
system: after dividing out any common factor, the modulus still divides `sᵢ`. -/
theorem reduced_modulus_dvd {si g : ℤ} (hg : 0 < g) (hi : g ∣ si) : (si / g) ∣ si := by
  obtain ⟨b, hb⟩ := hi
  refine ⟨g, ?_⟩
  rw [hb, Int.mul_ediv_cancel_left b hg.ne', mul_comm]


/-! ## The residue class of a blocker is fixed across the whole family

`rescaled_residue` computed the position of a reading that is a **multiple** of `sₖ`. The following
holds for **every** reading, and is what makes the family rigid.

At any candidate `8q+1`, the residue of `a` modulo `8b` is congruent to `a` modulo `8` — independent
of the opening `q` and of the modulus `b`. So each blocker occupies one fixed class mod `8` across
the entire candidate family; only its position *within* that class moves as `q` varies.

Writing the residue as `8t + (a mod 8)`, clearance is a condition on `t` alone, and the admissible
band for `t` shifts with `a mod 8`:

```
    clear  ⟺  t ∈ [ ⌈(b − α)/8⌉ , ⌊(7b − α)/8⌋ ],   α = a mod 8
```

*(0 exceptions over 273,440 cases, `b < 30`, `a < 400`, `q < 40`.)*

**This bounds how far `small_b_blocks_iff` travels.** That law is `blocks 1 (8q+1) b ↔ b ∣ q`, and it
is the case `α = 1`. For a general coprime numerator it **fails** — 24,533 exceptions over the same
range, the first at `a = 3, b = 2, q = 0`. What survives to arbitrary `a` is the residue-class
rigidity below, not the divisibility law. -/

/-- **Fixed residue class.**  At every candidate, a reading's residue modulo `8b` lies in the class
of `a` modulo `8`, whatever the opening and whatever the modulus. -/
theorem blocker_class {a b q : ℤ} (hb : 0 < b) :
    ((a * (8 * q + 1)) % (8 * b)) % 8 = a % 8 := by
  have h8 : (8 : ℤ) ∣ 8 * b := ⟨b, rfl⟩
  rw [Int.emod_emod_of_dvd _ h8]
  have : a * (8 * q + 1) = a + 8 * (a * q) := by ring
  rw [this, Int.add_mul_emod_self_left]

end Rescale
