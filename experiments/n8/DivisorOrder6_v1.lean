import Mathlib

/-!
# Divisor-closed: the real witness converted to an integer one

`DIVISOR_CLOSED_v1.md` proves the reduction (`Rescale.divisor_reduces`): for a divisor-closed
profile every constraint collapses to a unit one, two of the seven readings are free, and what
remains is **five** moduli `b₁..b₅` needing an integer `q` with

```
    b ≤ 8*(q mod b) + 1 ≤ 7b    for each modulus b.
```

Five constraints is an **order-6** question, and order 6 is proved in this tree
(`intLRC_six`, axiom-clean, in-house). Order 6 supplies a **real** `t` with
`dist(t/b, ℤ) ≥ 1/6`. That document records the real→integer conversion as **untried**, with
the slack named: `1/6` against the needed `1/8`.

This file does the conversion. Rounding `t` to the nearest integer moves `q/b` by at most
`1/(2b)`, and the two ends give

```
    left :  b - 3 ≤ 6r   with   8r + 1 ≥ b
    right:  6r ≤ 5b + 3   with   8r + 1 ≤ 7b
```

Those are the **real** bounds, and they are lossy: the residue `r = q - b*m` is an **integer**,
so the right end is `6r ≤ 5b + 3` rather than `r ≤ 5b/6 + 1/2`. Keeping integrality, the
threshold is `b ≥ 10`, not `15` — and it is tight: at `b = 9` the rounding of `t = 15/2` gives
`q = 8`, which is blocked.

That moves the open middle band from `8 ≤ b ≤ 27` down to `8 ≤ b ≤ 9` — from twenty values
to two. The previous `b ≥ 28` came from an order-**7** route whose margin is `1/7 - 1/8 =
1/56`; using order 6 the margin is `1/6 - 1/8 = 1/24`, and the count of surviving constraints
is what licenses order 6.
-/

namespace DivisorOrder6

/-- Reading `sᵢ` is in the way at the candidate `A/sₖ` (same definition as `BlockerCount`). -/
def blocks (si A sk : ℤ) : Prop :=
  min ((si * A) % (8 * sk)) (8 * sk - (si * A) % (8 * sk)) < sk

/-- The unit residue: `(8q+1) mod 8b = 8*(q mod b) + 1`. -/
theorem unit_residue {b q : ℤ} (hb : 0 < b) :
    (1 * (8 * q + 1)) % (8 * b) = 8 * (q % b) + 1 := by
  have hr0 : 0 ≤ q % b := Int.emod_nonneg q hb.ne'
  have hrb : q % b < b := Int.emod_lt_of_pos q hb
  have hq : q = b * (q / b) + q % b := (Int.mul_ediv_add_emod q b).symm
  have key : (1 : ℤ) * (8 * q + 1) = (8 * (q % b) + 1) + (8 * b) * (q / b) := by
    conv_lhs => rw [hq]
    ring
  rw [key, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (by linarith) (by linarith)

/-- **The clear window.**  A unit constraint at modulus `b` is clear exactly when the residue
sits in `[b, 7b]`. -/
theorem not_blocks_iff {b q : ℤ} (hb : 0 < b) :
    ¬ blocks 1 (8 * q + 1) b ↔ (b ≤ 8 * (q % b) + 1 ∧ 8 * (q % b) + 1 ≤ 7 * b) := by
  unfold blocks
  rw [unit_residue hb]
  simp only [not_lt, le_min_iff]
  omega

/-- **The rounding step.**  If `t` lies in the `1/6`-clear band of modulus `b` around `b*m`, and
`b ≥ 10`, then the nearest integer `q` has residue exactly `q - b*m`. -/
theorem residue_of_rounding {b m q : ℤ} (hb : 10 ≤ b) {t : ℝ}
    (hlo : (b : ℝ) * m + (b : ℝ) / 6 ≤ t) (hhi : t ≤ (b : ℝ) * m + 5 * (b : ℝ) / 6)
    (hq : |(q : ℝ) - t| ≤ 1 / 2) : q % b = q - b * m := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : (0:ℤ) < b)
  have h1 : (q : ℝ) - t ≤ 1 / 2 := (abs_le.mp hq).2
  have h2 : -(1 / 2 : ℝ) ≤ (q : ℝ) - t := (abs_le.mp hq).1
  have hcast : (((q - b * m : ℤ)) : ℝ) = (q : ℝ) - (b : ℝ) * m := by push_cast; ring
  have hbR : (10 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  -- keep integrality: 6r is an integer, so these are integer inequalities
  have hL : ((b - 3 : ℤ) : ℝ) ≤ ((6 * (q - b * m) : ℤ) : ℝ) := by push_cast; rw [hcast] at *; linarith
  have hU : ((6 * (q - b * m) : ℤ) : ℝ) ≤ ((5 * b + 3 : ℤ) : ℝ) := by push_cast; rw [hcast] at *; linarith
  have hL' : b - 3 ≤ 6 * (q - b * m) := by exact_mod_cast hL
  have hU' : 6 * (q - b * m) ≤ 5 * b + 3 := by exact_mod_cast hU
  have hge' : 0 ≤ q - b * m := by omega
  have hlt' : q - b * m < b := by omega
  have hsub : (q - b * m) % b = q % b := by
    have hrw : q - b * m = q + b * (-m) := by ring
    rw [hrw, Int.add_mul_emod_self_left]
  rw [← hsub]
  exact Int.emod_eq_of_lt hge' hlt'

/-- **The conversion.**  An order-6 real witness, rounded to the nearest integer, clears every
modulus of size at least `10`. -/
theorem clear_of_order6 {b m q : ℤ} (hb : 10 ≤ b) {t : ℝ}
    (hlo : (b : ℝ) * m + (b : ℝ) / 6 ≤ t) (hhi : t ≤ (b : ℝ) * m + 5 * (b : ℝ) / 6)
    (hq : |(q : ℝ) - t| ≤ 1 / 2) : ¬ blocks 1 (8 * q + 1) b := by
  have hb0 : (0 : ℤ) < b := by omega
  rw [not_blocks_iff hb0, residue_of_rounding hb hlo hhi hq]
  have h1 : (q : ℝ) - t ≤ 1 / 2 := (abs_le.mp hq).2
  have h2 : -(1 / 2 : ℝ) ≤ (q : ℝ) - t := (abs_le.mp hq).1
  have hcast : (((q - b * m : ℤ)) : ℝ) = (q : ℝ) - (b : ℝ) * m := by push_cast; ring
  have hbR : (10 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hL : ((b - 3 : ℤ) : ℝ) ≤ ((6 * (q - b * m) : ℤ) : ℝ) := by push_cast; rw [hcast] at *; linarith
  have hU : ((6 * (q - b * m) : ℤ) : ℝ) ≤ ((5 * b + 3 : ℤ) : ℝ) := by push_cast; rw [hcast] at *; linarith
  have hL' : b - 3 ≤ 6 * (q - b * m) := by exact_mod_cast hL
  have hU' : 6 * (q - b * m) ≤ 5 * b + 3 := by exact_mod_cast hU
  -- Both ends are integer linear arithmetic.  The rational relaxation only closes for b ≥ 15,
  -- so 10 ≤ b ≤ 14 is where integrality of the residue actually does the work; split there.
  by_cases h14 : b ≤ 14
  · interval_cases b <;> omega
  · omega

/-- **The whole profile.**  One real witness in the `1/6` band at every modulus gives one
integer `q` clearing every modulus, provided every modulus is at least `10`. -/
theorem profile_clear_of_order6 {bs : List ℤ} {t : ℝ} (q : ℤ)
    (hq : |(q : ℝ) - t| ≤ 1 / 2)
    (h : ∀ b ∈ bs, 10 ≤ b ∧ ∃ m : ℤ,
          (b : ℝ) * m + (b : ℝ) / 6 ≤ t ∧ t ≤ (b : ℝ) * m + 5 * (b : ℝ) / 6) :
    ∀ b ∈ bs, ¬ blocks 1 (8 * q + 1) b := by
  intro b hb
  obtain ⟨h15, m, hlo, hhi⟩ := h b hb
  exact clear_of_order6 h15 hlo hhi hq

/-- The nearest integer exists, so the hypothesis `|q - t| ≤ 1/2` is never vacuous. -/
theorem exists_rounding (t : ℝ) : ∃ q : ℤ, |(q : ℝ) - t| ≤ 1 / 2 :=
  ⟨round t, by rw [abs_sub_comm]; exact abs_sub_round t⟩

end DivisorOrder6

#print axioms DivisorOrder6.unit_residue
#print axioms DivisorOrder6.not_blocks_iff
#print axioms DivisorOrder6.residue_of_rounding
#print axioms DivisorOrder6.clear_of_order6
#print axioms DivisorOrder6.profile_clear_of_order6
#print axioms DivisorOrder6.exists_rounding
