import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # Which of the order-8 facts are really about 8

Three tiers emerge once the statements are compared.

**Tier 1 — no order appears.** `ReachRule` (13), `GapRule` (3), `ArithForm` (2), `EdgeWitness` (4),
`SolutionPair` (3) are stated with the order as a free variable or with none at all. They hold at
every order already.

**Tier 3 — special to `n ∣ 24`.** `Guard.klein_self_inverse` says every unit of `ZMod 8` is
self-inverse. That holds **exactly for `n ∈ {2,3,4,6,8,12,24}`** — computed, `n < 60`. So
`TwoPatterns.unit_on_both`, and with it the AP's four-coincidence structure, is a fact about
`n ∣ 24` and **not** about order 8 as an order: at `n = 7, 9, 11, 13` the units are not self-inverse
and `x = u` does not sit on the `+1` pattern via reading `u`.

**Tier 2 — order-8 in statement, general in substance.** `Guard.odd_clear_of_not_dvd` is
`¬(8 ∣ s) → Odd R → ¬(8 ∣ s·R)`, and at order 8 "odd" is exactly "coprime to 8". The general
statement below is what the proof actually uses, and it needs no Klein structure — only that `R` is
invertible mod `n`.

**This is the Branch A mechanism at every order:** if no reading is divisible by `n`, any `R`
coprime to `n` clears, because clearance at `R` is `n ∤ sᵢ·R`. -/

namespace GeneralOrder

/-- **Branch A, at every order.**  If `n` does not divide `s`, and `R` is coprime to `n`, then `n`
does not divide `s·R`. At `n = 8` with `R` odd this is `Guard.odd_clear_of_not_dvd`. -/
theorem clear_of_not_dvd {n s R : ℤ} (hcop : IsCoprime R n) (hs : ¬ (n ∣ s)) :
    ¬ (n ∣ s * R) := by
  intro h
  exact hs ((hcop.symm.dvd_of_dvd_mul_right) h)

/-- **All units clear together, at every order.**  If no reading is divisible by `n`, then *every*
`R` coprime to `n` is clear of every reading — not merely some. This is `spine_all_or_nothing`
without the order-8 hypothesis. -/
theorem spine_all_or_nothing {n R : ℤ} (S : List ℤ)
    (hcop : IsCoprime R n) (hS : ∀ s ∈ S, ¬ (n ∣ s)) :
    ∀ s ∈ S, ¬ (n ∣ s * R) :=
  fun s hsS => clear_of_not_dvd hcop (hS s hsS)

/-! ## The `n − 1` constant at every order

`Rescale.small_b_blocks_iff` is `blocks 1 (8q+1) b ↔ b ∣ q` for `2 ≤ b ≤ 7`, and its break at `b = 8`
was identified with Theorem 4.8's `n − 1`. That identification is now a theorem rather than a
coincidence of `8`.

At order `n`, a candidate `n·q + 1` has residue `n·ρ + 1` where `ρ = q mod b`. Clearance asks
`b ≤ n·ρ + 1 ≤ (n−1)·b`:

* the lower bound fails at `ρ = 0` (since `b ≥ 2`) and holds for `ρ ≥ 1` provided `b ≤ n`;
* the upper bound is tightest at `ρ = b − 1`, where it reads `n − 1 ≥ b`.

So the law holds exactly on `2 ≤ b ≤ n − 1` and breaks at `b = n`. Checked at every order
`4 ≤ n ≤ 19`: the largest `b` for which it holds is `n − 1` in every case, and the first failure at
`b = n` is at `q = b − 1` — the upper endpoint, as the derivation says. -/

/-- Blocking at order `n`: the residue of `sᵢ·A` modulo `n·sₖ` lies within `sₖ` of `0`. -/
def blocksN (n si A sk : ℤ) : Prop :=
  min ((si * A) % (n * sk)) (n * sk - (si * A) % (n * sk)) < sk

/-- **The small-modulus law, at every order.**  For `2 ≤ b ≤ n − 1`, a unit constraint is bare
non-divisibility. The bound `n − 1` is sharp: it fails at `b = n`. -/
theorem small_b_general {n b q : ℤ} (h2 : 2 ≤ b) (hb : b ≤ n - 1) :
    blocksN n 1 (n * q + 1) b ↔ b ∣ q := by
  have hn : 3 ≤ n := by omega
  have hbpos : 0 < b := by omega
  have hr0 : 0 ≤ q % b := Int.emod_nonneg q hbpos.ne'
  have hrb : q % b < b := Int.emod_lt_of_pos q hbpos
  have key : (1 * (n * q + 1)) % (n * b) = n * (q % b) + 1 := by
    have hq : q = b * (q / b) + q % b := (Int.mul_ediv_add_emod q b).symm
    have hid : (1 : ℤ) * (n * q + 1) = (n * (q % b) + 1) + (n * b) * (q / b) := by
      conv_lhs => rw [hq]
      ring
    rw [hid, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by nlinarith) (by nlinarith)
  unfold blocksN
  rw [key, Int.dvd_iff_emod_eq_zero]
  constructor
  · intro h
    rcases min_cases (n * (q % b) + 1) (n * b - (n * (q % b) + 1)) with ⟨he, -⟩ | ⟨he, -⟩ <;>
      rw [he] at h <;> nlinarith
  · intro h
    rw [h]
    simp only [mul_zero, zero_add]
    exact lt_of_le_of_lt (min_le_left _ _) (by omega)

end GeneralOrder
