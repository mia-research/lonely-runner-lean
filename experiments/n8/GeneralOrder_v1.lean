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

end GeneralOrder
