import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Int

/-!
# The modulus seven is totient-full

2026-09-25.  Order seven's residue arguments (Barajas–Serra, `OrderSeven*N.lean`) use one fact
about the modulus `7`, in three forms: a multiple of `7` in a product sits in a factor
(`7 ∣ a·b → 7 ∣ a ∨ 7 ∣ b`), a non-multiple of `7` is coprime to it, and every nonzero residue
mod `7` has an inverse (the multiplier `λ` is chosen from the units, level by level).

All three are the statement that **every nonzero residue mod `7` is a unit**, which is
`φ(7) = 7 − 1`.  It is a finite check (`seven_unit_of_ne_zero`, `totient_seven`), and the term
Mathlib's unit, coprimality and field API is keyed on is derived here from the totient by
`Nat.totient_eq_iff_prime` (`seven_totient_full`) — the reading §16D of the manuscript gives of
`shifted_budget_is_totient`: what does the work is `φ(n) = n − 1`.  Every use in the order-seven
tree goes through the two terms below; none is re-derived from primality.

No global instance is declared here, so the kernel `decide` tables over `ZMod 7` downstream are
not affected.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.OrderSevenN

/-- `φ(7) = 6`: six units mod `7`, the multipliers available at each level. -/
theorem totient_seven : Nat.totient 7 = 6 := by decide

/-- **Every nonzero residue mod `7` is a unit**, by a finite check. -/
theorem seven_unit_of_ne_zero : ∀ a : ZMod 7, a ≠ 0 → ∃ b : ZMod 7, a * b = 1 := by decide

/-- **Seven is totient-full**, `φ(7) = 7 − 1`, in the form Mathlib's API takes it
(`Nat.totient_eq_iff_prime`). -/
theorem seven_totient_full : Nat.Prime 7 :=
  (Nat.totient_eq_iff_prime (by norm_num)).mp totient_seven

/-- The same over `ℤ`: `7 ∣ a·b → 7 ∣ a ∨ 7 ∣ b`, coprimality with non-multiples. -/
theorem seven_totient_full_int : Prime (7 : ℤ) :=
  Nat.prime_iff_prime_int.mp seven_totient_full

end LRC.OrderSevenN
