import LonelyRunner.LRC.Spec.OverlapFlankN

/-!
# The divisible flank, with the lonely point named from the arithmetic

2026-09-24.  Let `n ∣ e`, `e = n·E`.  For `k < n` the opening `j = k·E` is the instant

    t_k = k/n + 1/(n e).

When `k` is a unit mod `n`, `k/n` is a moment of global isolation of the ideal: the equally spaced
speeds `0, 1, …, n − 1` stand one to each `n`-th there, and every disparity not divisible by `n`
is already clear.  `t_k` is that moment pushed forward by exactly `1/(n e)`, the amount that puts
the flank on the boundary.  The only question is whether the push carries some other runner into
the zone.

Write `k ≡ −u⁻¹ (mod n)` for a unit `u`.  A disparity `d = q·e + r` not divisible by `n` reads
`e·((d·k + q) mod n) + r` at `t_k`, and multiplying `d·k + q` by `−u` shows

    d·k + q ≡ 0      ⟺   d ≡ q·u        (mod n),
    d·k + q ≡ −1     ⟺   d ≡ (q + 1)·u  (mod n).

So `d` is carried into the zone exactly when it **hits** `u` in one of these two ways; a disparity
below the flank (`q = 0`) hits only `u ≡ d`.  If some unit `u` is hit by no disparity, and every
other multiple of `n` is clear at `j = 0`, the flank's certificate is exhibited at the named point
`k ≡ −u⁻¹` (`flankWorks_of_unhit_unit`).  No counting is used.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.Resonance

open Flanks MomentIterationN LRC.SpecN LRC.FlankFinite

variable {n : ℕ} [Fact (2 ≤ n)]

/-- **The named point, given `k` with `u·k ≡ −1`.**  If no disparity not divisible by `n` hits
`u` — that is, `d ≢ ⌊d/e⌋·u` and `d ≢ (⌊d/e⌋ + 1)·u (mod n)` — then the shift `k` is free, and the
flank `e` hosts a lonely opening there. -/
theorem flankWorks_of_unhit (L : List ℕ) (e : ℕ) (he : 0 < e) (hen : n ∣ e)
    (hmult : ∀ d ∈ L, n ∣ d → e ≤ d % (n * e) ∧ d % (n * e) ≤ (n - 1) * e)
    (u k : ℕ) (hkn : k < n) (huk : n ∣ u * k + 1)
    (hunhit : ∀ d ∈ L, ¬ n ∣ d →
      d % n ≠ (d / e * u) % n ∧ d % n ≠ ((d / e + 1) * u) % n) :
    flankWorks n (e :: L) e = true := by
  have hn2 : 2 ≤ n := Fact.out
  refine flankWorks_of_free_shift L e he hen hmult k hkn fun d hdL hnd => ⟨?_, ?_⟩
  · intro h
    apply (hunhit d hdL hnd).1
    have h1 : (n : ℤ) ∣ (d : ℤ) * k + (d / e : ℕ) := by
      have := Nat.dvd_of_mod_eq_zero h
      exact_mod_cast this
    have h2 : (n : ℤ) ∣ (u : ℤ) * k + 1 := by exact_mod_cast huk
    have h3 : (n : ℤ) ∣ ((d / e * u : ℕ) : ℤ) - (d : ℤ) := by
      have := dvd_sub (dvd_mul_of_dvd_right h1 (u : ℤ)) (dvd_mul_of_dvd_right h2 (d : ℤ))
      have heq : (u : ℤ) * ((d : ℤ) * k + (d / e : ℕ)) - (d : ℤ) * ((u : ℤ) * k + 1)
          = ((d / e * u : ℕ) : ℤ) - (d : ℤ) := by push_cast; ring
      rwa [heq] at this
    exact Nat.modEq_iff_dvd.mpr h3
  · intro h
    apply (hunhit d hdL hnd).2
    have h1n : n ∣ d * k + d / e + 1 := by
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod, h, Nat.mod_eq_of_lt (show 1 < n by omega),
        Nat.sub_add_cancel (by omega), Nat.mod_self]
    have h1 : (n : ℤ) ∣ (d : ℤ) * k + (d / e : ℕ) + 1 := by exact_mod_cast h1n
    have h2 : (n : ℤ) ∣ (u : ℤ) * k + 1 := by exact_mod_cast huk
    have h3 : (n : ℤ) ∣ (((d / e + 1) * u : ℕ) : ℤ) - (d : ℤ) := by
      have := dvd_sub (dvd_mul_of_dvd_right h1 (u : ℤ)) (dvd_mul_of_dvd_right h2 (d : ℤ))
      have heq : (u : ℤ) * ((d : ℤ) * k + (d / e : ℕ) + 1) - (d : ℤ) * ((u : ℤ) * k + 1)
          = (((d / e + 1) * u : ℕ) : ℤ) - (d : ℤ) := by push_cast; ring
      rwa [heq] at this
    exact Nat.modEq_iff_dvd.mpr h3

/-- **The named point, from the unit alone.**  If `u` is a unit mod `n` hit by no disparity not
divisible by `n`, and every other multiple of `n` is clear at `j = 0`, the flank `e` hosts a lonely
opening at `t = k/n + 1/(n e)` with `k ≡ −u⁻¹ (mod n)`: the ideal's moment of global isolation
`k/n`, pushed forward by `1/(n e)`. -/
theorem flankWorks_of_unhit_unit (L : List ℕ) (e : ℕ) (he : 0 < e) (hen : n ∣ e)
    (hmult : ∀ d ∈ L, n ∣ d → e ≤ d % (n * e) ∧ d % (n * e) ≤ (n - 1) * e)
    (u : ℕ) (hu : Nat.Coprime u n)
    (hunhit : ∀ d ∈ L, ¬ n ∣ d →
      d % n ≠ (d / e * u) % n ∧ d % n ≠ ((d / e + 1) * u) % n) :
    flankWorks n (e :: L) e = true := by
  have hn2 : 2 ≤ n := Fact.out
  haveI : NeZero n := ⟨by omega⟩
  set k : ℕ := (-((u : ZMod n)⁻¹)).val with hk
  have hkn : k < n := ZMod.val_lt _
  have huk : n ∣ u * k + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hk, ZMod.natCast_zmod_val, mul_neg, ZMod.coe_mul_inv_eq_one u hu]
    ring
  exact flankWorks_of_unhit L e he hen hmult u k hkn huk hunhit

/-- The worked set `{1, 4, 5, 6}` at order five: the unit `u = 2` is hit by nothing, so the named
point `k = 2`, `t = 11/25`, is lonely at the flank `5`. -/
example : flankWorks 5 [5, 1, 4, 6] 5 = true := by
  haveI : Fact (2 ≤ 5) := ⟨by norm_num⟩
  refine flankWorks_of_unhit_unit [1, 4, 6] 5 (by norm_num) (dvd_refl 5) ?_ 2 (by norm_num) ?_
  · intro d hd hnd; simp at hd; omega
  · intro d hd _; simp at hd; rcases hd with rfl | rfl | rfl <;> decide

end LRC.Resonance
