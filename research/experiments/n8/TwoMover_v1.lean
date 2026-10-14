import Mathlib

/-!
# Two movers: the counting lemma

`docs/n8/WITNESS_MAP_v1.md`, and the `m`-mover ladder of §6.11.  A mover is a reading
`u = p/q` (lowest terms, non-integer); it is **clear** at the opening `A = 8k+1` when
`(p*A) mod 8q ∈ [q, 7q]`.

The reading collapses.  Writing `p = 8s + r` with `r = p % 8`, and using that `k ↦ p*k`
permutes `ZMod q`, the value `(p*(8k+1)) mod 8q` runs exactly over `8*m + r` as `m` runs
over `[0, q)`.  So the allowed set is an **arithmetic progression counted in an interval**,
and everything reduces to `allowed` below.

`card_allowed_two_mul` is the lemma the two-mover step needs: a single mover can never block
more than half of its own period, and it blocks exactly half only when `q = 2`.  That is why
`q = 2` is the sole failing denominator, and why two movers not both of denominator `2`
cannot jointly block every `k`.
-/

namespace TwoMover

/-- The openings a mover with residue `r` and denominator `q` leaves clear, as residues `m`
with reading `8*m + r`. -/
def allowed (r q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun m => q ≤ 8 * m + r ∧ 8 * m + r ≤ 7 * q)

/-- **The allowed set contains an explicit block.**  Every `m` with `(q+7)/8 ≤ m` and
`8*m + r ≤ 7*q` is allowed; this exhibits the block rather than counting around it. -/
theorem Ico_subset_allowed {r q : ℕ} (hr : r < 8) (hq : 0 < q) :
    Finset.Ico ((q - r + 7) / 8) ((7 * q - r) / 8 + 1) ⊆ allowed r q := by
  intro m hm
  rw [Finset.mem_Ico] at hm
  obtain ⟨h1, h2⟩ := hm
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, by omega⟩

/-- **A mover leaves at least half its period clear.**  `q ≤ 2 * |allowed r q|`. -/
theorem card_allowed_two_mul {r q : ℕ} (hr : r < 8) (hq : 2 ≤ q) :
    q ≤ 2 * (allowed r q).card := by
  have hq0 : 0 < q := by omega
  have hsub := Ico_subset_allowed (r := r) (q := q) hr hq0
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hcard
  have key : q ≤ 2 * ((7 * q - r) / 8 + 1 - (q - r + 7) / 8) := by omega
  omega

/-- **Equality only at `q = 2`.**  For `q ≥ 3` a mover leaves strictly more than half clear. -/
theorem card_allowed_lt {r q : ℕ} (hr : r < 8) (hq : 3 ≤ q) :
    q < 2 * (allowed r q).card := by
  have hq0 : 0 < q := by omega
  have hsub := Ico_subset_allowed (r := r) (q := q) hr hq0
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hcard
  have key : q < 2 * ((7 * q - r) / 8 + 1 - (q - r + 7) / 8) := by
    obtain ⟨a, ha⟩ : ∃ a, (7 * q - r) / 8 = a := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, (q - r + 7) / 8 = b := ⟨_, rfl⟩
    have ha1 : 8 * a ≤ 7 * q - r := by omega
    have ha2 : 7 * q - r < 8 * a + 8 := by omega
    have hb1 : 8 * b ≤ q - r + 7 := by omega
    have hb2 : q - r + 7 < 8 * b + 8 := by omega
    rw [ha, hb]
    rcases Nat.lt_or_ge q r with h | h
    · have hz : q - r = 0 := by omega
      omega
    · omega
  omega


/-! ## the two-mover statement is false without an exclusion

Recorded as a **theorem**, not as a `Prop` to be attempted.  `DoorFirstLap` entered
`Spec/Doors.lean` as a `def … : Prop` and was type-checked without ever being proved, so its
falsity went unnoticed; a refutation belongs in the form the checker can hold. -/

/-- A mover `u = p/q` is clear at the opening with numerator `A`. -/
def Clear (p q A : ℕ) : Prop := q ≤ (p * A) % (8 * q) ∧ (p * A) % (8 * q) ≤ 7 * q

instance (p q A : ℕ) : Decidable (Clear p q A) := by unfold Clear; infer_instance

/-- **Unconditional two-mover clearance is false.**  The movers `u₁ = 1/2` and `u₂ = 7/2` have
period `2` in the opening index, and each index is blocked by one of them: `k` even leaves
`u₁` reading `1 (mod 16)`, `k` odd leaves `u₂` reading `15 (mod 16)`, and both are within `1/8`
of an integer.  So no `k` clears both.

This is why Theorem 6.9 extends only under an exclusion, and what Proposition 6.10's
"one off the other's lattice" hypothesis was guarding. -/
theorem two_mover_refuted (k : ℕ) : ¬ (Clear 1 2 (8 * k + 1) ∧ Clear 7 2 (8 * k + 1)) := by
  unfold Clear
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩ <;> subst hm <;> omega

/-- The same, as the failure of the unconditional statement. -/
theorem not_forall_two_mover :
    ¬ (∀ p₁ q₁ p₂ q₂ : ℕ, 2 ≤ q₁ → 2 ≤ q₂ → ∃ k, Clear p₁ q₁ (8*k+1) ∧ Clear p₂ q₂ (8*k+1)) := by
  intro h
  obtain ⟨k, hk⟩ := h 1 2 7 2 (by norm_num) (by norm_num)
  exact two_mover_refuted k hk

end TwoMover

#print axioms TwoMover.Ico_subset_allowed
#print axioms TwoMover.card_allowed_two_mul
#print axioms TwoMover.card_allowed_lt
#print axioms TwoMover.two_mover_refuted
#print axioms TwoMover.not_forall_two_mover
