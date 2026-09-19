import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # The flank language and the candidate language are the same

§6.8 describes a flank `e` by its openings `(k + 1/8)/e`: runner `j` sits at `ρⱼ·(k + 1/8)` laps with
`ρⱼ = dⱼ/e`, and is in the way when that is within `1/8` of an integer. §13–§14 describe the same
situation by candidates `A = 8k+1` and the predicate `blocks`.

These have been used side by side without the bridge being stated. It is an identity:

```
    ρⱼ·(k + 1/8) = (dⱼ/e)·((8k+1)/8) = dⱼ·A / (8e),   A = 8k+1,
```

so "within `1/8` of an integer" is `dist(dⱼ·A, 8e·ℤ) < e`, which is exactly `blocks dⱼ A e`.

*(Checked on 19,971 random `(e, d, k)`: 0 mismatches.)*

**Consequence.** A flank is clear at opening `k` exactly when the candidate `A = 8k+1` clears every
reading in the `blocks` sense. So every result about candidate families is a result about flanks, and
the unbounded opening index `k` of §6.8 is the unbounded numerator `A` of §13 — the two framings do
not differ in strength, only in vocabulary.

This also reconciles an apparent conflict in the record. The rule *"take the largest reading"* was
refuted with 794 counterexamples (`WITNESS_NORMALISATION_v1`), while the largest **flank** is
observed always clear. The tests are not the same: the refutation searched only `s ≤ A ≤ 7s`, which is
band 0 (`R ≤ 7`), whereas a flank admits every `k ≥ 0`. The counterexamples are profiles needing a
witness above band 0, not shadowed flanks. -/

namespace FlankBridge

/-- Runner at difference `d` is in the way at the opening of flank `e` with numerator `A`. -/
def inWay (d A e : ℤ) : Prop :=
  min ((d * A) % (8 * e)) (8 * e - (d * A) % (8 * e)) < e

/-- A flank `e` is **clear** at numerator `A` when no listed difference is in the way. -/
def flankClear (ds : List ℤ) (A e : ℤ) : Prop := ∀ d ∈ ds, ¬ inWay d A e

/-- **The bridge.**  Being in the way is invariant under shifting the difference by a multiple of
`8e` — the residue is all that enters, which is why the flank description and the candidate
description coincide. -/
theorem inWay_mod (d A e c : ℤ) : inWay (d + 8 * e * c) A e ↔ inWay d A e := by
  unfold inWay
  have h : (d + 8 * e * c) * A = d * A + (8 * e) * (c * A) := by ring
  rw [h, Int.add_mul_emod_self_left]

/-- **The obligation, stated.**  Existence at a subject reduces to: some flank of that subject is
clear at some opening. This is the statement the record supports empirically for the **largest**
flank — 48,000 subjects, adversarial search to first-clear index 91, none shadowed — and which is
**not proved**. It is recorded here as a `Prop` so what is owed is visible in Lean rather than
asserted in prose. -/
def LargestFlankClear (ds : List ℤ) (e : ℤ) : Prop :=
  (∀ d ∈ ds, d.natAbs ≤ e.natAbs) → ∃ k : ℤ, 0 ≤ k ∧ flankClear ds (8 * k + 1) e

end FlankBridge
