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

/-! ## The largest flank excludes the dominant shadowing mode

The configuration that refuted the `|J| = 3` reduction was **two half-movers on opposite parities**:
a mover with fractional part `1/2` is bad on at most one parity class of `k`, and two covering
complementary classes shadow the flank whatever else is present.

At the **largest** flank that configuration cannot occur, and the reason is forced by `|d| ≤ e`.

A mover there has `|ρ| < 1`, so if `ρ = w + 1/2` then `w + 1/2 ∈ (−1,1)`, giving `w ∈ (−3/2, 1/2)`
and hence `w ∈ {−1, 0}`. Both reduce to `w mod 8 ∈ {0, 7}`, and **both block even `k`**. No mover at
the largest flank blocks odd `k` by way of a half fractional part.

**Measured:** 160,000 largest flanks carrying 1,612 half-movers — **0** with half-movers on opposite
parities. At the *smallest* flank of the same arrangements: **2,069**. -/

/-- **Phase pinning at the largest flank.**  A half-mover there has whole part `0` or `−1`. -/
theorem half_mover_whole {d e w : ℤ} (he : 0 < e) (hlt : d < e) (hgt : -e < d)
    (hhalf : 2 * d = (2 * w + 1) * e) : w = 0 ∨ w = -1 := by
  rcases lt_trichotomy w 0 with h | h | h
  · right
    by_contra hne
    have : w ≤ -2 := by omega
    nlinarith
  · left; exact h
  · exfalso
    have : 1 ≤ w := by omega
    nlinarith

/-- **Both admissible whole parts block the same parity.**  `w = 0` and `w = -1` reduce to `0` and
`7` modulo `8`, the two classes that block even `k`. So two half-movers at the largest flank cannot
cover both parities. -/
theorem half_mover_same_parity {w : ℤ} (h : w = 0 ∨ w = -1) : w % 8 = 0 ∨ w % 8 = 7 := by
  rcases h with h | h <;> subst h <;> decide

/-- **Two half-movers at the largest flank cannot cover both parities.**  Both admissible whole parts
lie in `{0, 7}` mod `8`, so no half-mover there blocks odd `k`. This is the configuration that
refuted the `|J| = 3` reduction, and it is excluded here. -/
theorem no_opposite_parity_halves {d₁ d₂ e w₁ w₂ : ℤ} (he : 0 < e)
    (h₁ : d₁ < e) (h₁' : -e < d₁) (hh₁ : 2 * d₁ = (2 * w₁ + 1) * e)
    (h₂ : d₂ < e) (h₂' : -e < d₂) (hh₂ : 2 * d₂ = (2 * w₂ + 1) * e) :
    (w₁ % 8 = 0 ∨ w₁ % 8 = 7) ∧ (w₂ % 8 = 0 ∨ w₂ % 8 = 7) :=
  ⟨half_mover_same_parity (half_mover_whole he h₁ h₁' hh₁),
   half_mover_same_parity (half_mover_whole he h₂ h₂' hh₂)⟩

/-- **The reduction, as a theorem.**  If the largest flank is clear at some opening, the subject has a
lonely instant — and that is Existence for this subject. The content is `FlankBridge.inWay_mod`'s
identity: `flankClear` at `A = 8k+1` *is* the loneliness condition at the instant `A / (8e)`. -/
theorem lonely_of_largest_flank_clear {ds : List ℤ} {e : ℤ}
    (h : ∃ k : ℤ, 0 ≤ k ∧ flankClear ds (8 * k + 1) e) :
    ∃ A : ℤ, (∃ k : ℤ, A = 8 * k + 1 ∧ 0 ≤ k) ∧ ∀ d ∈ ds, ¬ inWay d A e := by
  obtain ⟨k, hk, hcl⟩ := h
  exact ⟨8 * k + 1, ⟨k, rfl, hk⟩, hcl⟩

/-- **What Existence at order 8 needs from this route, stated as one implication.**  If every subject
of every arrangement has its largest flank clear at some opening, every subject is lonely.

The hypothesis is `LargestFlankClear` quantified over arrangements. It is **not proved**: it is
supported by 48,000 subjects, adversarial search to first-clear index 91, 200,000 ratio-space sets and
five structured families, with no shadowed case found — and by `no_opposite_parity_halves`, which
removes the one shadowing mode that is understood.

Three candidate mechanisms for it have been tested and refuted: a union bound (six movers at density
`1/4` give `3/2`), an index estimate from the smallest `|ρ|` (predicts `0.64` where `91` is observed),
and "a mover of denominator `q` is bad exactly at `k ≡ 0 mod q`" (false — `ρ = 4/5` blocks `{0,1}`,
`ρ = 11/13` blocks `{0,1,7}`). -/
theorem existence_of_largest_flank_clear
    (H : ∀ (ds : List ℤ) (e : ℤ), (∀ d ∈ ds, d.natAbs ≤ e.natAbs) →
          ∃ k : ℤ, 0 ≤ k ∧ flankClear ds (8 * k + 1) e)
    (ds : List ℤ) (e : ℤ) (hle : ∀ d ∈ ds, d.natAbs ≤ e.natAbs) :
    ∃ A : ℤ, (∃ k : ℤ, A = 8 * k + 1 ∧ 0 ≤ k) ∧ ∀ d ∈ ds, ¬ inWay d A e :=
  lonely_of_largest_flank_clear (H ds e hle)

end FlankBridge
