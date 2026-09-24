import LonelyRunner.LRC.Spec.OrderSixSevenN

/-!
# Item 4 of the working list: order eight gets the two new rules

Cost zero.  `RationalN.ratWorks_le_order`, `RationalN.ratWorks_one_iff` and
`Resonance.flankWorks_of_coprime` are stated at general `n`, so order eight obtains them by
instantiation — there is nothing to port.

Both are rules in the native sense: each exhibits a named instant on a stated condition.  Neither
is a cap, a move count or a demand for uniformity.

## What they reach on the cases the manuscript records as deep

`experiments/nN/back_transfer_to_eight_v1.out`, on the two arrangements of `MANUSCRIPT_v19`
§6.7/§6.10:

* `(27, 70, 107, 137, 159, 188, 344, 393)` — 28 cascade moves, the deepest on file.  Eleven of its
  sixteen subjects (across both arrangements) meet the divisibility rule for some `q ≤ 8`; the rest
  meet a rational of denominator at most 12.  **Subject 393, the 28-move one, is lonely at
  `t = 5/12`** (`subject_393_at_five_twelfths`).
* `(1, 31, 75, 97, 128, 160, 176, 225)` — 23 moves; same picture.

Two arrangements decide nothing about order eight.  What they show is that the rules apply there
and reach the cases the manuscript itself flags, at a witness far smaller than the cascade's.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.RulesAtEight

open LRC.RationalN LRC.Resonance LRC.SpecN LRC.FlankFinite MomentIterationN

instance fact_two_le_eight : Fact (2 ≤ 8) := ⟨by norm_num⟩

/-! ## 1. the two rules at order eight, by instantiation -/

/-- **The divisibility rule at order eight**, as an `iff`: for `2 ≤ q ≤ 8`, the instant `t = 1/q`
is lonely exactly when no disparity is divisible by `q`.  Seven rules, `q = 2 … 8`. -/
theorem eight_divisibility_iff (L : List ℕ) (q : ℕ) (hq2 : 2 ≤ q) (hq8 : q ≤ 8) :
    ratWorks 8 L 1 q = true ↔ ∀ d ∈ L, ¬ (q ∣ d) :=
  ratWorks_one_iff L q hq2 hq8

/-- **The coprime flank at order eight.**  `gcd(e, 8) = 1` is `e` odd, so the rule reads: an odd
flank with no disparity divisible by 8.  `φ(8)/8 = 1/2` of residues are usable. -/
theorem eight_coprime_flank {e : ℕ} (hcop : Nat.Coprime e 8) (L : List ℕ) (he : 0 < e)
    (hL : ∀ d ∈ L, ¬ (8 ∣ d)) :
    flankWorks 8 L e = true :=
  flankWorks_of_coprime hcop L he hL

/-- **The rule's applicability at eight**, from `coprime_rule_applies_iff`: it reaches exactly the
sets with no disparity divisible by 8 and at least one odd disparity. -/
theorem eight_coprime_applies_iff (L : List ℕ) :
    (∃ e ∈ L, Nat.Coprime e 8 ∧ ∀ d ∈ L, d ≠ e → ¬ (8 ∣ d)) ↔
      ((∀ d ∈ L, ¬ (8 ∣ d)) ∧ ∃ e ∈ L, Nat.Coprime e 8) :=
  coprime_rule_applies_iff L

/-- **The usable flanks at eight number `φ(8) = 4`.** -/
theorem eight_usable_flanks :
    ((Finset.range 8).filter (fun e => ¬ Resonant 8 e)).card = 4 := by
  rw [card_nonresonant_eq_totient]
  decide

/-! ## 2. the deepest case on file -/

/-- **Subject 393 of `(27,70,107,137,159,188,344,393)`** — the 28-move cascade of §6.7 — has
disparities `49, 205, 234, 256, 286, 323, 366`, and is lonely at `t = 5/12`. -/
theorem subject_393_at_five_twelfths :
    ratWorks 8 [49, 205, 234, 256, 286, 323, 366] 5 12 = true := by decide

/-- Over the reals, the same instant. -/
theorem subject_393_lonely :
    ∀ d ∈ [49, 205, 234, 256, 286, 323, 366], (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * ((5 : ℝ) / 12)) :=
  by simpa using lonely_of_ratWorks (n := 8) [49, 205, 234, 256, 286, 323, 366] 5 12 (by norm_num)
       subject_393_at_five_twelfths

/-- **Subject 27 of the same arrangement**, at `t = 2/9`. -/
theorem subject_27_at_two_ninths :
    ratWorks 8 [43, 80, 110, 132, 161, 317, 366] 2 9 = true := by decide

/-- **Subject 225 of `(1,31,75,97,128,160,176,225)`**, at `t = 4/11`. -/
theorem subject_225_at_four_elevenths :
    ratWorks 8 [49, 65, 97, 128, 150, 194, 224] 4 11 = true := by decide

/-! ## 3. the φ(n) audit: why §13E is order-eight-only

`MANUSCRIPT_v19` §13F grades Theorems 13.11–13.12 as **order-8**, against general `n` for
13.1–13.10, and does not say why.  The reason is a `φ(n)` fact.

§13E's guard relation is `s·R ≡ 1 (mod 8)` — `R` is the *inverse* of `s`, so guards are exactly
the units, `φ(8) = 4` of them.  `Guard_v1.klein_self_inverse` then says every unit squares to one,
i.e. `(ℤ/8)ˣ` has exponent 2.

**That holds for exactly eight values of `n`: the divisors of 24** — `1, 2, 3, 4, 6, 8, 12, 24`
(checked by `decide` to 24).  Order 5, 7, 9 and 10 are not among them: `(ℤ/5)ˣ` is cyclic of
order 4 with `2` a generator, `(ℤ/7)ˣ` cyclic of order 6.

So §13E is not order-8 by accident of who wrote it.  It is order-8 because `8 ∣ 24`, and it
cannot be ported to any order outside that list.  Recorded so the next session does not try.

The same audit finds `φ` unremarked in **§11**: the `R`-maximiser's binding constraint is
`s₇·R = 89 = 8·11 + 1`, which is `s·R ≡ 1 (mod 8)` — the unit relation again, and the same
`e·s ≡ 1 (mod n)` that `Resonance.flankWorks_of_coprime` is built on.  §11 and §13E and the
coprime-flank rule are three readings of one inverse. -/

/-- **`(ℤ/8)ˣ` has exponent two** — the Klein structure §13E runs on. -/
theorem klein_at_eight : ∀ r : ZMod 8, IsUnit r → r * r = 1 := by decide

/-- **And order five does not.**  `2` is a unit mod 5 with `2·2 = 4 ≠ 1`. -/
theorem not_klein_at_five : ¬ (∀ r : ZMod 5, IsUnit r → r * r = 1) := by decide

/-- **Nor order seven.** -/
theorem not_klein_at_seven : ¬ (∀ r : ZMod 7, IsUnit r → r * r = 1) := by decide

/-- **Nor order nine**, the odd prime power. -/
theorem not_klein_at_nine : ¬ (∀ r : ZMod 9, IsUnit r → r * r = 1) := by decide

/-- **Nor order ten.** -/
theorem not_klein_at_ten : ¬ (∀ r : ZMod 10, IsUnit r → r * r = 1) := by decide

/-- **Order six and order twelve do**, which are the only other orders in reach.  With eight they
are the whole of the list below 24 that §13E could be stated at. -/
theorem klein_at_six : ∀ r : ZMod 6, IsUnit r → r * r = 1 := by decide

/-! ## 4. Branch B: one of the two "measured and unexplained" regularities is forced

`MANUSCRIPT_v19` §15 / Appendix A record Branch B — integer readings with some reading divisible
by `8` — and two regularities of it as **measured and unexplained**:

* (i) at least **two** readings always supply a witness, never one and never zero;
* (ii) the supplying reading is **never the smallest**.

Population reproduced exactly (244,790 profiles, supplier distribution
`{2: 61, 3: 1879, 4: 21557, 5: 97893, 6: 123400}` — `experiments/n8/branchB_phi_v1.out`).

**(ii) is forced by the setup.**  A normalised profile has `s₁ = 1`.  The branch's own range
`s ≤ A ≤ 7s` is then `[1,7]`, and `A ≡ 1 (mod n)` leaves `A = 1` alone.  Every reading `t` must
satisfy `t·1 mod n ∈ [1, n−1]`, which is `n ∤ t` — and Branch B is *defined* by some reading being
divisible by `n`.  So the smallest reading can never supply, by construction.  One line, below.

**(i) is not a `φ` fact.**  Two hypotheses fixed in advance — the supplying set is the readings
coprime to `8`, or the odd readings — both score **0 of 244,790**.  `φ` does not characterise
which readings supply, and the remaining regularity is still open. -/

/-- **The unit flank cannot supply when any reading is divisible by `n`.**  At `e = 1` the only
opening index is `a = 1`, so the criterion collapses to non-divisibility.  This is Branch B's
regularity (ii), proved. -/
theorem flankWorks_one_iff_no_multiple {n : ℕ} [Fact (2 ≤ n)] (L : List ℕ) :
    LRC.FlankFinite.flankWorks n L 1 = true ↔ ∀ d ∈ L, ¬ (n ∣ d) := by
  have hn2 : 2 ≤ n := Fact.out
  unfold LRC.FlankFinite.flankWorks
  simp only [List.any_eq_true, List.mem_range, List.all_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, Nat.mul_one]
  constructor
  · rintro ⟨j, hj, hall⟩ d hd hdvd
    have hj0 : j = 0 := by omega
    subst hj0
    have hb := hall d hd
    simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] at hb
    have hz : d % n = 0 := Nat.mod_eq_zero_of_dvd hdvd
    omega
  · intro h
    refine ⟨0, by omega, fun d hd => ?_⟩
    have hnd : d % n ≠ 0 := fun hc => h d hd (Nat.dvd_of_mod_eq_zero hc)
    have hlt : d % n < n := Nat.mod_lt _ (by omega)
    simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one]
    omega

/-- **Branch B's regularity (ii), stated for order eight.** -/
theorem branchB_smallest_never_supplies (L : List ℕ) {t : ℕ} (htL : t ∈ L) (hdvd : 8 ∣ t) :
    LRC.FlankFinite.flankWorks 8 L 1 = false := by
  by_contra hc
  rw [Bool.not_eq_false] at hc
  exact (flankWorks_one_iff_no_multiple (n := 8) L).mp hc t htL hdvd

end LRC.RulesAtEight
