# The integer-reading case: a dichotomy with one branch proved

The exact search found every zero has **no reading divisible by 8**, and that connects to a theorem
already proved. For the class of profiles whose readings are integers — equivalently, `d_min`
divides every disparity — this gives a dichotomy with one branch closed.

---

## 1. The dichotomy

For an integer profile `1 = s₁ < s₂ < … < s₇`:

```
   BRANCH A   no reading ≡ 0 (mod 8)
              →  every odd integer of [1,15] is clear        [PROVED]
              →  R = 1 < 16

   BRANCH B   some reading ≡ 0 (mod 8)
              →  uncovered length > 0                        ← the one target
              →  a clear interval exists, so R ≤ 15 < 16
```

**Branch A is proved.** `Guard.odd_clear_of_not_dvd`: for integer `s` with `8 ∤ s` and `R` odd,
`8 ∤ s·R`. So no reading blocks any odd instant, and every one of `1,3,…,15` is clear. Axiom-clean.

**If Branch B holds, Existence is proved for the whole integer class.**

## 2. Why Branch B is plausible, and what supports it

Every zero of the uncovered functional found so far avoids multiples of 8:

```
   integers 2..40      3,262,623 profiles → 3 zeros: [2,3,4,5,6,7], [2,3,4,5,7,12], [4,5,6,7,11,13]
   half-integers to 20 2,760,681 profiles → the same 3
   zeros with a reading divisible by 8 :  none
   zeros with an empty clear set       :  none
```

and all three supply exactly the odd residues `{3,5,7}` mod 8 — the guard residues, with `s₁ = 1`
supplying the fourth. That is the guard structure appearing as a *necessary* condition on the zeros,
not an observation about one configuration.

## 3. Scope, stated plainly

Integer readings means `d_min` divides every disparity — a restricted class, not the general case.
Rational speeds give rational readings, not integer ones. So Branch A closes a sub-case and Branch B
would close that sub-case entirely; neither touches the irrational or general-rational profiles.

## 4. Why this is the right shape anyway

The two branches are the **residue partition seen from the covering side**. A reading divisible by
`8` is exactly a *colliding* disparity (v11 §6.15): it blocks every odd instant at once, which is
why Branch A's hypothesis is precisely "no collisions". So:

* no collision → the spine instants are clear → `R = 1` — this is `spine_all_or_nothing`;
* a collision → the subject must cascade, and the target is that the covering then cannot be
  complete.

The same split that governs cascade entry governs the covering. That is the third time the unit /
non-unit distinction of `slot_gcd` has decided a question in this line — after the cage and the
guards.

## 5. Status

| | |
|---|---|
| Branch A | **`[PROVED]`** `Guard.odd_clear_of_not_dvd`, axiom-clean |
| zeros avoid multiples of 8 | `[EMPIRICAL]` — 6.0M exact profiles, 3 zeros, none with one |
| zeros supply residues `{3,5,7}` | `[EMPIRICAL]` — all three |
| Branch B | **the target** — would close the integer class |
| the general case | untouched by this |

```bash
cd LonelyRunner && lake env lean ../experiments/n8/Guard_v1.lean
python3 experiments/n8/zeros_wide_v1.py    # 6.0M exact profiles, 3 zeros
python3 experiments/n8/mult8_v1.py         # minimum uncovered given a multiple of 8
```
