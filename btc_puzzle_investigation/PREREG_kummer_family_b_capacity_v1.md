# PRE-REGISTRATION — how much can the Kummer-cover family `w^k = x³+b` know about `b`?

*Filed 2026-07-23 **before** the run. Binding on: any run reporting `b`-dependence of a Kummer cover
`w^k = x³ + b`. Motivated by `RESULT_mu3_cover_jacobian_v2.md`, where a claimed link turned out to be an
identity in `b`. Rather than deflate one more claim retroactively, this bounds the whole family in advance.*

## 0. The question

Three covers have now been built (`k = 3, 4, 6`). Every `b`-dependence found so far reduced to a residue
symbol of `b`. **Question: is that a general law, and if so what is the exact information capacity of the
family in `b`?**

Object under test, for `d | k`, `d > 1`, `χ_d` of exact order `d`:
```
S_d(b) := Σ_{x ∈ F_q} χ_d(x³ + b)          (χ_d(0) := 0,  d | q−1)
```
These sums are the Frobenius traces of the exact-order-`d` isotypic pieces of `Jac(w^k = x³+b)`, so any
isogeny-type invariant of any piece of any cover in the family is a function of the `S_d`.

## 1. The prediction, and why confirming it is NOT evidence

**Derived before the run** (record it as derived so a confirmation cannot be miscounted):
substituting `x → cx` gives `Σ_x χ_d(x³ + c³b) = χ_d(c³)·Σ_y χ_d(y³ + b)`, i.e.
```
(★)   S_d(c³ b) = χ_d(c)³ · S_d(b)        for every c ≠ 0
```

⚠ **`(★)` is a derivation. Verifying it is an INSTRUMENT CHECK on the code — zero information as
evidence.** It is registered here only so that a later run cannot report it as a discovery. (This is the
forced/unforced rule; the same mistake was made and corrected earlier today.)

## 2. The primary — this is the arm that carries information

`(★)` says `S_d` is constant on the orbits of `b ↦ c³b` **up to an explicit factor**. Those orbits are
the **cubic classes** of `F_q^*`, of which there are exactly **3**. The evidence-bearing question is
whether `(★)` is the *whole* story:

> **P1 (primary).** For every pair `b, b′` in the same cubic class, with `b′ = c³b`, does
> `S_d(b′) = χ_d(c)³ S_d(b)` hold **exactly, for every such pair**?

- **P1 confirmed ⇒** `S_d` is a function of the cubic class of `b` alone (plus the explicit factor)
  ⇒ **the entire family carries exactly `log₂ 3 ≈ 1.585` bits about `b`, and no more.**
- **P1 falsified ⇒** residual `b`-structure exists beyond the cubic class — **a positive**, and the
  interesting outcome. Any single exact counterexample falsifies.

## 3. Controls (must fire, or the arm is VOID)

- **C1 — wrong-exponent control.** Re-run P1 with the exponent perturbed: test
  `S_d(c³b) =? χ_d(c)² S_d(b)` and `χ_d(c)⁴ S_d(b)`. **Both must FAIL on a substantial fraction of
  pairs.** If a wrong exponent also "passes", the statistic has no power and the arm is void.
- **C2 — cross-class control.** For `b, b′` in *different* cubic classes there is no `c` with `b′=c³b`;
  the naive relation must **fail**. If it passes, the cubic classes are not being separated and the arm
  is void.
- **C3 — degenerate-`d` guard.** Report `d` values where `χ_d` does not exist over `F_q` (`d ∤ q−1`)
  separately; they are not evidence either way.

## 4. Scope, fixed in advance

- `q = p` prime, `p ≡ 1 mod 6`, `11 ≤ p ≤ 200` (so `χ₃, χ₆` exist); `d ∈ {2,3,6}` at all such `p`, plus
  `d ∈ {4,12}` at the subset with `4 | p−1` resp. `12 | p−1`.
- **All** `b ∈ {1,…,p−1}` and **all** `c ∈ {1,…,p−1}` — exhaustive, not sampled.
- Reported as exact counts of pairs, never a p-value. No float in the signal path.

## 5. Pre-committed conclusions

| outcome | conclusion, pre-committed |
|---|---|
| P1 exact, C1 + C2 both fire | The Kummer family's `b`-capacity is **exactly `log₂3` bits**. No cover in the family — at any `k`, for any piece — can carry secp-specific information about `b = 7` beyond `χ₃(7)`. **This closes the family as a source of curve-specific structure.** |
| P1 falsified (any exact counterexample) | Residual `b`-structure exists. Report the counterexample and the `(d, p, b, c)`; do **not** interpret further without a new prereg. |
| C1 or C2 fails to fire | **Arm VOID.** Report the control failure, no conclusion about capacity. |

## 6. What this cannot decide, stated in advance

- It bounds dependence on **`b`**, not on **`p`**. The `p`-dependence (e.g. `p mod 12`, supersingularity
  of the μ₄ part) is untouched and is not evidence for or against anything here.
- It says nothing about the **`d`-side**. No leakage, key-recovery, or ECDLP consequence follows in
  either direction — the covers are curve-side CM objects throughout.
- A capacity bound of `log₂3` bits is a statement about **this family of covers**, not about all
  constructions from `E`. Non-Kummer covers, other place-combinations, and higher-degree
  non-cyclic covers are outside it (cf. Addendum §A1.4's own scope line).
