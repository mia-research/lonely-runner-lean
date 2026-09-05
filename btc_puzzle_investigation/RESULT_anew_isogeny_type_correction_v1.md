# RESULT — `A_new` is **not** a Weil restriction at `m = ±1`; its isogeny type, corrected and sharpened

*2026-07-23. Object-level audit of `POSITIVE_FINDINGS_ADDENDUM_1_v1.md` §A1.1 "Fact 2".
Independent re-implementation + exhaustive enumeration. Scripts: `scratchpad/mlaw.py`, `scratchpad/ss2.py`.
No leakage, key-recovery, or ECDLP claim is made or implied.*

---

## 0. What triggered this

§A1.1 Fact 2 states, of `C : w⁴ = f(x)`, `Jac(C) ~ E × A_new`:

> "With `b₁ = 0`, `L_new(T) = 1 + m·p·T² + p²T⁴` is a polynomial in `T²` ⇒ `A_new` is up to isogeny the
> **Weil restriction of an elliptic curve `E'/F_{p²}`**."

The inference "L-polynomial even in `T` ⇒ Weil restriction from `F_{p²}`" is a **non-sequitur**. Evenness
is a statement about the *coefficients*; being a Weil restriction is a statement about the *isogeny
class*, and it carries an existence obligation: some elliptic curve `E'/F_{p²}` must actually have
`L_{E'}(S) = 1 − t'S + p²S²` with `t' = −m·p`. That obligation is not discharged in §A1.1, and at
`m = ±1` **it cannot be**.

## 1. The `m`-law, independently reproduced `[VERIFIED — 22 primes, second implementation]`

`m` computed from scratch by point-counting `C : w⁴ = x³+7` and `E : y² = x³+7` over `F_p` and `F_{p²}`
(`a_new(k) = a_C(k) − a_E(k)`; `b₁ = −a_new(1)`; `b₂ = (b₁² − a_new(2))/2`; `m = b₂/p`). Exact integer
arithmetic throughout; `F_{p²}` built as `F_p[T]/(irreducible)`. `p ≡ 3 mod 4`, `13 ≤ p ≤ 199`.

**Counts, split forced / unforced** (drill rule: forced agreement carries zero information):

| observation | count | forced? |
|---|---|---|
| `b₁ = 0` | 22/22 | **FORCED** — §A1.1 Fact 1 *derives* it from the proved step-2 conjugation relation. This is an **instrument check on my code**, not evidence. |
| `p ≡ 11 mod 12 ⇒ m = 2` | 11/11 | **UNDETERMINED.** I did not establish whether `m = 2` is forced here. (`p ≡ 2 mod 3` makes `y²=x³+7` itself supersingular, which is *consistent* with `π²=−p` but is not shown to force it; `m ∈ {0,±1,±2}` a priori.) **Until that is settled this row cannot be graded as unforced evidence.** |
| `p ≡ 7 mod 12`, `7` a **non**-cube `⇒ m = 1` | 10/10 | unforced |
| `p ≡ 7 mod 12`, `7` a cube `⇒ m = −2` | 1/1 (`p=19` only) | unforced, **but a single prime** |

**Unforced content of this run: the 11 primes at `p ≡ 7 mod 12` where the cubic residue of `B` selects
the branch — of which exactly one exercises `m = −2`.** The `22/22` and the `11/11` must not be added to
that. (This is the `42/42 → 35/35` failure mode of v33; it recurred here and is corrected in place.)

This agrees with `secp_mu4_eigenvalue_individual_2026_07_20` and §A2.1 across two independent
implementations — which is what validates my code, including the one modelling choice the script does
**not** verify: `#C(F_{p^k}) = (affine count) + 1`, i.e. a single totally-ramified point at infinity
(`gcd(deg f, 4) = 1`). That choice is validated by the agreement, not derived in the script.

## 2. The existence obstruction `[VERIFIED by exhaustion + CITED]`

**Claim tested:** over `F_q`, `q = p²`, a supersingular elliptic curve of trace `t = ±p = ±√q` exists
**iff `p ≢ 1 mod 3`.**

Exhaustive enumeration of *every* curve `y² = x³+ax+b` over `F_{p²}` (all `(a,b)`, nonzero
discriminant), collecting all traces divisible by `p`:

| `p` | `p mod 3` | supersingular traces over `F_{p²}` | `±p` present? |
|---:|---:|---|---|
| 5 | 2 | `{−10, −5, 0, 5, 10}` | **yes** |
| 7 | 1 | `{−14, 0, 14}` | **no** |
| 11 | 2 | `{−22, −11, 0, 11, 22}` | **yes** |
| 13 | 1 | `{−26, 0, 26}` | **no** |

`[VERIFIED — exhaustive, 4 primes ≤ 13]`. The corresponding classical statement (Waterhouse 1969
Thm 4.1; Schoof 1987 §4) is `[CITED — NOT verified against source; citation-verifier NOT run]`.

⚠ **Scope, corrected.** An earlier draft of this section claimed "the conclusion rests on the
enumeration, not the citation." **That is true only at small `p`.** The enumeration covers `p ≤ 13`;
the application to `p = 2²⁵⁶−2³²−977` is a ~250-binary-order extrapolation — frontier §XI.5's scale
banner, which governs this file as it governs every other. Therefore:
- **the withdrawal of §A1.1's sentence at the enumerated primes** is `[VERIFIED]`;
- **the withdrawal at secp** is `[CITED-CONDITIONAL]` — it holds *if* the classical theorem holds at
  256-bit `p`, which is standard but unverified here. Running `citation-verifier` on Waterhouse
  Thm 4.1 is the outstanding step and is a precondition for grading §3 any higher.

## 3. Consequence `[DERIVED at p ≤ 13 / CITED-CONDITIONAL at secp — see §2's scope note]`

`p ≡ 7 mod 12` ⟹ `p ≡ 1 mod 3`. If `A_new ~ Res_{F_{p²}/F_p}(E')` then `L_new(T) = L_{E'}(T²)`, forcing
`t' = −m·p`. At `m = 1` that is `t' = −p`, which **no elliptic curve over `F_{p²}` attains when
`p ≡ 1 mod 3`**. Symmetrically for `m = −1`.

> **`A_new` is not isogenous to a Weil restriction of an elliptic curve over `F_{p²}` whenever
> `m = ±1`.** §A1.1's Fact 2 sentence is **withdrawn** in that generality.

**secp256k1 is exactly this case:** `p ≡ 7 mod 12` (`p mod 12 = 7`, `p mod 8 = 7`, `p mod 3 = 1`,
`p mod 4 = 3` — all verified at the 256-bit prime), and `m = 1` `[CONDITIONAL — Jacobi sign law,
Addendum §A2.2 / frontier #15]`.

## 4. The corrected statement — three isogeny types, one per branch `[DERIVED from §1]`

Frobenius char. polynomial `P(t) = t⁴ + m·p·t² + p²`.

| branch | `P(t)` | `π²` | `ℚ(π)` | isogeny type |
|---|---|---|---|---|
| `p ≡ 11 mod 12` (`m = 2`) | `(t²+p)²` | `−p` | `ℚ(√−p)`, **quadratic** | `A_new ~ E'²`, `E'/F_p` supersingular `t = 0`. Not simple. Consistent: `p ≡ 2 mod 3` ⇒ `y²=x³+7` is **itself** supersingular. |
| `p ≡ 7 mod 12`, `7` a cube (`m = −2`) | `(t²−p)²` | `+p` | `ℚ(√p)`, **real quadratic** | Real Weil number ⇒ **simple** surface, quaternionic `End⁰`. |
| `p ≡ 7 mod 12`, `7` a non-cube (`m = 1`) | `t⁴+pt²+p²` | `p·ζ₃` | `ℚ(√p, √−3) = ℚ(√p, ω)`, **quartic** | **Simple** supersingular abelian surface. `π/√p` has order **6**. ← **secp** |

**The eigenvalues at `m = 1`:** `√p · {ζ₆, ζ₆², ζ₆⁴, ζ₆⁵}` — the four sixth roots of unity other than
`±1`, at `60°, 120°, 240°, 300°`. Sum `= 0` (recovers `b₁ = 0`), and `π⁶ = p³`, i.e. `k(m=1) = 6` —
which **independently reconfirms** `secp_mu4_eigenvalue_individual_2026_07_20`'s corrected root order
(primitive 3rd/6th, **not** `ζ₁₂`) and reconfirms the retraction recorded at §A4.28.

**Why the corrected form is stronger, not weaker.** The Frobenius field of `A_new` at secp is
`ℚ(√p) · ℚ(ω)` — the compositum of the real quadratic `ℚ(√p)` with **the curve's own CM field `ℚ(ω)`**.
"Weil restriction of some curve over `F_{p²}`" said nothing about secp's arithmetic; the corrected
statement names `A_new` as a *simple* surface whose endomorphism field contains `ℤ[ω]`, tying the μ₄
cover back to the μ₃ structure that carries every other law in the record.

## 5. What is unaffected — **checked, not asserted**

- **The withdrawal does not propagate.** `grep -rni "weil restriction"` over the whole investigation
  directory returns **exactly two hits**: `RESULT_mu6_cohomology_supersingular_v2.md:95` (the source
  artifact) and `POSITIVE_FINDINGS_ADDENDUM_1_v1.md:88` (§A1.1). **Nothing downstream builds on it.**
- ⚠ **But neither source file points at this withdrawal.** Per CLAUDE.md §1 those versioned files must
  not be edited in place; the back-pointer belongs in their successor versions. Recorded in the memory
  index only. **Flag for the next `compile-diff`-gated promotion** — a withdrawal that is not linked
  from its source is the exact failure mode of the H3→H4→master degradation audit.
- **No collision with either retraction ledger** — checked against v4 §XII (1–26) and Addendum §A4
  (27–38). Nothing claimed here re-claims a retracted item; §4's `m = 1` ⇒ order-6 eigenvalues
  **independently reconfirms** §A4.28's correction rather than restating the retracted `ζ₁₂` form.
- **§A1.1's supersingularity theorem is untouched.** Its three-step proof (`ζ₄` ⇒ `Q(i) ↪ End⁰`;
  `π ζ₄ π⁻¹ = ζ₄⁻¹` at `p ≡ 3 mod 4`; `p`-rank dichotomy) never used the Weil-restriction sentence. `A_new`
  is supersingular at secp.
- **`b₁ = 0` (Fact 1), the `m` range `{−2,…,2}`, the `p mod 12` law, and `m = 1` at secp
  `[CONDITIONAL]`** all stand — §1 reproduces them independently.
- Frontier **#15** (the Jacobi sign law) is **not** retired by this. At `p ≡ 7 mod 12` **both** `m = −2`
  and `m = 1` occur, so no congruence condition on `p` alone selects the branch — the cubic residue of
  `B` does, and that is precisely the Jacobi-sum content. The classical classification constrains
  *which* `m` are available; it does not compute *which one happens*.

## 6. A hypothesis of mine, killed by its own check

I conjectured that the `3` in frontier **#16**'s open identity
`(†) C′ − C = 3·h(−p)` is the class number of the compositum, i.e. that `(†)` is a known relation
between `h(−p)` and `h(−3p)`. **Refuted.** `h(−12p)/h(−p)` (disc of `ℚ(√−3p)` is `−12p` for
`p ≡ 3 mod 4`) is **not constant** — it ranges over `0.49 … 20.0` across `p < 2000`, in both residue
classes `p ≡ 7, 11 mod 12`. The `3` is not a genus-theory/compositum factor. Frontier #16 stands
exactly as recorded, with the machinery still unnamed.

---

*Grade of §3–§4: `[DERIVED — UNREVIEWED]` (author's own derivation from §1–§2; no adversarial pass).
§1 and §2 are `[VERIFIED]` at the stated scopes. The scale banner applies to §1 (`p ≤ 199`); §2's
enumeration is at `p ≤ 13`; §3's application to secp uses only the exact congruences of the 256-bit
prime plus the `[CONDITIONAL]` value `m = 1`.*
