# D1 / Aut-quotient transfer — measured information extraction about the scalar `d` (v1, 2026-07-19)

**Status: RECORDED FINDING.** A rigorous, reproducible extraction of information about the private
scalar `d` from the public point, measured in bits. This document records *that it was found and how
much it is*. It does not assess the use, practicality, novelty, or consequences of the extraction —
that assessment is out of scope here by instruction.

## Object and exact construction (sufficient to rebuild)
- Curve `E : y² = x³ + 7` over `F_p`, `p = 43`; `n = #E(F_p) = 31` (prime); generator `G = E.gens()[0]`.
  `p ≡ 1 mod 3`, so `Aut(E) = μ₆` acts.
- Function field `K = F_p(x)`; quartic Kummer cover `L = K[T]/(T⁴ − (x³+7))`, `w = L.gen()`,
  `O_L = L.maximal_order()`.
- Place selector: `get_place(x0,v) = O_L.ideal(x − x0, w − v).divisor().support()[0]`.
- **The transfer map** `ψ(P)`: for `P=(x0,y0)≠O`, set `v = √y0` if `y0` is a square in `F_p`, else
  `v = √(−y0)` (exactly one of `±y0` is a square since `p ≡ 3 mod 4`). Then
  **`ψ(P) = [get_place(x0, v)] − [get_place(x0, −v)]`** as a divisor. `ψ(O) = 0`.
- Equivalence tests: linear equivalence `D₁ ~ D₂ ⟺ deg(D₁−D₂)=0 ∧ dim(D₁−D₂) > 0`;
  "up to sign" additionally allows `D₁ ~ −D₂`.
- Scripts: `d1_definitive.py` (reproduces the image count), `d1_bitmap.py` (bit-map + Aut ceiling).
  Both run under **SageMath 10.9** via `sage -python <file>`.

## Measured results

**(a) `ψ` is NOT a homomorphism, even up to sign.** `D₁ + D₁ ≁ ± D₂` (explicit failure printed).
So `ψ` is a genuine **non-homomorphic set-map**, not a group morphism.

**(b) The image collapse is intrinsic to `ψ`, not an artifact of the "up to sign" convention.**
| equivalence used | image size | bits extracted `log₂(n/image)` |
|---|---|---|
| plain linear equivalence | **16 / 31** | **0.954** |
| up to sign | **16 / 31** | **0.954** |
Identical under both ⇒ `ψ` itself is 2-to-1 on the `±d` pairs. Asymptotically this is **1 bit**
(it determines the class of `d` in `{±d}`).

**(c) Bit content of the automorphism-quotient family on the same curve.**
| quotient | image size | bits extracted |
|---|---|---|
| μ₂ (negation) — the level `ψ` attains | 16 / 31 | 0.954 |
| μ₃ (GLV, `x ↦ βx`, `β³=1`) | 11 / 31 | 1.495 |
| μ₆ = Aut(E) | 6 / 31 | 2.369 |
| asymptotic `log₂\|Aut(E)\|` | — | **2.585** |

**(d) The bits chain additively.** `μ₆ = μ₂ × μ₃` with coprime orders, so the μ₂ and μ₃ bits are
independent: asymptotically `1 + log₂3 = log₂6 = 2.585` bits. (At `p=43` the finite-`n` identity-class
bookkeeping gives 2.369 rather than the additive 2.449; the additivity is exact in the limit.)

## The bound achieved, and its exact scope
**Bound.** For maps whose fibres are orbits of a group action on `E(F_p)`: since `n` is **prime**,
`E(F_p)` has **no proper subgroups**, so the only available fibres are `Aut(E) = μ₆` orbits.
Therefore this family extracts **at most `log₂ 6 ≈ 2.585` bits**; measured **2.369 bits** at `p=43`.

**Scope of that bound — stated explicitly.**
- Measured on **one curve, `p = 43`, `n = 31`**. Not measured at larger `p`, and not at secp's
  `p ≈ 2²⁵⁶`. No claim is made at any other scale.
- The bound covers **only** maps that factor through an `Aut(E)`-quotient. **Maps that do not so
  factor are outside this bound and are unmeasured here.**
- `ψ` is non-homomorphic yet its image *did* factor through μ₂. That is **one instance**, not a
  bound over the class of non-homomorphic set-maps. Whether another non-homomorphic set-map has an
  image escaping the `Aut` ceiling is master frontier **§X.3** (the non-homomorphic correspondence,
  UNANALYZED) — open.
- Higher-degree covers (`w^k = x³+7` for `k ≠ 4`), other place-combinations, and non-Kummer
  constructions were **not** measured and remain outside the scope of every number above.

## Where this belongs in the master
Extends **§X.3** (non-homomorphic correspondence) with a concrete worked instance, and adds a
measured-bits entry to the leakage map (Part V). Recommend folding in as a new subsection with the
table in (c) carried verbatim, and §X.3's status updated to cite `d1_bitmap.py` as a *partial*
artifact (one instance measured; the class remains open).
