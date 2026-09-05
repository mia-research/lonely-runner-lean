# The Sextic-Character Uniform Law (v1, 2026-07-13)

Companion / contrast case to `lift_sextant_rhombus_law_v2.md`. Both the lift **angle**
(sextant) and the sextic **character** `χ₆` are single-`x`-coordinate functionals, and
both are scalar-independent. Their marginals have opposite shapes — one non-uniform, one
exactly uniform — and (the sharper finding) they are **asymptotically independent**.

Verification: `lift_chi6_uniform_law_proof_v1.py` (exact integer counting; full-`𝔽_p`
enumeration for the independence test — no sampling noise).

## Setup

`p ≡ 1 (mod 3)`, `p` odd ⇒ `p ≡ 1 (mod 6)` ⇒ `6 | (p−1)`. `χ₆ : 𝔽_p^* → μ₆`,
`χ₆(x) = x^{(p−1)/6}` valued in the 6th roots of unity `μ₆ ⊂ 𝔽_p` (a multiplicative
readout of `x`). This is the same `χ₆` the investigation uses for the sextic/CM structure.
The lift **sextant** `σ(eis(X))`, by contrast, is an **additive/geometric** readout: the
60° angular sector of `X mod π_p` in the rhombus `P`.

## Theorem (χ₆ marginal is exactly uniform — unconditional, group theory)

`𝔽_p^*` is cyclic of order `p−1`; `χ₆` is a surjective homomorphism onto `μ₆` with kernel
the sextic residues, of index exactly 6. Hence every fiber has **exactly** `(p−1)/6`
elements:

  **`#{ X ∈ 𝔽_p^* : χ₆(X) = ζ^j } = (p−1)/6`  for each `j = 0,…,5`,**

and the additive character sum `Σ_{X∈𝔽_p^*} ζ_6^{χ₆(X)} = 0` exactly. No `d`, no analytic
input. *(Verified by exact enumeration at `p=100003`: all six fibers `= 16667`, character
sum `= 0`; secp `(p−1) mod 6 = 0`; secp uniform-`X` sampler matches `1/6` to `~1/√M`.)*

## The contrast (both single-`x`, both scalar-independent)

| readout | type | marginal |
|---|---|---|
| sextant `σ(eis(X))` | additive / geometric | **non-uniform** — rhombus area law `(1/8, p₀(θ), 3/8−p₀(θ))` |
| `χ₆(X)` | multiplicative | **exactly uniform** — `1/6` each |

"Scalar-independent" does **not** mean "uniform." The marginal is whatever the
functional's pushforward of `Uniform(ℤ²∩P)` (resp. of `Uniform(𝔽_p^*)`) yields, and both
are computed exactly here: geometric angle is skewed by the rhombus, multiplicative
character is flat by orthogonality.

## Relation: the two shadows are asymptotically independent

Exact full-`𝔽_p` enumeration of the `6×6` `(σ, χ₆)` contingency table gives a `χ²` of
independence (df `= 25`) that stays `~25` as `p` grows from `10³` to `4·10⁵` (`N` ×400) —
**no growth**, so `σ` and `χ₆` are **asymptotically independent**; any correlation is
`O(p^{-1/2})`, at the character-sum floor. The additive/geometric shadow and the
multiplicative shadow of `X` do not interact.

> **Correction to prior note.** The earlier control "`MI(sextant; χ₆(X))` fires"
> (`eisenstein_lift_sextant_exact_v1.py`, and the memory) was a **small-sample artifact** —
> the finite-sample MI estimator echoing sextant's own marginal non-uniformity, not genuine
> dependence. The exact enumeration is decisive: independent. That control should not be
> relied on as a "detector-sees-dependence" sanity check.

## Conditional (curve, cited — same footing as the rhombus law)

Over curve `x`-coordinates `x([d]G)` the per-value count splits as
`N_j = Σ_x [χ₆(x)=j](1 + χ₂(x³+7)) = (p−1)/6  +  Σ_x [χ₆(x)=j] χ₂(x³+7)`,
where the first term is exact (orthogonality) and the second is a curve character sum,
`|·| = O(√p)` (Weil). So `χ₆` over the curve is uniform up to `O(p^{-1/2})`, and
`MI(χ₆ ; d mod m) = O(p^{-δ})` — a single-`x` functional, hence covered by the same
equidistribution input as every other single-`x` readout. *(Empirical gen256, `M=40000`:
matches `1/6` to `max|·−1/6| = 0.0044`.)*

## Scope

Adds the exactly-uniform contrast case and the exact independence of the two shadows.
Unchanged frontier (from the rhombus law): the **conditional** rests on cited Weil
equidistribution; **joint/multi-point** and **`y`/group-law** functionals are not addressed.
Next single-`x` target still open: the GLV-orbit action on `χ₆` (`χ₆` shifts by `χ₆(β)=`
const under the GLV endomorphism — a closed-form orbit statement).
