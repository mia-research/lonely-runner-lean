# The Lift-Norm Band Law (v1, 2026-07-13)

Completes the single-`x` chart (with `lift_sextant_rhombus_law_v2.md`,
`lift_chi6_uniform_law_v1.md`, `glv_orbit_structure_v1.md`). The last single-`x`
functional: the **norm** `N(eis(X)) = |eis(X)|² = u²−uv+v²` (the true squared length of
the lift). Verification: `norm_band_law_proof_v1.py`.

## Theorem (norm-band law — universal, θ- and p-independent)

`{eis(X)}` is uniform on `ℤ²∩P`, and `N` is rotation-invariant, while the rhombus `P`
has a **universal shape** (60°, diagonals `√(3p) : √p`) — only its orientation `θ`
varies. Hence, with `s = N(eis(X))/p`, the distribution of `s` is **the same for every
prime `p ≡ 1 (mod 3)` and independent of `θ`**:

- **support** `[0, 3/4]` (max at the long vertices, `|A|² = 3p/4`);
- **mean** `E[s] = 1/6` exactly, i.e. `E[N] = p/6` (second moment of the diamond
  `|x/a|+|y/b|≤1` is `(a²+b²)/6 = (3p/4 + p/4)/6`);
- **density** piecewise-analytic, `f(s) = (d/ds)·area(P ∩ disk_{√(sp)})/(√3 p/2)`, with
  breakpoints at the **inradius** `ρ²/p = 3/16`, the **short vertex** `1/4`, and the
  **long vertex** `3/4`. On the first piece the disk lies inside `P`, so
  `f(s) = 2π/√3 ≈ 3.628` is **constant** on `[0, 3/16]`; beyond `3/16` subtract the four
  equal circular segments cut past the (tangential) edges; past `1/4` the short vertices
  enter.

*(Verified: exact circle-∩-rhombus CDF matches the exact secp lattice histogram to
`max|·| = 0.0008`; `E[s] = 0.16678 ≈ 1/6`; `max s = 0.7474 ≈ 3/4`; the same closed-form
CDF matches the exact full-`𝔽_p` histogram at `p = 10009` to `0.0011` — confirming
`θ/p`-independence.)*

## Contrast within the single-x chart

| functional | marginal | depends on `θ`? |
|---|---|---|
| angle (sextant) | non-uniform rhombus **area** law | **yes** (orientation) |
| norm (band) | universal density, mean `1/6` | **no** (rotation-invariant) |
| `χ₆` (multiplicative) | exactly uniform | no |

The angle and the norm are the two coordinates of the same uniform-on-rhombus lift: the
**angular** part carries the `θ`-dependence (rhombus orientation), the **radial** part is
`θ`-blind (rhombus shape). Both are scalar-independent; both have `O(p^{-1/2})`
conditional MI with any coarse `d`-target (Weil). This exhausts the single-`x` axis.
