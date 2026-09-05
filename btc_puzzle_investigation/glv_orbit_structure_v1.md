# GLV-Orbit Action on the Single-x Shadows (v1, 2026-07-13)

Completes the single-`x` structure map begun by `lift_sextant_rhombus_law_v2.md`
(geometric shadow) and `lift_chi6_uniform_law_v1.md` (multiplicative shadow). Here:
how the **GLV endomorphism** acts on each shadow, in closed form.

Verification: `glv_orbit_structure_proof_v1.py` (exact arithmetic; real curve points).

## Setup

GLV endomorphism `φ(x,y) = (β·x, y)`, `β³=1, β≠1` (a nontrivial cube root of unity
mod `p`); on scalars `[λ]P = φ(P)`, `λ²+λ+1 = 0 (mod n)`. The **GLV triple** of a key
`d` is `{[d]G, [λd]G, [λ²d]G}`, with `x`-coordinates `{x, βx, β²x}`.

## (A) `β ≡ ω² (mod π_p)` — GLV is Eisenstein-unit multiplication

`𝔽_p ≅ ℤ[ω]/(π_p)` sends `ω` to a root of `X²+X+1`; `β` is exactly such a root, and
numerically `β = ω² mod π_p`. So the GLV endomorphism **is** "multiply the lift by a
primitive cube root of unity `ω²`" — the CM-by-`ℤ[ω]` origin of secp's GLV made
explicit at the lift level.

## (B) Multiplicative shadow — clean constant shift

Because `χ_k` are multiplicative, GLV shifts them by a constant (exact, all `x`):

| character | GLV action | on the triple `{x, βx, β²x}` |
|---|---|---|
| `χ₆(βx) = χ₆(x) + 4 (mod 6)` | +4 | three residues of **fixed parity** `{c, c+2, c+4}` |
| `χ₃(βx) = χ₃(x) + 1 (mod 3)` | +1 | **all three** cubic classes `{0,1,2}`, once each |
| `χ₂(βx) = χ₂(x)` | invariant | constant (`β` is a QR) |

Since `χ₆ = (χ₂, χ₃)` by CRT on `ℤ/6`, the whole action is carried by `χ₃` (`+1`);
`χ₂` is fixed. The cubic character is a **bijection on each GLV orbit**. *(Verified
exact over 40000 `x`.)* This is the closed-form "GLV-orbit action on `χ₆`" target.

## (C) Geometric shadow — GLV-tangled (no clean law)

Multiplication by `ω²` is a 120° lattice rotation = `+4` sextants, but the fundamental
domain `P` is a **rhombus** (180°-symmetric, not 120°), so reducing `ω²·w` back into
`P` folds. Measured `sextant(eis(βx)) − sextant(eis(x))`: `+4` ≈ 75%, `+0` ≈ 23%,
boundary ≈ 2% — **no clean shift**. The additive/geometric readout does not respect
GLV, precisely because its symmetry (rhombus `D₂`) is coarser than the endomorphism's
(cube-root `C₃`).

## (D) `y` is fixed by GLV

`φ` preserves `y`, and `x³+7` is GLV-invariant (`β³=1`, verified). So GLV gives **zero
leverage** on any `y`-coordinate / group-law functional — that frontier is orthogonal
to the endomorphism.

## What this closes — the single-x map is charted

Putting the three results together, the single-`x` structure is now essentially
complete:

- **Multiplicative readouts** (`χ_k`, `k | p−1`, nontrivial): marginal **exactly
  uniform** (character orthogonality); GLV acts by a **constant shift**; conditional
  on `d` is `O(p^{-1/2})` (Weil).
- **Geometric readout** (lift sextant / angle): marginal is the **non-uniform rhombus
  area law** (one parameter `θ`); GLV **tangles** it; conditional `O(p^{-1/2})`.
- **`y`**: **GLV-invariant**; single-`x` machinery says nothing about it.
- Geometric ⟂ multiplicative shadows (asymptotically independent, exact).

## What stays genuinely open (unchanged)

The remaining structure lives **off** the single-`x` axis:

1. **Joint / multi-point across INDEPENDENT keys.** GLV yields only the *degenerate,
   deterministic* triple `{x, βx, β²x}` of a single key — not correlations across the
   independent puzzle keys. The generator's only possible fingerprint is a joint
   property of the SET it left; no single-`x` or GLV-orbit result touches this.
2. **`y` / group-law functionals.** GLV fixes `y`; the point-addition structure is
   where a set signature could hide, and it is not reduced to single-`x`
   equidistribution.

As recorded throughout: a null battery can never prove curve-side closure (= ECDLP
security); only positive theorems are provable, and these charted single-`x` positives
are exactly that — they say the single-`x` axis carries no scalar information, by
theorem rather than by accumulated nulls.
