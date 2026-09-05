# RESULT — #26: `G` constructed explicitly; its Möbius symmetry group is TRIVIAL over `F̄`; and the reformulation that replaces the symmetry programme

**Date:** 2026-08-01. **Scripts:** `tors2_fp3_symmetry_v1.py`, `_v2.py`. Both pass `check_no_float.py`.
**Grade:** construction `[VERIFIED — validated against direct point arithmetic]`;
symmetry group `[REFUTED — exhaustive over `F̄`, 3 curves]`.
Follows `RESULT_26_involution_mechanism_refuted_v1.md` (which refuted odd symmetries over `F_p` only).

---

## 1. `G` is now explicit — first time in the record

For the line through `−R = (x_R, −y_R)` of slope `λ`, the cubic
`x³+Ax+B − (λ(x−x_R)−y_R)²` has roots `x_R, x₁, x₂`, giving
`x₁+x₂ = λ²−x_R` and `x₁x₂ = x_Rλ² + 2y_Rλ + A + x_R²`. Hence

> `D(λ) = λ⁴ − 6x_Rλ² − 8y_Rλ − 3x_R² − 4A`  (`= (x₁+x₂)²−4x₁x₂`; `χ₂(D)` = split/inert)
> `F(λ) = y_Rλ³ + (A+3x_R²)λ² + 3x_Ry_Rλ + y_R²`  (`= y₁y₂`)
> **`G = D·F`, degree 7, and `T(λ) = χ₂(G(λ))`.**

**Validated, not assumed:** both formulas checked against direct point arithmetic at every `λ`, and
`Σ_λ χ₂(G(λ)) = 0` reproduces the independent point-based computation exactly (42 nonzero terms at
`p=43`, matching `tors2_involution_test_v3.py`'s 42 non-branch `t`).

**Root structure, as predicted:** `D`'s roots are the four tangent slopes at `{P : 2P=R}`; `F`'s are
the slopes through the three 2-torsion points. **All 7 roots lie in `F_{p³}`** — verified, every case.
(`F_{p³}` is the 2-torsion field: `x³+Ax+B` is irreducible over `F_p` exactly when `n` is odd.)

## 2. The symmetry group is trivial — exhaustive over `F̄`, not a sweep

A Möbius `σ` with `G∘σ = ν·G` must **permute `G`'s 7 roots**, and a Möbius map is pinned by 3 points.
So the `7·6·5 = 210` triple-correspondences exhaust **every** candidate over `F̄` — this is not a
search over `PGL₂(F_p)` or `PGL₂(F_{p³})`, it is the complete list.

| curve | `p` | `R` | roots in `F_{p³}` | Möbius maps permuting them | `Σχ₂(G)` |
|---|---|---|---|---|---|
| `y²=x³+7` | 43 | `e=1,2,3` | 7 | **1 (identity only)** | 0 |
| `y²=x³+7` | 67 | `e=1,2` | 7 | **1 (identity only)** | 0 |
| `y²=x³+x+6` (generic `j`) | 79 | `e=1,2` | 7 | **1 (identity only)** | 0 |

> **The stabiliser of `G`'s root configuration in `PGL₂(F̄)` is trivial.**

**⇒ The odd-symmetry programme is dead, completely.** Not "no rational involution" (the previous
result), and not "none over `F_{p³}`" — **no Möbius symmetry of `G` exists at all**, over the
algebraic closure. The exact balance of `T` has no explanation in the geometry of the `t`-line.

This also retires the specific `E[2]`-translation candidate: the `τ_T` do act on `E/ι`, but they do
**not** preserve `G` (they permute `D`'s roots but not `G`'s, since `F`'s roots are not stabilised).

## 3. What replaces it — a reformulation, and it is sharper

`deg G = 7` is odd, so the hyperelliptic curve

> **`C : w² = G(λ)`, genus 3**

has exactly one point at infinity, and `#C(F_p) = p + 1 + Σ_λ χ₂(G(λ))`. Therefore

> ### #26 ⟺ `#C(F_p) = p + 1` exactly, for every `R ≠ O` — i.e. `Jac(C)` has Frobenius trace **0**.
> Equivalently: **`C` has the same point count as its own quadratic twist.**

That is a statement about `Jac(C)`, not about `P¹` — which is precisely why §2's exhaustive negative
does not touch it. It also puts the odd/even-`n` hinge in a natural place: trace-zero/supersingularity
conditions are exactly where 2-torsion rationality enters.

**And it explains the shape of the original identity.** The two sides of
`Σ_rational = Σ_conjugate` are sums over `E(F_p)` and over the trace-zero subgroup `≅ E'(F_p)` — the
quadratic twist. A twist-pairing forcing `a_p(Jac C) = 0` is exactly the kind of object that makes a
character sum vanish *exactly* rather than to `O(√p)`.

## 4. Next step — decompose `Jac(C)`

Concrete and finite: `C : w² = D(λ)F(λ)` with `D` quartic (branch/tangent) and `F` cubic (2-torsion).
Determine whether `Jac(C)` (dim 3) splits — the natural guess is factors related to `E` and its
quadratic twist, with the trace cancelling between them. Testable immediately by counting
`#C(F_{p^k})` for `k = 1,2,3` and reading off the zeta function, then comparing to `E`, `E'`.

**Do NOT run another symmetry search.** §2 is exhaustive over `F̄`; that avenue is closed at grade —
object: the Möbius stabiliser of `G`'s root set; class: all of `PGL₂(F̄)`; power: exhaustive, exact;
scope: 3 curves (`j=0` and generic `j`), `p = 43,67,79`, several `R`.
