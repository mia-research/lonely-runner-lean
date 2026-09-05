# RESULT — which carry findings are ring-UNIVERSAL vs secp-specific (ℤ[i] vs ℤ[ω])

**Grade: cohomology `[VERIFIED — universal, ℤ[i]+ℤ[ω], exact]`; ¾-gate `[VERIFIED — ℤ[ω]-specific, geometric reason]`.**
Date 2026-08-17. Reflection thread 3 (the `ℤ[i]` generalization). Purpose: fix the *scope* of the carry
bricks so they are reusable with known generality. Reproduction: `scratchpad/gaussian.py`. Exact ℤ[i]/ℤ[ω].
No master edited.

## Setup
Same three carry constructions, run on a `j=1728` curve family (CM by the Gaussian integers `ℤ[i]`, `i`
order 4, `n≡1 mod 4`), and compared to secp's `ℤ[ω]` (`i`→`ω`, order-4→order-3).

## Ring-UNIVERSAL — the cohomology (additive class = conjugate Frobenius)
`ε_add(a,b)=(D(a)+D(b)−D(a+b))/π_n`; class `= Σ_i ε_add(1,i) = conj(π_n) = π̄_n`. **Holds exactly for `ℤ[i]`**:
n=1009 → (28,994)=(28,−15)=π̄; n=4993 → (63,4961)=π̄; n=20021 → (110,19932)=π̄ (3/3). Same as `ℤ[ω]`.
- **So the additive↔multiplicative = conjugate-split (`n = π·π̄`) result is GENERAL CM structure**, not
  `ℤ[ω]`-specific. Any CM curve's additive carry has class `π̄_n`; the multiplicative carry lives on `π_n`.
  This is the portable brick — it moves to any CM curve unchanged.

## Ring-SPECIFIC — the ¾ multiplicative carry gate is secp's (hexagonal) geometry
`ℤ[i]` multiplicative carry `ĉ(d)=(i·D(d)−D(i·d))/π_n`: **`Pr[ĉ=0] → 1`** (0.9980, 0.9996, 0.9999) — a
**trivial** carry (only rare boundary exceptions), vs `ℤ[ω]`'s nontrivial **¾**.
- **Geometric reason (intrinsic, not a convention choice):** the Gaussian reduced basis `{π_n, i·π_n}` is
  **orthogonal** (dot product `−ab+ba=0`, both norm `n`) — its fundamental domain is a **square**, which is
  `i`-invariant (90° symmetry), so `×i` never crosses a boundary ⇒ carry ≡ 0. The Eisenstein basis
  `{π_n, ω²·π_n}` sits at **60°** (hexagonal, non-orthogonal); the square lift-coordinates do **not** align
  with the `ω`-symmetry, and the mismatch is exactly ¼ ⇒ the `{¾,⅛,⅛}` carry.
- **The orbit-conservation** (`Σ ζ^k c(ζ^k d)=0`) is likewise: exact & nontrivial for `ℤ[ω]` (because the
  carry is nontrivial), trivial for `ℤ[i]` (`≈`0 because the carry is `≈`0).

## What this scopes (why it makes the other bricks more useful)
| brick | scope |
|---|---|
| additive class `= π̄_n`; additive↔mult = conjugate split | **universal CM** (ℤ[i], ℤ[ω], any order) |
| the ¾/{¾,⅛,⅛} multiplicative carry **gate** | **ℤ[ω]-specific** — the hexagonal μ₆/j=0 geometry (secp) |
| the `s<3/16` inscribed-ellipse threshold | **ℤ[ω]-specific** (the hexagon's inellipse) |
| the orbit **conservation** `Σζ^k c=0` | universal in *form*; **nontrivial only where the carry is** (ℤ[ω]) |
| island = ×(eigenvalue) rotation return set, gaps = `CF`/Cornacchia | universal (any CM eigenvalue) |

**Reading:** secp's *cohomological* carry structure is generic to CM; its *geometric* ¾-carry-gate is a
genuine distinguishing feature of the hexagonal `ℤ[ω]` curve. j=0 being "the most symmetric curve" shows up
concretely here: the 60° Eisenstein lattice is exactly what makes the multiplicative carry nontrivial, where
the 90° Gaussian lattice makes it vanish.

## Strengthening — j=0 is the UNIQUE CM curve with a nontrivial multiplicative carry gate
The `ℤ[i]`/`ℤ[ω]` pair is not two samples of many — it **exhausts** the cases. A multiplicative carry
`(ζ·D − D(ζ·))/π` needs an automorphism `ζ` of **order >2**, and the only imaginary quadratic orders with a
unit of order >2 are exactly **`ℤ[i]` (μ₄, j=1728)** and **`ℤ[ω]` (μ₆, j=0)** — every other CM order has unit
group `{±1}` (order-2), so `ζ=−1` gives only the negation carry, not a genuine multiplicative gate. We have
now measured **both**: `ℤ[i]` → trivial (orthogonal lattice), `ℤ[ω]` → nontrivial ¾ (60° lattice). Therefore:

> **Among ALL CM elliptic curves, j=0 (`ℤ[ω]`, secp) is the unique one carrying a nontrivial multiplicative
> carry gate.** It is the only order that has both an order->2 automorphism AND a non-orthogonal lattice.

`[VERIFIED — the two cases are exhaustive; rests on the standard classification of imaginary-quadratic unit
groups (only disc −3, −4 have units beyond ±1) + the two measurements here, not on extrapolation.]` This is
why the project's entire carry arsenal is a j=0/secp phenomenon and does not exist on any other curve.

## Scope / caveats
- `ℤ[i]` verified 3 curves (`n ≤ 20021`); the cohomology-class identity is algebraic (scale-independent),
  the `Pr[ĉ=0]→1` is the intrinsic orthogonal-lattice fact (rare exceptions = boundary ties).
- "¾ is ℤ[ω]-specific" is a statement about the *natural reduced-basis lift*; a deliberately sheared lift
  could manufacture a nontrivial carry on `ℤ[i]`, but that is not the ring's natural geometry. The point is
  the **natural** carry: nontrivial (ℤ[ω]) vs trivial (ℤ[i]).
- Structure, not a leak; d-homogeneous throughout.

## Where this leaves the map
The carry world is now scoped: a **universal cohomological layer** (conjugate split, portable) sits under a
**ℤ[ω]-specific geometric layer** (the ¾ gate, the hexagon threshold, the nontrivial conservation). Reusing
any carry brick elsewhere, we now know which layer it belongs to. The "which CM curves have a nontrivial
carry" question is **closed** by the exhaustiveness argument above (only j=0). The remaining live structural
thread from the reflection is the `L(s,χ₋₃)` shadow of the island gaps (thread 4) — the RH-programme link.
