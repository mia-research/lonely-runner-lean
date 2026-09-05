# RESULT — pre-screen of the Eisenstein-lattice features: two of three are FORCED; the third lane is open and never run

**Date:** 2026-08-01. **Script:** `glv_lattice_feature_prescreen_v1.py` (integer-only, passes
`check_no_float.py`). **Grade:** forcing results `[PROVED]` (identity) + `[VERIFIED — 5 j=0 curves]`;
the surviving lane `[OPEN — never run]`.

---

## 0. What was proposed

> *"Every scalar `d` lifts to an Eisenstein integer `κ = k₁ + k₂ω`. Measure the exact hexagonal norm
> `N = k₁² − k₁k₂ + k₂²` and the sextic sector of that scalar … measure the exact integer
> cross-product (the determinant) of a scalar and its inverse in GLV space."*

The coordinate system is **right** — see §3. Two of the three named statistics are forced to zero.

## 1. The forcing rules (both exact, neither statistical)

On a `j=0` curve, `[λ](x,y) = (βx, y)` with `β` of order 3. Hence, **by the endomorphism**:

- `c(λd) = c(d)` for `c = χ₂(y)` — `y` is untouched. **μ₃-invariant.**
- `c(−d) = ε·c(d)`, `ε = χ₂(−1)`. secp256k1 has `p ≡ 3 mod 4`, so **`ε = −1`: `c` is ODD.**
- `χ₂(β) = +1` (as `p ≡ 1 mod 6`, `(p−1)/3` is even), so `χ₂(x)` is **also μ₃-invariant**, and it is
  **EVEN** under `d ↦ −d`.

All four verified exactly at `p = 43, 67, 79, 127, 163` (controls C1–C4, no exceptions).

## 2. The two kills

**(a) `N(κ)` against `χ₂(y)`: forced by parity.** `N(−κ) = N(κ)`, so `N` is even while `c` is odd;
pairing `d ↔ −d` cancels term by term. `Σ_d c(d)·f(N(κ(d))) = 0` **identically, for every `f`** — no
sample size helps. Verified exactly (`f` = `N`, `N mod 3`, `N mod 7`, `[N even]`; all 0 at 5 curves).

**(b) `det(κ(d), κ(d⁻¹))` against ANY curve-native readout: doubly forced.** Beyond parity, there is
an orbit identity. Let `Ω` be multiplication by `ω` (a rotation, `det Ω = 1`, `Ω³ = I`). GLV
reduction is μ₃-equivariant: `κ(λd) = Ω κ(d)` (verified — `N` is constant on μ₃-orbits). Then
`κ((λd)⁻¹) = Ω²κ(d⁻¹)`, and

`det(Ω^k u, Ω^{2k} v) = det(Ω^{2k} u, v)` ⇒ `Σ_{k=0}^{2} det(Ω^k u, Ω^{2k}v) = det((I + Ω + Ω²)u, v) = 0`

> **because `1 + ω + ω² = 0`.**

So the determinant sums to **zero over every μ₃-orbit**. Every legal curve readout is μ₃-invariant
(forced, §1), so the determinant is annihilated against **all of them** — `χ₂(y)` *and* `χ₂(x)`.
Verified: `det(d) + det(ωd) + det(ω²d) = 0` for **every** `d` at all 5 curves; both readout sums
exactly 0. **The Eisenstein structure that makes the lattice attractive is exactly what kills this
statistic.** `det` is not weakly informative here; it is identically uninformative.

**(c) The sextic sector against `χ₂(y)`: nearly all of it is forced.** μ₃-invariance needs
`f(s+2) = f(s)`; oddness needs `f(s+3) = −f(s)`. Together these leave a **one-dimensional** space,
`f(s) = (−1)^s`. Every other sector weighting is forced to zero. The survivor measures `±6` at every
prime tested — flat, and at high tautology risk (sector parity is close to the readout's own sign
structure). Not a lane.

## 3. What survives — and it is the record's own open item

The pairing rule that generates legal probes:

> **(feature parity under `d ↦ −d`) × (readout parity) must be EVEN**, and the feature must not
> be annihilated by the μ₃ orbit-sum.

`N(κ)` is even and μ₃-constant. So it is legal against an **EVEN** readout — `χ₂(x)`, `χ₃(x)`,
`χ₆(x)`, sextant of `x`. **Control fires:** `Σ_d χ₂(x)·f(N)` moves at every prime
(−60, −192, +222, −114, … vs the forced 0 in the odd column). The instrument is live, not dead.

This lane is exactly the item the record carries as **OPEN with no statistic projecting onto it**:
`h_k[m·d] = h_k[d]` forces the readout onto the μ₃-invariant subspace, `N(κ)` and the reduced
representative's position **are** the natural coordinates on that quotient, and the pairing is
disjointly constructed — feature from the scalar's lattice position, target from the curve point —
so it does not repeat the residue-vs-component tautology.

**It has never been run.**

## 4. Scope flags

- **Generation-side.** *"If the puzzle generation relies on the curve's geometry, it will scar these
  local lattice invariants"* is a hypothesis about **how the scalars were chosen**, under a standing
  hard ban, and its natural matched null is a generator pool — also permanently out of scope. The
  in-scope form of the same object asks whether the **curve** couples the lattice coordinate to the
  point readout, with scalars constructed freely at any bit-length. That is what §3 specifies.
- **The rigidity does not lower the shortscalar arm's noise floor.** The 120° lock bounds the
  **complete** sum `|V| ≤ 2√p`. The shortscalar statistic is an **incomplete** sum over `B ≪ √p`,
  whose variance comes from the interval — which is precisely why no character-sum bound reaches it
  and why the channel is open. There is no global-curve variance being removed from that arm.

## 5. Instance count

This is the **5th** logged case of a probe forced to zero before any data (after the quadratic-chirp
alignment cap, the phase-family "odd phase AND a bijection" rule, the `a²` even-index annihilation,
and the readout×index-set parity catch). It is the first where the forcing was found **before** the
probe was built rather than after it returned a null. The pre-screen cost one script.
