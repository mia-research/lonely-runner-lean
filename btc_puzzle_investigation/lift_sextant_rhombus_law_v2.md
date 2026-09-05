# The Eisenstein Lift-Sextant Rhombus Law (v2, 2026-07-13)

Strengthens `lift_sextant_law_v1.md`. v1 proved, for secp's prime `p`, that the
lift-sextant marginal is an exact area law over the fundamental domain `P` of
`(π_p)`, and reported the numbers `{0,3}=1/8`, `{1,4}=0.1297`, `{2,5}=0.2453` as
opaque, seemingly `p`-specific rationals. v2 identifies the geometric object those
numbers come from and proves the law for **every** prime `p ≡ 1 (mod 3)` as a
**one-real-parameter closed form**.

Verification: `lift_sextant_rhombus_law_proof_v2.py` (exact rational areas;
symbolic identity for the invariant; real-analytic closed form cross-checked to
`1.7e-16` over 150 primes and against the pipeline's own `eis()/sextant()`).

## What v1 left implicit

v1's `P` is the Gauss-reduced fundamental parallelogram of the ideal `(π_p)`. v1
computed its sector areas but did not name its shape or say why `1/8` appears.
Both reduced basis vectors turn out to have **Eisenstein norm exactly `p`** — the
tell that `P` is not a generic parallelogram.

## Theorem 1 (rhombus — unconditional, all `p ≡ 1 mod 3`)

The two Gauss-reduced basis vectors `R₁, R₂` of `(π_p)` each have Eisenstein norm
exactly `p`; i.e. both are **associates** `ζ·π_p` of the CM prime (`ζ` a unit
sixth-root of unity). Hence `P` is a **60° rhombus** whose four vertices `±(R₁±R₂)/2`
lie among the six shortest vectors `{ζ·π_p}` (a regular hexagon).

*Proof.* A nonzero ideal element is `α·π_p`, of Eisenstein norm `N(α)·p`, minimized
at `N(α)=1`, i.e. `α` a unit — norm exactly `p`. The six units give a hexagon of
shortest vectors; two adjacent ones generate `(π_p)` and are Gauss-reduced (60°
apart, equal length). Since `N(w)=u²−uv+v² = |w|²` is the **true** squared length in
the `{1,ω}` embedding, both edges have true length `√p` and the rhombus has area
`p·(√3/2)`. ∎ *(Verified `N(R₁)=N(R₂)=p` for all 300 primes `p≡1(3)` in `[7,4513]`
and for secp.)*

## Theorem 2 (one-parameter closed form)

Because `P` is a `√p`-edge 60° rhombus, the entire sextant histogram is a function
of a **single** real parameter — the rhombus orientation
`θ = arg(π_p) mod 60°` (fold to `[0°,30°]`, since `θ` and `60°−θ` give mirror-image
rhombi with identical proportion values). With `H(s) = area(P ∩ sector_s) + O(√p)`:

| opposite-pair | proportion `H(s)/p` |
|---|---|
| pinned pair | **exactly `1/8`** (θ-independent) |
| free pair A | `p₀(θ) = (3/4)·|cos 2θ| / (2 cos 2θ + 1)` |
| free pair B | `3/8 − p₀(θ)` |

Central symmetry `(u,v)↦(−u,−v)` forces `H(s)=H(s+3)`, so there are three
opposite-pairs; they sum to `1/2`. `p₀` runs monotonically from `1/4` (at `θ=0°`,
degenerate: a third sector also hits `1/8`) to `3/16` (at `θ=30°`, where the two
free pairs coincide). *(Closed form matches the exact rational areas to `1.7e-16`
over 150 primes.)*

## Theorem 3 (the `1/8` is a universal invariant, and never the maximal pair)

For every `p ≡ 1 (mod 3)`, **exactly one opposite-pair** of sextants has area
**exactly `p/8`**, independent of `θ`. This is a rhombus-symmetry fact, proved as a
symbolic identity: in the unit-edge model the pinned wedge area is identically
`√3/16 = (√3/2)/8`, with no `θ` dependence. The pinned pair is always the `{0,3}` or
`{1,4}` class — **never** the maximal `{2,5}` pair (the one containing the long
diagonal). *(Verified: exactly 2 sextants `= 1/8` for all 300 test primes; pinned
class `∈ {0,1}`, never `2`; and the max-pair-exclusion asserted per prime.)*

## secp256k1 instance

`θ = arg(π_p) = 50.55° ≡ 9.45° (mod fold)`. Pinned pair `{0,3} = 1/8`; free pairs
`p₀ = 0.2453` (sectors `{2,5}`) and `3/8 − p₀ = 0.1297` (sectors `{1,4}`) — exactly
v1's rationals, now read off one angle. The v1 statement "`{0,3}=1/8`" is the
`θ_secp`-specific label of the universal invariant; generically (188 of 300 primes)
the pinned pair is `{1,4}` instead. The `≈2×` "enhancement" of `{2,5}` is
`p₀(θ)`/`(1/8)` for secp's `θ`, i.e. `0.2453/0.125 = 1.96×`.

## Scope — what v2 adds and what it still does not reach

**Strengthened over v1:**
- from "closed form at one `p`" to "closed form for the whole family, one parameter";
- the `1/8` is explained (rhombus symmetry) and shown universal-to-a-pair, correcting
  v1's implicit reading that `{0,3}=1/8` was structural to secp;
- the messy free-sector rationals are demystified as `p₀(θ)` at `θ_secp`.

**Umbrella (unchanged from v1's Lemma A, now sharper).** The lift multiset
`{eis(X) : X ∈ 𝔽_p}` is *exactly* the `p` lattice points of `ℤ[ω]` in the rhombus `P`,
uniform. So **every** single-point functional `f(eis(X))` — sextant, norm-band,
sextic character `χ₆`, GLV-sector — has a marginal that is a deterministic pushforward
of Uniform(`ℤ²∩P`): closed-form and scalar-independent. The sextant is the one case
now solved in full closed form; the others are the same theorem at a different `f`.

**Not reached (unchanged, still open):**
- **conditional** `MI(σ ; d mod m)`: still rests on the cited Weil / Kohel–Shparlinski
  equidistribution of `x([d]G)` (marginal is unconditional; conditional is not).
- **joint / multi-point** statistics across keys, and **`y`-coordinate / group-law**
  functionals that do not reduce to single-`x` equidistribution. A marginal law says
  nothing about these; they are not closed, merely not addressed.

## What this closes / opens

- **Closes:** "why `1/8`, and is it special to secp?" — answered: rhombus symmetry,
  universal to one opposite-pair, secp's is `{0,3}` by its `θ`.
- **Opens (positive-theorem track):** the same `Uniform(ℤ²∩P)` pushforward should give
  a closed form for the `χ₆` marginal (trivially uniform by character orthogonality —
  worth stating as the contrast case: angle is non-uniform, sextic character is exactly
  uniform) and for the GLV-orbit action on `χ₆`. Those are single-`x` and so covered in
  principle; joint/`y` remain the genuine frontier.
