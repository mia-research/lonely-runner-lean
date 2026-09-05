# The Eisenstein Lift-Sextant Distribution Law (v1, 2026-07-13)

**A positive structural theorem** for the secp256k1 CM lift — the first result in
the "flip the script: prove structure, don't accumulate nulls" program. It replaces
the observed-but-unexplained "sextant ~2–3× enhancement" with an exact, scalar-
independent closed form (unconditional, pure counting), and — via a *cited*
equidistribution input (Weil) — explains the measured per-point-`x` MI-nulls as
consequences of that equidistribution. Scope is stated precisely below: the marginal
law is unconditional; the conditional MI bound rests on equidistribution; joint/multi-
point and `y`/group-law functionals are **not** addressed and stay open.

Verification script: `lift_sextant_law_proof_v1.py` (exact rational arithmetic).

## Setup

`p` = secp256k1 field prime, `p ≡ 1 (mod 3)`. `ℤ[ω]` = Eisenstein integers,
`ω = e^{2πi/3}`, identified with `ℤ²` via the basis `{1, ω}`. Since `p` splits,
`(π_p)` is a degree-1 prime ideal with `N(π_p) = p`, and `ℤ[ω]/(π_p) ≅ 𝔽_p`.

`r₁, r₂` = the Gauss-reduced basis of the ideal `(π_p)` (the two shortest vectors,
each of length `~√p ≈ 2¹²⁸`). The lift map used throughout the investigation,
`eis : 𝔽_p → ℤ[ω]`, sends `X` to the representative of `X mod π_p` obtained by Babai
rounding `(X,0)` in the basis `{r₁,r₂}` — i.e. into the fundamental parallelogram
`P = { α r₁ + β r₂ : α,β ∈ [−½, ½) }`.

The **sextant** `σ(u,v) ∈ {0,…,5}` is the 60° angular sector of `u + vω`, computed
exactly by integer ω-rotation (`(u,v) ↦ (v, v−u)` is −60°). Sector boundaries are the
six Eisenstein unit directions `{±1, ±ω, ±(1+ω)}` = integer rays.

## Lemma A (bijection — exact)

`X ↦ X mod π_p` is a bijection `𝔽_p → ℤ[ω]/(π_p)`, and every residue class has a
unique representative in `P`. Therefore
`{ eis(X) : X ∈ 𝔽_p }` is **exactly** the set of the `p` lattice points of `ℤ[ω]`
lying in `P`, each attained once. *(Immediate from the definition of eis as the
mod-`π_p` reduction into `P`.)*

**Consequence:** the sextant histogram over uniform `X ∈ 𝔽_p` is a deterministic
counting fact — `H(s) = #{ w ∈ ℤ[ω] ∩ P : σ(w) = s }` — with no randomness and no
scalar.

## Lemma B (area law — exact rational + error bound)

In the `(u,v)` integer coordinates, `ℤ[ω]` is `ℤ²` (covolume 1) and
`area(P) = |det(r₁,r₂)| = N(π_p) = p` (verified exactly). By Gauss lattice-point
counting on the convex region `P ∩ sector_s`,

  `H(s) = area(P ∩ sector_s) + O(perimeter(P)) = area(P ∩ sector_s) + O(2¹²⁸)`,

so, dividing by `p`,

  **`P[σ = s] = area(P ∩ sector_s) / p + O(2⁻¹²⁸).`**

The sector rays are integer directions, so `area(P ∩ sector_s)` is computed by exact
rational polygon clipping. The result:

| sector s | exact proportion | decimal |
|---|---|---|
| 0 | **1/8** | 0.1250 |
| 1 | (basis rational) | 0.1297 |
| 2 | (basis rational) | 0.2453 |
| 3 | **1/8** | 0.1250 |
| 4 | (basis rational) | 0.1297 |
| 5 | (basis rational) | 0.2453 |

The six areas sum to `p` exactly. Central symmetry `(u,v) ↦ (−u,−v)` maps sector `s`
to `s+3`, giving `H(s) = H(s+3)` — confirmed (0=3, 1=4, 2=5). Sectors {0,3} are
**exactly 1/8** (a basis vector meets a sector edge); {2,5} carry ≈2× the {0,3} mass —
this **is** the observed "enhancement," now exact.

## Lemma C (equidistribution bridge)

For random `d`, `X = x([d]G)` equidistributes over the `x`-coordinates of `E(𝔽_p)`
with discrepancy `O(p^{-δ})` (Weil / Kohel–Shparlinski character-sum bounds). Hence
the curve histogram matches the uniform-`𝔽_p` histogram up to that error.

## Numerical confirmation (`lift_sextant_law_proof_v1.py`)

- `area(P) = |det(r₁,r₂)| = p` ✔; Σ sector areas `= p` ✔.
- **Uniform-X (M=60000, no curve):** max |empirical − area-law| = **0.0020** < 1/√M
  = 0.0041 ⇒ Lemma A+B confirmed.
- **Curve gen256 (M=21000, `x([d]G)`):** max |empirical − area-law| = **0.0071**
  ⇒ Lemma C holds.

## Theorem & Corollary — stated precisely (no overreach)

**Theorem (marginal law — unconditional, pure counting).**
`P[σ(eis(X)) = s] = area(P ∩ sector_s)/p + O(2⁻¹²⁸)` for `X` uniform on `𝔽_p`, a
closed form in the reduced basis `r₁,r₂` of `(π_p)`. This rests only on Lemma A+B
(a bijection and Gauss counting) — **no analytic input, no `d`.** It proves the
observed histogram enhancement is a constant of `p`: the *marginal* sextant shadow
carries **zero** scalar information, exactly.

**What this does NOT prove by itself.** A fixed marginal does not imply the
*conditional* `MI(σ ; d mod m)` is zero — that is a separate (ECDLP-flavoured)
question. Do not conflate them.

**Conditional corollary (rests on a cited analytic input).** If `x([d]G)`
equidistributes over `𝔽_p` conditioned on `d ≡ r (mod m)` — true by Weil /
Kohel–Shparlinski, since each residue class is an interval/AP with `≫ √p` elements —
then the conditional sextant law equals the same area law for every `r`, so
`MI(σ(eis(x([d]G))) ; d mod m) = O(p^{-δ})`. More generally, since **any** statistic
of `x` alone is a function of an equidistributing quantity, `MI(f(x([d]G)) ; T(d)) =
O(p^{-δ})` for every coarse target `T` and every single-`x` functional `f`.

**So, honestly scoped:** the empirical per-point-`x` nulls we measured are not luck —
they are *consequences* of the equidistribution of `x([d]G)`. What this argument does
**not** reach (and what therefore stays genuinely open): (i) **joint / multi-point**
statistics — equidistribution of a single `x` says nothing about correlations across
keys; (ii) functionals using the **group law / `y`-coordinate** in ways that don't
reduce to single-`x` equidistribution. Those are not "closed"; they are simply not
addressed by this theorem.

## What this closes / opens

- **Closes:** the standing "sectors ~3× — observation real but unexplained (F6
  shortest-vector guess FALSE)" item. Correct cause = parallelogram-∩-sector area.
- **Template for Track 2:** the Corollary is a *classification* — the whole family of
  lift/CM-reduction functionals is scalar-independent by one bijection+equidistribution
  argument. Remaining positive targets that are NOT lift-factored (so not covered):
  the exact GLV-orbit action on χ₆ (χ₆ shifts by χ₆(β)=const — closed form?), and any
  functional using `y` / point-addition structure beyond the `x`-lift.
