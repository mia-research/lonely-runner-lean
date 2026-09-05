# Lift-Sextant Law — Reviewer Clarifications (v1, 2026-07-13)

Precise answers to six technical questions on `lift_sextant_rhombus_law_v2.md` /
`lift_chi6_uniform_law_v1.md`. Each point is tagged by epistemic status:
`PROVED` (symbolic/exact) · `VERIFIED-INSTANCE` (exact, specific inputs) ·
`EMPIRICAL` (finite sample) · `CITED` · `ASSERTED`.

## 1. Error term — absolute vs relative  [corrected]

The reviewer is right; the v1 write-up's `O(2⁻¹²⁸)` conflated absolute and relative.
Gauss lattice counting on a convex region gives absolute error `O(perimeter)`.

- **Absolute** (count): `|H(s) − area(P ∩ sector_s)| = O(perimeter) = O(√p)`.
  Perimeter `= 2(|R₁|+|R₂|) ≈ 4√p ≈ 2¹³⁰` for secp. `[EMPIRICAL]` across primes
  `5·10³…1.3·10⁴`: `|H(s)−area|/√p ≈ 0.5–0.6` (bounded, non-growing) and
  `perimeter/√p ≈ 4.0` — so the absolute count error for secp is `≈ 0.6·√p ≈ 2¹²⁷`
  (rigorously `≤ perimeter ≈ 2¹³⁰`).
- **Relative** (proportion): dividing by `p`,
  `P[σ=s] = area(P ∩ sector_s)/p + O(p^{-1/2})`, numerically `≈ 2⁻¹²⁸` (with the
  perimeter constant, `≈ 0.6·2⁻¹²⁸`). This is the quantity the theorem should state, and
  it is a **relative** bound. `[CITED: Gauss lattice-point counting]`

So: the marginal proportion is uniform-`𝔽_p`-exact to relative `O(p^{-1/2})`; the pinned
`1/8` is exact as an **area/proportion** (`[PROVED]`, symbolic), but the integer **count**
`H(s)` is `p/8 + O(√p)`, not an integer multiple of `p/8` (`p` is odd).

## 2. Conditional equidistribution under `d ≡ r (mod m)` — which `m`?  [safe]

`[VERIFIED-INSTANCE]` The empirical MI-nulls conditioned on `m ∈ {2,3,5,6,7}` and a
single mid-bit (`angular_interference_scaling_v1.py:149–152`). For a full-range key set
(`gen256`, `d ~ 2²⁵⁵`), each class `{d ≡ r (mod m)}` is an AP of length `≈ N/m ≈ 2²⁵⁵/7`,
which is `≫ √p ≈ 2¹²⁸` by a factor `~2¹²⁷`. `[CITED: Weil / Kohel–Shparlinski]` The
character sum has square-root cancellation with this many points, so the conditioning does
**not** degrade the bound at these `m`. The reviewer's caveat (degradation for `m ≳ √p`)
is real but only bites at `m ~ 2¹²⁸`, far outside anything measured. `[SCOPE]` This
applies to full-range keys; the small real puzzle keys (`d < √p`) do **not** equidistribute
and are explicitly outside this argument (that non-equidistribution is the kangaroo regime).

## 3. "Fine" functionals (Babai rounding beyond the residue class)  [covered]

`[PROVED, given Lemma A]` `eis : 𝔽_p → ℤ[ω] ∩ P` is a **bijection**, so `eis(X)` is a
deterministic function of `X`. There is exactly **one** lattice point per residue class in
`P` (the Babai representative), chosen deterministically — the "which point in the class"
freedom the reviewer asks about is empty here. Concretely the rounding coefficients
`(c₁,c₂)` with `eis(X)=X−c₁R₁−c₂R₂` are themselves functions of `X`
(`cᵢ = rdiv(…X…, det)`). Hence **every** functional of the lift — coarse or fine — factors
through `X`, and is covered by the marginal pushforward (and by the equidistribution for the
conditional). A functional can carry scalar information beyond equidistribution only by using
data **not** a function of `x` — i.e. `y` or the group law — which is the stated open
frontier, not a single-`x` functional. `[VERIFIED]` Every functional actually measured
(sextant, norm, `χ₂/χ₃/χ₆`, GLV-sector, lift angle) is a function of `x`/`eis(x)`; none used
`y` or `d` beyond `x`.

## 4. Exact rational proportions for the free sectors  [closed form in R₁,R₂]

`[PROVED]` (symbolic, sympy). They are exact rational functions of the integer components
`R₁=(a,b)`, `R₂=(c,d)` — not merely numerical. For secp's combinatorial cell (pinned pair
`{0,3}`):

- **sectors `{1,4}`:** `H/p = |det(R₁,R₂)| / (8·|a(a−b)|) = p / (8·|a(a−b)|)`.
- **sectors `{2,5}`:** `H/p = |ab + 2ad + cd| / (8·|ad|)`.
- **sectors `{0,3}`:** `1/8`.

Check: `1/8 + 0.129659… + 0.245341… = 1/2` ✓ (secp values). These are *piecewise*-rational:
which rays cross which rhombus edges depends on `θ`, so a different prime (different pinned
pair) gives an analogous rational expression from a different cell. The universal
one-parameter form is `p₀(θ)=(3/4)|cos2θ|/(2cos2θ+1)`, `θ = arg(π_p) mod 60°`
(`[PROVED]` symbolic; matches the exact rationals to `1.7e-16` over 150 primes).

## 5. Same as (2)

`m ∈ {2,3,5,6,7}` + one mid-bit — the small-`m` (safe) regime. No large-`m` argument is
relied upon.

## 6. Status of the "remaining open" items  [honest]

- **GLV-orbit on `χ₆`: RESOLVED, not open.** `[PROVED/VERIFIED]` `χ₆(βx)=χ₆(x)+4 (mod 6)`
  exactly (`glv_orbit_structure_*`); it relates the deterministic GLV conjugates
  `{x, βx, β²x}` (= `x` of `[d]G, [λd]G, [λ²d]G`) and carries **no** scalar information about
  `d`. It is a closed-form relation, not a candidate leak.
- **`y` / group-law: no data suggests a leak.** `[EMPIRICAL]` Every `y`/group-law test the
  investigation has run returned null (nonce recovery null; `(X,Y)→key` null at `~10⁻⁵` bits
  with control firing). So these are **not** "promising / not-yet-ruled-out with a signal";
  they are *empirically null so far*, and "open" only in the sense that absence-of-leak is
  not provable (and cannot be — the standing rule). There is no positive indication that any
  `y`/group-law functional carries scalar information.
