# AUDIT — the proposed `shortscalar_glv_interval_harness_v1.py`: the test is null by construction

**Date:** 2026-08-01. **Script:** `AUDIT_shortscalar_glv_interval_harness_v1.py`.
**Verdict: DO NOT RUN AS WRITTEN.** One fatal defect, one structural finding that reshapes the
whole approach, two minor defects. The structural finding (§2) is the useful part.

---

## 1. FATAL — a 100% planted coupling reads `p = 1.0`

Handed a readout defined as `sign(N − median(N))` — a *perfect*, noiseless coupling to the feature —
the proposed test returns:

| input | exact perm p |
|---|---|
| real data at `2^128` | 719/2001 |
| **perfect plant (100% coupling)** | **2001/2001** |
| anti-plant | 2001/2001 |
| pure noise | 2001/2001 |

Plant, anti-plant and noise are **indistinguishable**, and the perfect signal reads *maximally
non-significant*. The test is not weakly powered; it is anti-powered.

**Mechanism.** A free shuffle preserves `T = Σ readouts`. Writing `N_i = N₀ + δ_i`,

`S = Σ r_i N_i = N₀·T + Σ r_i δ_i`

and the first term is **identical for every permutation**. Measured at `2^128`: `N₀ ~ 2²⁵¹` while
`max δ ~ 2¹³³` — so the permutation can only move the statistic by a relative `2⁻¹¹⁸` of its own
size. The comparison `|S'| ≥ |S|` is then decided entirely by the residual, and because the plant
arranges the residual to oppose `N₀·T`, every shuffle comes out *larger*. Hence `p = 1`.

A single plant control would have caught this before any interpretation. The proposed script has
**no controls at all** — no plant, no forced-zero check, no instrument validation.

## 2. STRUCTURAL — the GLV lift is *locally affine*, so the footprint carries no local information

This is the finding that matters, and it is not a bug — it reshapes the approach.

`c₁ = round(d·B₂/N)` changes by 1 only when `d` moves by `N/B₂ ≈ 2²⁵⁶/2¹²⁸ = 2¹²⁸`. Across an
interval of width 1000 at scale `2¹²⁸`, `c₁` and `c₂` are **constant**. Therefore, measured exactly:

> **`k₂` is CONSTANT across the interval, and `k₁` increments by EXACTLY 1.**
> (verified for all 1000 scalars, both the floor and the round variants)

So `N(κ(d₀+i)) = (k₁⁰+i)² − (k₁⁰+i)k₂ + k₂²` — a **deterministic smooth quadratic in the interval
index `i`**, varying by a relative `2⁻¹¹⁸`.

**Consequence.** Testing `χ₂(x)` against `N(κ)` on a short interval is testing `χ₂(x)` against a
low-order polynomial in `i`. Any smooth monotone weight gives the identical test. **Nothing
Eisenstein survives at this scale.** The lattice footprint is a *global* coordinate; it becomes
non-trivial only across intervals of width `~2¹²⁸`, at which point it is not a short interval.

The premise in the proposal's header — *"a short interval is symmetry-broken, so the statistic is
free to move"* — is correct about the μ₆ symmetry and irrelevant here. What kills the test is not a
forced symmetry; it is that **the feature is nearly constant**, so the statistic is dominated by a
permutation-invariant term.

## 3. MINOR

- **Babai rounding uses floor, not round-to-nearest.** `c1 = (d*B2)//N` should be
  `rnd_div(d*B2, N)`. Both give a *valid* decomposition (`k₁ + k₂λ ≡ d mod N` verified 200/200 for
  each), but floor yields `max bit-length 129` vs round's `128` — the vector is not the shortest.
  Real, and worth fixing, but not what breaks the test.
- **A float in the reported p-value** (`(pval_num/pval_den):.4f`). Display-only, so permitted, but
  it should carry the `# noqa: float` marker to pass the guard cleanly.
- `legendre(current_pt[0], P)` will raise if `current_pt` is ever `None`; unreachable at this scale,
  but unguarded.
- The Montgomery ladder and the incremental `point_add` stepping are **correct** — checked.

## 4. THE REPAIR — move the lattice coordinate to the interval level

The GLV footprint is constant *within* an interval and varies *across* intervals. So put it where it
varies:

> **Per-interval statistic:** `T(d₀) = Σ_{i<W} χ₂(x_{d₀+i})`, the incomplete character sum over the
> interval — this is the object that has no Weil bound and is the actual open channel.
> **Interval-level covariate:** the lattice position of the interval — `k₂`, or `(c₁, c₂)`, or the
> sector of `κ(d₀)`. These *do* vary from interval to interval.
> **Test:** across many intervals sampled at the `2¹²⁸` scale, does `T` correlate with the interval's
> Eisenstein coordinate?

That is well-posed, it is genuinely about the lattice geometry, it keeps the incomplete sum as the
object, and it is in scope (nothing about how any `d` was chosen). It also has an obvious plant
control: inject a coupling between `T` and `k₂` and confirm detection before reading real data.

Required before it runs: `experiment-designer` pre-registration (it is a leakage test), a firing
plant, and a matched null at the interval level — permuting `T` values across intervals, not
readouts within one.

## 5. What was right in the proposal

The scale argument (§ "The Unbounded Shortscalar Arena") is correct and is the reason this channel
is the target: the 120° lock bounds the **complete** sum, and an incomplete sum over `B ≪ √p` is not
bounded by it. The readout choice `χ₂(x)` is correct and legal. The insistence on exact integer
arithmetic is correct. The scope reasoning — that this assumes nothing about how `d` was created —
is correct.

The error is one level down: the feature was placed at the scale where it is constant.
