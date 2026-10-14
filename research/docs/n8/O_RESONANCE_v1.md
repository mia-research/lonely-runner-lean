# `o` classified by resonance: the exact limits, and (H″) survives its counterexample hunt

2026-09-09. Continues `O_STRUCTURE_v2.md`. Machinery: `experiments/n8/{ob_core_v1,
ob_fast_v1, hp_omax_v1, hp_resonance_limit_v1, hp_reshunt_v1}.py`. Exact Fraction /
integer arithmetic; cells evaluated at their **entry** point.

## 1. The normal form  `[PROVED]`

Write `s_ρ = 2a_ρ + 1` with `a_ρ = ⌊e_ρ x/2⌋ mod 4`. In the coordinate `a = (u−1)/2` the
group `(ℤ/8)^×` becomes `(ℤ/2)²` under XOR. Putting `μ_ρ = (ρ−1)/2` (so `μ = 0,1,2,3`
for `ρ = 1,3,5,7`) and `ν_ρ = a_ρ ⊕ μ_ρ`:

    O = { x : ν_1, ν_3, ν_5, ν_7 are all distinct }.

**Quadrant form.** `a_ρ(x) = ⌊4·frac(e_ρ x/8)⌋`, so with `θ = x/8` the value `a_ρ` is
the *quadrant index* of `e_ρθ mod 1`. Hence `o` is a question about the closed geodesic
`θ ↦ (e_ρ θ)_ρ` on `T⁴` and which quadrant each coordinate occupies — which is why
resonances `n·e = 0` are the controlling structure.

## 2. Exactly two `±1` relations are possible  `[PROVED]`

For a `±1` vector `σ`, `Σσ_ρ e_ρ ≡ Σσ_ρ ρ (mod 8)`. Enumerating the eight sign vectors
with `σ_1 = +1`:

| `σ` | `Σσ_ρ ρ` | mod 8 | |
|---|---|---|---|
| `(1,1,1,1)` | 16 | 0 | excluded: all speeds positive, sum cannot vanish |
| `(1,1,1,−1)` | 2 | 2 | impossible |
| `(1,1,−1,1)` | 6 | 6 | impossible |
| `(1,−1,1,1)` | 10 | 2 | impossible |
| **`(1,1,−1,−1)`** | **−8** | **0** | **admissible** — family B, `e_1+e_3 = e_5+e_7` |
| `(1,−1,1,−1)` | −4 | 4 | impossible |
| **`(1,−1,−1,1)`** | **0** | **0** | **admissible** — family A, `e_1+e_7 = e_3+e_5` |
| `(1,−1,−1,−1)` | −14 | 2 | impossible |

**A and B are mutually exclusive**: together they give `2e_1 + e_3 + e_7 = e_3 + 2e_5 +
e_7`, so `e_1 = e_5` — impossible since `e_1 ≡ 1` and `e_5 ≡ 5 (mod 8)`. So the `±1`
resonance lattice has rank at most 1.

## 3. The exact limits  `[DERIVED + numerically confirmed]`

Under the standard law — the geodesic equidistributes on the subtorus cut out by its
low-height resonances — the limiting value of `o` is:

| class | `o_∞` |
|---|---|
| no low resonance | `3/32 = 0.09375` |
| one relation, `e_1+e_7 = e_3+e_5` | `1/6 ≈ 0.16667` |
| one relation, `e_1+e_3 = e_5+e_7` | `1/6 ≈ 0.16667` |
| the next height class | `65/256 ≈ 0.25391` |

**Every limit is below `1/3`.** For family A the derivation is explicit: the relation
forces `j_7 ≡ j_3 + j_5 − j_1 + d (mod 4)` with `d = ⌊s_3+s_5−s_1⌋ ∈ {−1,0,1}` at
probabilities `1/6, 2/3, 1/6`. Confirmed numerically along the family — `o − 1/6` runs
`1.24e−1, 3.70e−2, 8.67e−2, 4.93e−3, 1.92e−3, 4.61e−4, 8.71e−5, 9.05e−6` as the speeds
grow. The non-resonant limit `3/32` matches six random tuples with speeds in the
hundreds (`0.0917…0.0943`) and the direct state count `384/4096`.

## 4. (H″) survives a hunt designed to break it  `[EMPIRICAL — targeted, not random]`

The margin between the observed non-resonant maximum and `1/3` is only about `0.02`, so
a counterexample was a live possibility. Random sampling is the **wrong** instrument —
it lands on non-resonant tuples where `o → 3/32`. The danger zone is *resonant* tuples
at *moderate* speeds: far enough from the limit that `o` has not settled, large enough
to sit outside the exhaustive small sweeps. So the families of §2 were swept directly.

| sweep | count | max `o` | attained at | `o > 1/3` outside the two exceptions |
|---|---|---|---|---|
| exhaustive, all tuples, speeds ≤ 71 | 6561 | `16/35` | `(1,3,5,7)` | 0 |
| exhaustive, **non-resonant**, speeds ≤ 71 | 5544 | `186/595 ≈ 0.3126` | `(17,3,5,7)` | 0 |
| **resonant families A and B**, speeds ≤ 295 | 3409 | A: `16/35`, B: `26/77` | `(1,3,5,7)`, `(1,11,5,7)` | **0** |

In each family the maximum is attained at that family's **minimal** member, and `o`
decreases along the family toward `1/6`.

## 5. Where (H″) now stands

> **(H″)** `o ≤ 1/3` for every primitive unit 4-tuple other than `(1,3,5,7)` and
> `(1,11,5,7)`.

The two exceptions are exactly the minimal members of the only two possible resonance
families. `(1,11,5,7)` has `u = 0` and closes by the `u = 0` bound; `(1,3,5,7)` is the
representative tuple closed by Lemma D. So (H″) finishes the leaf.

**What remains is a convergence rate.** The limits are all `≤ 65/256 < 1/3`, so `o > 1/3`
forces the tuple to be far from its limit, which forces small speeds. Making that
explicit — an effective bound `|o − o_∞| ≤ C/‖e‖` with `C` named — reduces (H″) to a
finite check, and §4 shows what that check finds.

## 6. Grades

§1 (normal form, quadrant form) and §2 (exactly two admissible relations, mutually
exclusive): **PROVED**. §3: **DERIVED** under equidistribution on the resonance
subtorus, and confirmed numerically to `9×10⁻⁶`; not proved unconditionally. §4:
**EMPIRICAL**, exhaustive over the stated ranges — and a targeted hunt, not a random one.
(H″): **OPEN**, now with its extremal cases classified and its remaining content
isolated to an effective convergence rate.
