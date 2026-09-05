# SCOPE — hand-rolled Tate pairing on Jac(C) for the f1–f4 pairing invariants (cost estimate, not a build)

**Date:** 2026-08-22. Answers "what does Phase 2's pairing route actually cost?" before committing.
Sage exposes no pairing on the genus-3 function-field Jacobian (`elt`/`J`/`G0` have no `*pair*` method),
so f1–f4 require a hand-rolled Tate pairing. Probe: `scratchpad/anew_p43_validation/miller_scope.sage`.

## The three primitives Miller needs — ALL work in Sage at p=43 (verified)
1. **Reduced divisor of a Jacobian element:** `W.divisor()` → a `DivisorGroup` element. ✓
2. **Function from a principal divisor:** no `is_principal`, but the divisor exposes `function_space` /
   `basis_function_space`. For principal `D = div(f)`, `L(D)` is spanned by `1/f`, so `f` is recoverable
   as the reciprocal of the space's generator. ✓ (needs a few lines of care).
3. **Evaluate a function at an F_{p³} place:** deg-3 places exist; `x.evaluate(place)` returns an
   `F_{p³}` value (e.g. `2·z3²+14·z3+30`). ✓

## The build
Miller double-and-add for `t(Q_d, R) = f_{N,Q_d}(D_R)^{(p³−1)/N}`, `N = |A_new| = p²+p+1`:
- ~`log2(N) ≈ 26` iterations at p≈5827 (N≈3.4e7). Each iteration = one Jac doubling/add + extract the
  step's Miller function (primitive 2) + evaluate at `D_R` (primitive 3). Then one final F_{p³}
  exponentiation. Estimated **~50–100 lines**. The f1–f4 reads (Legendre of trace, F_p-norm, mod ℓ₀,
  subfield indicator) are then cheap F_{p³} coordinate functions of the result.

## Two scaling risks (this is where the cost lives)
1. **R's F_{p³} place cannot be enumerated.** deg-3 places number O(p³) (~2e11 at p=5827), so
   `L.places(3)` is infeasible at scale. R's support must be **constructed directly** (the place above a
   chosen degree-3 prime / a specified F_{p³} point) — added implementation, not covered by the probe.
2. **Per-point runtime.** ~26 iterations × (Jac group-op ~0.2s at p=2011 + Riemann-Roch function
   extraction via Singular) ≈ **~10–20s per point**. At N=1000 sample points × 2 primes that is
   **hours to overnight**. Genus-3 Riemann-Roch per step is the hot path.

## Scoped verdict / recommended shape
- **Feasible, moderate code, runtime-heavy.** No blocking primitive is missing; the cost is (a) the
  direct F_{p³}-place construction and (b) the per-point Miller runtime.
- **Recommended first pairing run at REDUCED scale** — p≈1447 (N=248, N_test=124, plant floor π=1/4)
  or a capped sample — to get a real f1–f4 read at a fraction of the runtime, before any p≈5827 run.
- Prerequisite still owed: a d-DEPENDENT, A_new-structure-free matched control (S_closed zeroes the whole
  A_new part, so it cannot discriminate a pairing-coordinate signal either).

*No leakage claim. This is a cost estimate for a future build, not the build.*
