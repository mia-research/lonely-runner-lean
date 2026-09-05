> **CORRECTED by `RESULT_t1b_tail_geometry_v1.md`.** The pooled k≈1.4 below is a GEOMETRY MIXTURE, not
> a curve-global exponent: split by geometry, the sub-Rayleigh tail is entirely on the y-only (b=0) axis
> (k≈1); the x-only axis and the c=±b diagonal are Rayleigh (k≈2). Do not cite k≈1.4 as a property. The
> "new structure exists" conclusion stands, but LOCALIZED to the y-axis.

# RESULT — T1b.0: the real |U| tail is SUB-RAYLEIGH (k≈1.4) — a NEW structural fact; its relation to the −13.99σ deficit is UNTESTED

**Date:** 2026-08-11. **`[PROVISIONAL — experiment-designer unavailable]`** (gate hit a session limit;
this is a gate-free CHARACTERIZATION; the paired verdict T1b.1 is gate-owed — see
`PREREG_cbpm_phase_deficit_v1.md`). Anomaly-drill characterization (a sharper law + a next probe),
**not a verdict about the deficit**. **Artifact:** `scratchpad/t1b_tail_exponent_v1.py`. Float carve-out:
`|U|` magnitudes are analytic-size with integer args in the sum; distributional-shape fit, no key in the
arg path, no matched-null verdict.

## The finding (state it as the positive it is)
The exponent `k` in `P(|U(a,b,c)|/√n < ε) ~ ε^k`, pooled over `a≠0` and `(b,c)` = {x-axis, y-axis, c=±b
diagonal, generic}, real curve sum `U=Σ_d e_p(bx_d+cy_d)e_n(ad)` vs a random-unit-phase target:

| p | n | k_real | k_random (Rayleigh ref) |
|---|---|---|---|
| 547 | 547 | 1.563 | 1.922 |
| 1303 | 1249 | 1.411 | 1.895 |
| 2089 | 2143 | 1.410 | 1.981 |

- **The reference calibrates:** `k_random ≈ 1.9–2.0` (method recovers Rayleigh for a true complex-Gaussian
  target — not biasing the exponent).
- **NEW STRUCTURE: the real curve sum is sub-Rayleigh, `k_real ≈ 1.41–1.56`, robustly below Rayleigh on
  all three curves, stabilizing near ~1.4** (not decaying to the real-trace value 1). An **intermediate**
  exponent — a magnitude/structure with a home (consistent with `A_new` being a 2-D CM abelian surface: a
  trace of two complex eigenvalue contributions, neither 1-D real nor full complex-Gaussian). This is a
  lead to characterize further, not a nuisance parameter.

## Its relation to the −13.99σ deficit is UNTESTED (this is the open question, not a conclusion)
- The deficit is reported to have **survived a value-multiset (shape-preserving) matched null.** A
  marginal-shape fact therefore does **not**, on its face, explain it — a shape-matched null already
  controls for the marginal `|U|` distribution. So this sub-Rayleigh finding is an **additional**
  structural fact alongside the deficit, not a debunk of it. The deficit stands as the real,
  matched-null-surviving signal it was.
- **What is genuinely open (T1b.1, gate-owed):** re-score the deficit against a null matched to the
  sub-Rayleigh symmetry-type characterized here; is the deficit unchanged (expected, since it already
  survived a shape null), sharper, or is any part of it attributable to the marginal? **I do not predict
  the outcome.** The two findings (sub-Rayleigh marginal; the deficit) coexist until the test relates them.
- Both are structure. Neither diminishes the other absent the test.

## Scope / provisional caveats
- **PROVISIONAL** (§2a): no grade promotion; the matched-control-adequacy and falsification frame layers
  are un-isolation-reviewed (self-audit in the prereg); gate owed.
- The exponent fit is a 6-point log-log slope — the robust claim is the DIRECTION (`k_real < k_random`,
  sub-Rayleigh, ~1.4), not the exact value.
- Pooled over the listed `(b,c)`; per-`(b,c)` and the c=±b-only exponent are not separated here.

## Next (owed)
- **Gate:** re-run experiment-designer on `PREREG_cbpm_phase_deficit_v1.md` when the session limit resets.
- **T1b.1:** relate the sub-Rayleigh marginal to the deficit by re-scoring against the correct-shape null
  (outcome not pre-judged).
- **Characterize the sub-Rayleigh exponent itself** (T1a-adjacent): does `k≈1.4` split by the c₂
  cubic-residue class of `a`, or by the c=±b diagonal vs axes? That is a new object worth its own probe.
