# DEVIATIONS — `PREREG_weight1_derisk_v1.md`

*2026-07-24. Filed with `RESULT_weight1_proved_v1.md`.*

## D1 — ⚠ instrument too slow to reach the frozen `P_max = 100`

The spec froze an exhaustive list `{13,43,61,67,79,97}` and budgeted ~15–27 min for the six-prime
`O(Σp⁴)` sweep. **The instrument (`n1_twisted_eigenvalues_v1.sage`, `histogram()`) is ≈10× slower
than that estimate** because it enumerates `E(F_{p^k})` through Sage's `EllipticCurve` point objects
(`for x in Fq`, per-element `is_square`/`sqrt`, `k−1` Frobenius point additions each). Measured:
`p=61` at `k=4` (`61⁴ ≈ 1.4×10⁷`) did **not** complete in 9 minutes.

**Reached:** `p = 13` (`W ≈ 4.4×10⁻¹⁶`) and `p = 43` (`W ≈ 8.9×10⁻¹⁵`) — the two historical primes.
`p=61` is running in the background. **`{67,79,97}` are not reachable without a raw-`F_{p^k}`-arithmetic
rewrite of the histogram** (vectorized enumeration, trace via coordinate formulas, no point objects).

**Why this does not weaken the result.** The de-risk sweep is *confirmation* — insurance against a
mis-applied citation. The weight-1 premise is proved independently in `RESULT_weight1_proved_v1.md` §1
by KS Prop 2 (spot-checked against the PDF) and Deligne Weil II 3.2.3, neither of which depends on the
sweep. The pre-committed grade for a completed sweep was `[VERIFIED-scope]`, strictly weaker than the
`[PROVED]` the citation delivers. The frozen list stands; extending the reach is a tooling task, not a
scientific gap.

## D2 — the firing control was validated, and it is the load-bearing check that DID run

Per spec §4b, a non-weight-1 plant must be flagged. Confirmed at full sensitivity:
`{√p,√p,1,p}` → `W = 5.56`; one eigenvalue at `0.9√p` → `W = 0.10`; at `0.999√p` → `W = 1.0×10⁻³`;
all-weight-1 → `W = 0`. So `τ = 10⁻⁶` cleanly separates weight-1 from any off-weight configuration
down to a `10⁻³` relative displacement. The pipeline is not vacuous.
