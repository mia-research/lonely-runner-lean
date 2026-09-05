# RESULT — the T2c carry-composition gives NO interval-DLP advantage: fair, measured, theorem-consistent

**Grade:** `[VERIFIED-scope — scoped null / no computational advantage; fair op-model, two model curves,
theorem-consistent. Model scale, ZERO secp power.]`
**Date:** 2026-08-26. **Prereg:** `PREREG_t2c_carry_partition_kangaroo_bench_v1.md` + deviations D1 (BSGS
solver), D2 (small model curves), **D3 (self-audit: v1 stacked the deck two ways; v2 fixes both)**.
**Canonical runner:** `t2c_carry_composition_bench_v2.py` (`check_no_float.sh` clean; ported GLV/eps
validated == `t2c_range_glv_structure_v1` on 300 secp d). The v1 runner
`t2c_carry_partition_kangaroo_bench_v1.py` is SUPERSEDED (its 14–21× "liability" was a per-run-setup
artifact — see D3).

**MODEL SCALE — ZERO secp power.** Curves have `n` ~ 2¹⁵–2²⁰ so the interval DLP is brute-force solvable
and every op-count is exact. secp's DLP is not solvable; nothing transfers to 2²⁵⁶. No ECDLP/security
claim. This closes the T2c "√6-composition" open item **honestly** — a measured no-lever, not a wall.

---

## What was asked, and the self-audit that reshaped it
The chosen frontier (GLV-carry lattice confinement) grounded to the corpus's one open T2c residual: does
composing the exact public carry partition with the endomorphism/kangaroo beat the interval-DLP baseline,
and does any gain grow with k? A user-prompted **adversarial self-review of the first runner found the
deck stacked two ways** (D3): (1) the v1 variant's per-run BSGS setup inflated a real null into a fake
"14–21× liability"; (2) v1 tested the 1-D interval partition, NOT the actual **2-D GLV composition**
(`P=[a]G+[b]φ(G)` with the carry as an `(a,b)` sign-region constraint), citing the λ-fold result by proxy.
Both are fixed in v2, with a group-op metric (baby steps + giant-steps-to-find, 1 unit each) applied
identically to the 1-D and 2-D solvers so no implementation mismatch tilts the ratio.

## FIX (a) — the 1-D carry partition gives NO speedup: R1D ≈ 1.0
One BSGS over `I`, giant steps reordered by the public carry prior (vs natural order). Median op-count
ratio R1D = variant/baseline:

| curve | k-values | R1D |
|---|---|---|
| n~2¹⁵ | 7,9,11,13,14 | 0.92, 1.04, 1.13, 1.01, 0.96 |
| n~2¹⁹ | 9,11,14,17,18 | 1.00, 1.00, 0.99, 0.95, 1.04 |
| n~2²⁰ | 10,12,15,18,19 | 1.00, 0.99, 0.93, 0.92, 1.06 |

**R1D ≈ 1 everywhere** (0.92–1.13). A public labeling cannot localize a uniform `d`: reordering the
search by the carry prior does not change the expected steps-to-find. The v1 "21×" is gone — it was the
per-run-setup artifact, not the partition.

## FIX (b) — the actual 2-D GLV composition is WORSE than the interval: 2D/1D ≥ ~1
2-D meet-in-the-middle over the `(a,b)` box vs the 1-D interval baseline, same metric. `2Dor` = the
carry-ORACLE (given `ε(d)`, filter the accept to the matching sign-region):

| curve | k | P_k | boxWa×Wb | 2D/1D | 2Dor/1D |
|---|---|---|---|---|---|
| n~2¹⁹ | 9 | 0.004 | 512×2 | 15.8 | 15.8 |
| | 11 | 0.007 | 513×3 | 4.9 | 4.9 |
| | 14 | 0.048 | 527×17 | 2.2 | 2.2 |
| | 17 | 0.376 | 638×129 | 0.98 | 0.98 |
| | 18 | 0.747 | 768×513 | 1.5 | 1.5 |
| n~2²⁰ | 10 | 0.28 | 512×1 | 7.4 | 7.4 |
| | 12 | 0.48 | 964×1088 | 20.6 | 20.8 |
| | 15 | 0.46 | 1481×1088 | 8.0 | 8.0 |
| | 18 | 0.50 | 1488×1147 | 2.8 | 3.0 |
| | 19 | 0.50 | 1487×1167 | 2.4 | 2.4 |

- **2D/1D ≥ ~1, up to ~20×.** The 2-D GLV search costs ~`√n` (the box is ~`n` regardless of the interval,
  because the GLV halves span ~`√n` for any genuinely-2-D key), while the 1-D interval costs ~`√(2^k)`.
  For `k < log₂n`, the interval bound beats the GLV structure — exactly the λ-fold finding, now measured
  **with the carry included**. The gap shrinks to ~1 only as `k→log₂n` (full range); the single 0.98 at
  n~2¹⁹,k=17 is boundary "equal," not a speedup.
- **The carry oracle gives no benefit: 2Dor ≈ 2Dfull** at every row. A one-bit sign-region constraint
  cannot cheaply skip meet-in-the-middle giant rows; it filters the accept, saving at most a constant
  factor via a smaller effective box — never the exponent.

## Verdict
The T2c carry structure provides **no computational advantage on the interval DLP**, at model scale, on
either axis: the 1-D partition is useless (R1D≈1), and the 2-D GLV composition is strictly worse than the
plain interval (2D/1D≥~1, up to 20×), with the carry oracle adding nothing. This is a **fair, measured**
scoped null — the deck was un-stacked and the actual composition object was built and tested.

**Theorem-consistent (the reason it cannot be otherwise).** (i) `ε_LBE` is one bit ⇒ any ε-conditioning
is a constant factor, never exponent movement. (ii) For interval keys the GLV halves do not shrink with
the interval, so the 2-D box (~`n`) exceeds the interval (`2^k`) whenever `k<log₂n` — the interval bound
dominates the endomorphism structure (λ-fold, now joint with the carry). The measurements realize both.

## Scope / what is NOT claimed
- Model scale only; zero secp power. secp's live k (≥135) is unsolvable, so the *measurement* cannot run
  there — but the two mechanisms above (one-bit ceiling; box≫interval) are scale-free and secp's own P_k
  is decayed to ≈½ (more fragmentation), so nothing at secp scale reverses this.
- Untested refinements (unprojected clause): larger `n` bands; a non-meet-in-the-middle 2-D solver that
  exploits the half-plane geometry (still ≤ constant factor by the one-bit ceiling); other CM discriminants.
- This closes the T2c √6-composition residual as a measured no-lever. It does NOT close the broader
  computational (C-class) frontier — a subexponential prime-field ECDLP would be a real break and is
  untouched here.

## Provenance
Exact int/GF(q) signal path (curve arithmetic, GLV lattice, ε, partition, op-counts). Float only in
displayed ratios of exact integer counts (`# noqa: float`). Ported GLV/eps validated against
`t2c_range_glv_structure_v1` on 300 secp d. Runner + logs archived. v1 runner superseded per D3.
