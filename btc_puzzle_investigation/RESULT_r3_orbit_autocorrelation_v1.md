# RESULT — R3: no lag-d χ₃ correlation in the orbit (mixing confirmed, bound)

**Date:** 2026-08-02. **Executes** frozen `PREREG_r3_orbit_autocorrelation_v1.md`
(SHA `2689f781b862d60664bdb31ee95bf8d77161fb3ddb8ac2494a862d1d285e13e9`, experiment-designer
FRAME-CLEAN). **Script:** `r3_orbit_autocorrelation_v1.py`. **Grade:**
`[EMPIRICAL — bounded; code-shuffle matched null; 5-seed OOS; gate-cleared]`.

## 1. Result
`A(d)=|Σ_s ω^{c(s)−c(s+d)}|²`, `c(s)=χ₃(x([s]G))`, over a length-L=10⁵ orbit, vs the code-shuffle null
(same marginal, no order). 15 lags {1..256}, 5 fresh orbit locations, R_sh=2000.
- **No lag screened the same tail on 5/5 orbits.** 75 cells, one chance tail-touch (d=8 orbit1,
  p=0.999; ~0.75 expected at two-sided 0.01), not replicated. p-values scatter ~uniform.
- **C-PLANT fires at f=0.02** injected lag correlation (A=5.5M ≫ null 99th ≈4.5×10⁵; void at f=0) —
  well-powered instrument.
- **Forced-value: all 15 lags generic** (every median A(d) ≤ 2.4×10⁵ < null 99th ≈4.6×10⁵) —
  empirically confirms the gate's analytical result that no lag has a Weil-forced main term.

## 2. Verdict (Rule 5 — a bound, not a closure)
**Mixing confirmed at these lags/power.** The orbit's χ₃ sequence carries no lag-d correlation above
the shuffle floor. Excludes lag correlations ≳ the f=0.02 injection magnitude; **blind below**.
**Untested (open):** χ₂/χ₆ lag-correlations, lags beyond 256, other L, non-consecutive spacings.

## 3. What it settles
Strengthens `RESULT_interval_vs_random_characterize_v1.md`: the interval char-sum is pseudorandom at
**both** the histogram level (that result) and the **sequential** level (this one). The Stage A anomaly
is fully accounted for as the bootstrap artifact; no residual finer structure survives to this power.

## 4. Bridge to C2
`A(d)` is a group-law-difference correlation (`χ₃(x(P))` vs `χ₃(x(P+[d]G))`), consecutive-along-orbit.
It came back null for **χ₃**. C2 tests the sibling object — **χ₂/χ₆** on the group-law difference of a
**band-random** point set (all-pairs, not fixed-lag) — which R3 does not settle (different characters,
different pairing). C2 proceeds.

## 5. Compute (Rule 2)
5 orbits × 100256 χ₃-modexp = 501,280 modexp; `pow`=76.9µs; 10⁴ integer shuffles; 61s wall. Shuffle
null uses exact-integer numpy (permutation + bincount of 0/1/2 labels) — no float in the signal path.
