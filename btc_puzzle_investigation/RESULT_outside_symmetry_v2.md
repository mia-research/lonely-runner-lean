# "Outside the symmetry" v2 — CORRECTS v1's mislabel of the flatness

Date: 2026-07-18. Supersedes `RESULT_outside_symmetry_v1.md`. Script `scratchpad/e_outside.py`
+ diagnostic `scratchpad/diag_flatter.py`. **v1 error being corrected:** v1 reported eps and the
symmetrized norm N̄ as "within null (flat/geometric)". They are NOT within the null — they are
SIGNIFICANTLY flatter than random. v1's peak statistic R was only mildly off, but the N_eff (spectral
spread) channel — pre-registered as the subspace guard — is +12σ (eps) to +32σ (N̄). The "flat" label
under-read that channel. Caught on review.

## The corrected finding (p=100003, L=16667, exhaustive x, folded to F_p*/μ6)
Null = uniform random permutation of the feature's own L quotient-values (same multiset, arrangement
scrambled). Statistics: R = top descended char's power share (peak); N_eff = S²/ΣP[m]² (effective #
of participating harmonics; high = flatter).

| feature | R_obs | null R (mean, sd, min) | z_R | N_eff_obs | null N_eff (mean, sd) | z_N |
|---|---|---|---|---|---|---|
| eps | 0.00040 | 0.00058, 8e-5, 0.00041 | −2.2 (below all) | 9465 | 8336, 92 | **+12.3** |
| N̄ | 0.00029 | 0.00058, 8e-5, 0.00043 | −3.7 | 11290 | 8332, 91 | **+32.5** |
| rand(eps) [calib] | 0.00063 | — | +0.8 | 8266 | — | −0.7 |
| rand01 [calib] | 0.00056 | — | −0.2 | 8280 | — | −0.7 |

Both calibration controls land at the null median (z≈0) → the pipeline is sound and the eps/N̄ effect
is a property of their ARRANGEMENT by discrete log, not of their value multiset or the statistic.
Low-frequency (bottom 5%) power share: eps z=−0.1 (broadband, NOT low-freq specific); N̄ z=−8.6
(long-wavelength fluctuations suppressed → hyperuniform-like); rand(eps) z=+0.4 (median).

## Interpretation (characterized, not explained)
- **This is the OPPOSITE of a leak.** A leak = a spectral PEAK (concentration = predictability). eps
  and N̄ are ANTI-concentrated: their autocorrelation decays FASTER than random; they mix more than iid
  under multiplication by g. A more-uniform-than-random function is LESS exploitable, not more.
- **It is a genuine structural fingerprint** of the CM lift (calibrated, +12σ/+32σ), distinct from both
  the forced μ6-dual zeros (Part B) and a peak. eps: broadband flatter. N̄: additionally hyperuniform.
- **Mechanism NOT pinned.** Why the lift geometry decorrelates super-randomly along the multiplicative
  progression g^j is unexplained; not asserted. Named as a characterization (magnitude + broadband/
  low-freq split), per the anomaly-drill rule "kill a named mechanism, never assert an unnamed symmetry."

## What the corrected result does and does not say
- CONFIRMED (both primes, pre-registered): NO descended-character CONCENTRATION / peak in the
  μ6-invariant objects — no leak-shaped structure in the invariant part.
- CORRECTED: there IS a significant flatter-than-random (anti-concentration / hyperuniform) departure,
  which v1 wrongly folded into "null." It is structure, but in the anti-leak direction.
- UNCHANGED scope limit: eps/N̄ are μ6-INVARIANT and provably cannot pin d. This whole test is the
  invariant side; d-leakage, if any, lives in the anti-invariant complement (untested here).
- OPEN: the mechanism of the flatter-than-random effect; and the faithful anti-invariant probe (#2).
