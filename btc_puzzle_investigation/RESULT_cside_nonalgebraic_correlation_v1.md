# RESULT: c-side non-algebraic index correlation (queue item C) — scoped NULL + flagged sub-detection bias

**Date:** 2026-07-31
**Scripts:** `cside_nonalgebraic_correlation_v1.py` (small-p, no power), `cside_orbitlevel_v1.py` (orbit-level, scalable)
**Grade: `[EMPIRICAL — SCOPED, family-wise NULL]`** for the per-prime CDH/inversion structure; **`[FLAGGED LEAD — sub-detection, calibration-controlled]`** for the pooled negative bias. **Not a closure** (per the counter-prior: a clean scoped null is valid, but a surviving pooled tilt is an open thread to chase, not bury).
**Register:** purist. This is the first run of the record's named open queue item "C" (`STRUCTURAL_IMPLICATIONS §5.3, §8`).

---

## 0. What was run, and why it was genuinely open

The direct c-side correlations $T_f=\sum_d c(d)\,c(f(d))$ for **non-algebraic** index maps $f$ (inverse $d^{-1}$, odd power maps $d^k$) — the CDH/inversion channel, the one wall the Weil closure does not cover. Recon confirmed these were **genuinely un-run**: the record had tested only (a) the *frequency-side* analogue $\mathrm{corr}(u(a),u(\sigma(a)))$ (NULL) and (b) the c-side *spinning-phase hologram* $H(k,a)$ (NULL) — both different statistics (`RESULT_large_p_and_arrangement_v1.md`, `RESULT_phase_family_and_tail_v1.md`).

## 1. The reduction that makes it scalable

$c(d)=\chi_2(y_{[d]G})$ is **exactly constant on each $\mu_3$ orbit** (verified: 0 deviations across all orbits at p=43,127,547) — the GLV invariance $c(\lambda d)=c(d)$, forced. Both `inv` and `pow-k` map orbits to orbits (verified at n=127). So $c(d)c(f(d))$ depends only on the **orbit pair** $(\text{orbit}(d), \text{orbit}(f(d)))$, and the effective sample size is the orbit count $(n-1)/3$, not $n$.

This is both the enabler and a finding: **the orbit count, not $n$, sets the power.** Small $p$ (orbits ~10–33) has no power — confirmed by an independent firing control that failed to clear the gate at p≤211. Large $p$ (orbits ~3600–4400) gives real power: the control (a decisive 80%-agreement planted $f$-correlation, independent of $c$) fires at `ge_hi=0/R` at every large prime.

## 2. Result — family-wise NULL on the `inv` map

**18 large primes** (p=10831…15919, 3620–4400 orbits each), `inv` map, orbit-permutation null (R=400), gate firing at every prime:

- `max|z| = 2.39` (p=11503); **0 cells clear Bonferroni** (|z|>2.8 for ~18 tests).
- The one edge cell, **p=11503** (z=−2.39, one-sided p≈0.008 at R=2000), did **not** survive multiple-testing and did not replicate in its neighbors (p=11743 z=+0.56, p=11839 z=−0.25, p=12919 z=−1.09). This is the record's recurring "isolated cell that pops at one prime" pattern; treated as the expected one-in-N edge, not a finding.
- Power maps (pow7/11/13) at p=10831: all inside the null (ge 394–531/600), gate firing.

⇒ **Per-prime CDH/inversion structure: NULL at scale, with a firing control.** A scoped result, bounded at the orbit level at $p\sim10^4$.

## 3. The flagged lead — a small consistent negative bias

Discipline check on the *pooled* statistic (the thing the counter-prior says not to dismiss):

- `inv` z-scores across 18 primes: **mean $-0.622$, 15 of 18 negative, Stouffer pooled $z=-2.64$** (one-sided p≈0.004). Individually every cell is null; collectively they tilt consistently negative.

**Null-calibration control (decisive).** On **pure random** orbit values (known $E[T]=0$ by construction), the same null gives mean $z=+0.341$, pooled $z=+1.02$ — the null does **not** manufacture negative bias. So the real-data pooled tilt is **not a null artifact**; it is a feature of the data. ⚠ Calibration std is $0.793$ (under-dispersed), so the z's are mildly inflated; corrected pooled $z\approx-2.1$. Still suggestive, weaker.

**Honest status: a sub-detection CDH/inversion bias that survives a calibration control, but is below per-prime detection and does not survive family-wise correction.** Not a finding, not nothing — an open thread. Per the counter-prior: a clean scoped null is a valid result (§2), but this surviving tilt is to be **chased, not closed**.

## 4. What would resolve it (next on C, if pursued)

- **More primes + Stouffer with a calibrated (permutation) pooled p-value** rather than z-inflation — ~30–50 large primes would settle whether the pooled tilt is a real small effect ($T_{\text{inv}}\approx-0.02$, far below the ~0.5 detection floor) or the tail of noise.
- **An OOS retest of the most-negative cells** (the record's standard: re-run p=11503/13147/15607 on fresh null seeds; if the pooled tilt is a draw of the statistic it will wash out).
- **The shortscalar arm at the $2^{128}$ scale** (`PREREG_incomplete_shortscalar_v2`) remains the operationally-decisive form of this channel — the orbit-level test here is at $p\sim10^4$, three orders of magnitude below the puzzle's $\sqrt{n}\sim2^{128}$ threshold where complete-sum bounds go vacuous. The bias, if real, could grow in that regime.

## 5. Files

- `cside_orbitlevel_v1.py` — the scalable orbit-level test (this result).
- `cside_nonalgebraic_correlation_v1.py` — the small-p version (no power; kept for the parity-rule record).
- Recon: `arrangement_correlation_v1.py` (freq-side template), `phase_family_scan_v1.py` (c-side hologram, distinct statistic).
