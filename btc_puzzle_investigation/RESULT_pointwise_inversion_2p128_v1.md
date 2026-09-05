# RESULT — pointwise inversion at $2^{128}$ (ITEM 5, secp scale)

**Date:** 2026-08-08.
**Script:** `pointwise_inversion_2p128_item5_v1.py` (gmpy2 Jacobian arithmetic + batch inversion).
**Object:** $S = \sum_{i=1}^{M} \chi_2(x_{[d_i]G}) \cdot \chi_2(x_{[d_i^{-1}]G})$, the pointwise
non-algebraic ($d \mapsto d^{-1}$) autocorrelation of the $\chi_2(x)$ sign sequence, at secp scale.
**Scale:** $d_i \in [2^{k-1}, 2^k)$ for $k \in \{128, 135, 160\}$ + full-range control.
$M = 20000$ samples, $R = 2000$ permutation null draws.
**Seed (discovery):** `20260801`. **OOS seeds:** `20260810`–`20260814`.

---

## 0. What this tests

This is the §5.3 prediction from `STRUCTURAL_IMPLICATIONS_2026-07-30_v1.md`: the non-algebraic index
map $d \mapsto d^{-1}$ is the one channel the Weil closure does NOT cover. The pointwise version
samples $M$ discrete logs from a dyadic band, pairs each $d$ with its inverse $d^{-1} \bmod n$
(which lands at a pseudo-random location), and tests whether the sign correlation
$\chi_2(x_{[d]G}) \cdot \chi_2(x_{[d^{-1}]G})$ is stronger than random.

This is the secp-scale complement to the small-$p$ Probe B of
`RESULT_mu3_subspace_residual_v1.md` (which tested $d^{-1}$ on the reduced $Q_6$ at $|Q_6| \leq 2191$).

---

## 1. Discovery run (seed 20260801)

| arm | $M$ | C-FIX | C-DUP | $S$ | null $\mu$ | null $\sigma$ | theory $\sqrt{M}$ | ratio | perm $p$ |
|---|---|---|---|---|---|---|---|---|---|
| $k=128$ | 20000 | 0 | 0 | $-154$ | $-9.3$ | 141.6 | 141.4 | 1.001 | 548/2001 |
| $k=135$ | 20000 | 0 | 0 | $+52$ | $+0.8$ | 144.9 | 141.4 | 1.025 | 1457/2001 |
| $k=160$ | 20000 | 0 | 0 | $+416$ | $+0.5$ | 141.1 | 141.4 | 0.998 | **6/2001** |
| full-range | 20000 | 0 | 0 | $-46$ | $-3.3$ | 137.9 | 141.4 | 0.975 | 1515/2001 |

**Controls all valid:** C-NULLSD ratios in $[0.975, 1.025]$ (null scale matches theory);
C-BALANCE marginals near-balanced ($\pm 1\%$); C-FIX 0 exclusions (no $d^2 \equiv \pm 1$ in sampled
range); C-DUP 0 ($\mu_6$-class collisions); C-PLANT power floor between 2% and 5% (5% planted fires
at $|S|=862$; 2% does not at $|S|=250$).

The $k=160$ cell fired: $p = 6/2001 = 0.003$, $z \approx 2.95\sigma$. With 4 arms, Bonferroni-adjusted
$p \approx 0.012$. The C-PLANT floor places the observed $|S|=416$ at roughly a $\sim 3\%$ coherent
signal **if real**. The native-scale arms ($k=128$, $k=135$) and full-range control are null.

---

## 2. OOS replication (5 fresh seeds at $k=160$, 2 at $k=128$)

Per the project discipline (`CLAUDE.md`), a single-seed sub-$0.01$ lead is not promotable without
OOS replication. Ran 5 fresh seeds at $k=160$ (the firing arm) and 2 at $k=128$ (the null baseline):

| arm | seed | $S$ | null $\sigma$ | perm $p$ | fires? |
|---|---|---|---|---|---|
| $k=160$ | 20260810 | $-146$ | 139.6 | 580/2001 = 0.29 | no |
| $k=160$ | 20260811 | $+132$ | 138.8 | 699/2001 = 0.35 | no |
| $k=160$ | 20260812 | $+238$ | 139.2 | 170/2001 = 0.085 | no |
| $k=160$ | 20260813 | $-144$ | 143.8 | 655/2001 = 0.33 | no |
| $k=160$ | 20260814 | $-78$ | 143.2 | 1183/2001 = 0.59 | no |
| $k=128$ | 20260810 | $+46$ | 140.4 | 1534/2001 = 0.77 | no |
| $k=128$ | 20260811 | $-14$ | 141.2 | 1865/2001 = 0.93 | no |

**The $k=160$ firing does not replicate.** All 5 OOS seeds are within $1.7\sigma$ of the null mean;
pooled OOS $S$ mean $\approx 0.4$, consistent with zero. The original $S = 416$ was a false positive.

This matches the established pattern: `pow7` (`RESULT_cside_replication_v1.md`, $Z_{\text{pool}}^{F30} = -0.923$)
and `inv` (`RESULT_cside_pooled_tilt_settlement_v1.md`, calibrated $p = 0.265$) — single-seed
sub-detection leads that fail OOS replication.

---

## 3. Grade

**`[SCOPED NULL — OOS-retested, secp scale]`** on the pointwise $d^{-1}$ inversion autocorrelation
$S = \sum_i \chi_2(x_{[d_i]G}) \cdot \chi_2(x_{[d_i^{-1}]G})$.

- **Object:** pointwise $d^{-1}$ sign correlation of $\chi_2(x)$.
- **Class:** permutation null ($b$ permuted against $a$), $M = 20000$, $R = 2000$.
- **Power:** C-PLANT floor 2–5% coherent signal; null scale validated (C-NULLSD ratios in $[0.975, 1.025]$).
- **Scope:** 4 arms ($k=128, 135, 160$, full-range) $\times$ 1 discovery seed + 7 OOS seeds.
  dyadic-$d$ sampling at secp scale.

**The $k=160$ lead is closed as a false positive** (5/5 OOS seeds fail). Not promoted.

---

## 4. What this means

1. **The §5.3 non-algebraic channel ($d^{-1}$) shows no detectable pointwise signal at secp scale**,
   at the $\sim 3$–$5\%$ coherent-signal power floor. Combined with the Probe B scoped null on the
   reduced $Q_6$ (`RESULT_mu3_subspace_residual_v1.md`) and the orbit-level scoped null
   (`RESULT_cside_nonalgebraic_correlation_v1.md`), the $d^{-1}$ channel is now nulled at three
   scales: $|Q_6| \leq 2191$ (reduced), $p \sim 10^4$ (orbit-level), and secp $2^{128}$
   (pointwise, dyadic-$d$ sampling).

2. **The power floor is the honest limit.** The C-PLANT curve shows the instrument detects
   $\geq 5\%$ coherent signals reliably and $\geq 2\%$ marginally. A sub-$2\%$ signal would be
   invisible. The scoped null excludes coherent $d^{-1}$ correlation above $\sim 3\%$ at $M = 20000$.

3. **What remains genuinely untested:** the *interval-restricted* $R_{\text{inv}}(I) =
   \sum_{d \in I} c(d) \cdot c(d^{-1})$ over a *contiguous* dyadic-$d$ interval (the pointwise
   version samples $M$ random $d$; the interval version restricts to a block, which is structurally
   different and connects to the aperture wall). No code exists for this. Also untested: the
   additive-twist incomplete sum $V(a,I) = \sum_{d \in I} c(d)\,e_n(ad)$ over dyadic intervals.

---

## 5. Reproducibility

- Discovery: `python3 pointwise_inversion_2p128_item5_v1.py 20000 2000` (seed 20260801, 67s).
- OOS: 5 seeds (20260810–20260814) at $k=160$, 2 at $k=128$, inline script (119s).
- $M = 20000$, $R = 2000$, secp256k1 parameters.
- All controls (C-BALANCE, C-DUP, C-FIX, C-NULLSD, C-PLANT) valid at every seed.
