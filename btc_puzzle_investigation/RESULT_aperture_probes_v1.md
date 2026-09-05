# RESULT — aperture-channel probes E (interval inversion) + F (twisted incomplete sum)

**Date:** 2026-08-08.
**PREREG:** `PREREG_aperture_probes_v1.md` (frozen before data).
**Script:** `aperture_probes_v1.py` (passes `check_no_float.py`).
**Seeds:** discovery `20260815`, OOS `20260816`–`20260818`. $R = 1000$ permutation-null draws per cell.
**No deviations from the PREREG.**

---

## 0. What these probes are

The two genuinely-untested objects from the consequences audit
(`CONSEQUENCES_mu3_subspace_null_v1.md`):

**Probe E — interval-restricted inversion autocorrelation.**
$$S_E(I) = \sum_{j=0}^{W-1} \chi_k(w_{[d_0+j]G}) \cdot \chi_k(w_{[(d_0+j)^{-1}]G})$$
where $I = [d_0, d_0+W) \subset [2^{k-1}, 2^k)$ is a **contiguous** dyadic-$d$ interval ($W = 2000$),
$w \in \{x, y\}$ (both characters tested), $d^{-1} = d^{-1} \bmod n$. This is the composition of the
non-algebraic $d^{-1}$ channel with the aperture (contiguous interval). Null: within-interval value
permutation of $b$ against $a$ (marginal-preserving), max over $M_{\text{int}} = 50$ intervals.

**Probe F — additive-twist incomplete sum.**
$$V(a, I) = \sum_{j=0}^{W-1} \chi_2(y_{[d_0+j]G}) \cdot e_n(a(d_0+j))$$
where $e_n(t) = e^{2\pi i t/n}$. $K = 200$ random twist parameters $a \in [1, n-1)$. Statistic:
$\max_{I,a} |V(a,I)|$. Null: iid $\pm 1$ of length $W$, same twist params. This is the incomplete-sum
analogue of the complete sum $V(a)$ (proved bounded by #26), at the aperture scale where no bound holds.

---

## 1. Discovery run (seed 20260815)

| arm | $\max|S_E|$ or $\max|V|$ | rank | percentile | verdict |
|---|---|---|---|---|
| E $k=128$ $\chi_2(x)$ | 110 | 463/1000 | 46% | null |
| E $k=128$ $\chi_2(y)$ | 104 | 334/1000 | 33% | null |
| E $k=160$ $\chi_2(x)$ | 94 | 145/1000 | 14% | null |
| E $k=160$ $\chi_2(y)$ | 108 | 447/1000 | 44% | null |
| F $k=128$ | 137.0 | 419/1000 | 41% | null |

**Controls valid:** C-PLANT fires at 5% on Probe E ($|S| = 194$, rank 1000/1000) and marginally at
2% (rank 998/1000). C-PLANT fires at 5% on Probe F ($|V| = 106$, rank 988/1000), fails at 2%
(rank 913/1000 — below the power floor). Null scale validated: $\text{sd}[\max \text{ over 50}]
\approx 18$, matching the theoretical $\sigma/\sqrt{2\ln 50} \approx 16$ for the max of 50 iid
$N(0, \sqrt{W}^2)$ draws (the diagnostic label comparing to $\sqrt{W} = 44$ was checking the wrong
quantity — single-draw $\sigma$, not max-of-50 $\sigma$; the null is correctly scaled).

---

## 2. OOS replication (3 fresh seeds)

| arm | seed 16 | seed 17 | seed 18 | mean |
|---|---|---|---|---|
| E $k=128$ $\chi_2(x)$ | 32% | 25% | 6% | 21% |
| E $k=128$ $\chi_2(y)$ | 69% | 59% | **97%** $\ast$ | 75% |
| E $k=160$ $\chi_2(x)$ | 60% | 53% | 18% | 44% |
| E $k=160$ $\chi_2(y)$ | 28% | **93%** | 10% | 44% |
| F $k=128$ | 4% | **95%** $\ast$ | 34% | 44% |

Two OOS cells at FIRE ($\geq 95\%$): $k=128\,\chi_2(y)$ seed 18 (97%), $F\,k=128$ seed 17 (95%).
Neither is at HIT ($\geq 99\%$). Both are at **different arms and different seeds** — no replication.

---

## 3. Multiple-testing assessment

**20 total cells** (4 Probe E arms + 1 Probe F arm, × 4 seeds).

| threshold | expected FP | observed | replicated? |
|---|---|---|---|
| 95% (FIRE) | 1.0 | 2 | no (different arms/seeds) |
| 99% (HIT) | 0.2 | 0 | — |

$\Pr(\geq 2 \text{ FIRE} \mid \lambda = 1.0) = 0.264$ — well within chance. The rank distribution
passes KS uniformity ($D = 0.200$, crit$_{0.05} = 0.304$ for $n = 20$).

---

## 4. Grade

**`[SCOPED NULL — OOS-retested, secp, aperture scale]`** on both:
- **Probe E:** interval-restricted inversion autocorrelation $S_E(I)$, both characters, $k \in \{128,160\}$.
- **Probe F:** additive-twist incomplete sum $V(a,I)$, $k = 128$.

**The two FIRE cells are not replicated** (different arms, different seeds), and the total count
matches the expected false-positive rate. They are consistent with the null tail.

**Power floor:**
- Probe E: C-PLANT detects $\geq 5\%$ coherent inversion signal reliably, $\geq 2\%$ marginally.
- Probe F: C-PLANT detects $\geq 5\%$ single-frequency signal; below 5% the power floor is weak
  (2% fails at rank 913/1000). The $K = 200$ twist parameters dilute the per-frequency power.

---

## 5. What this means

1. **The interval-restricted $d^{-1}$ channel is nulled at secp scale.** This was the
   structurally-predicted composition of the non-algebraic channel with the aperture
   (`STRUCTURAL_IMPLICATIONS` §5.3-5.4). At $W = 2000$, $M_{\text{int}} = 50$, with firing controls
   passing, no concentration was found in either $\chi_2(x)$ or $\chi_2(y)$. Combined with the
   pointwise $d^{-1}$ null (`RESULT_pointwise_inversion_2p128_v1.md`), the $d^{-1}$ channel is now
   nulled at four scales: reduced $Q_6$, orbit-level, secp pointwise, and secp interval-restricted.

2. **The additive-twist incomplete sum $V(a,I)$ shows no concentration at the aperture scale.**
   This was the genuinely-new object connecting the aperture to the $V(a)$ eigenvalue machinery.
   The null says: at $W = 2000$, $K = 200$ twist params, the twisted incomplete sum is
   indistinguishable from random $\pm 1$ against the same twist.

3. **The power floor is the honest limit.** Probe E excludes coherent inversion correlation
   $\geq 5\%$ reliably; Probe F excludes single-frequency concentration $\geq 5\%$ at reduced power
   (the $K = 200$ twist scan trades depth for breadth). A sub-5% signal is below detection at these
   parameters.

4. **The genuine remaining gap** is now narrower: the GLV/lattice aperture arm (gate-blocked,
   harness unbuilt), and the possibility of structure at $W$ closer to the Pólya-Vinogradov wall
   ($W \sim 2^{135}$ at secp — unreachable). At $W = 2000$ the incomplete sum is still well below
   the wall ($\sqrt{p} \log p \approx 2^{135}$ at secp), but it is the largest contiguous-$d$
   aperture test that has been run on the $\chi_2(y)$ and $d^{-1}$ channels.

---

## 6. Reproducibility

- Discovery: `python3 aperture_probes_v1.py` (seed 20260815, 214s).
- OOS: 3 seeds (20260816–20260818), inline script (634s).
- $W = 2000$, $M_{\text{int}} = 50$, $K = 200$, $R = 1000$.
- secp256k1 parameters (gmpy2 Jacobian arithmetic).
- C-PLANT fires at 5% on both probes; C-NULLSD validated (max-of-50 scaling).
