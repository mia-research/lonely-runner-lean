# PREREG — aperture-channel probes E (interval inversion) and F (twisted incomplete sum)

**Date:** 2026-08-08.
**Frozen BEFORE data.** Deviations to `PREREG_aperture_probes_v1_DEVIATIONS.md`.
**Trigger:** the consequences audit (`CONSEQUENCES_mu3_subspace_null_v1.md`) identified two
genuinely-untested objects for which no code exists. These are the two probes that break the silence
on the $2^{128}$ aperture channel.

---

## 0. The two objects

Both live on secp256k1 at the native puzzle scale ($d \in [2^{k-1}, 2^k)$), continuing the pointwise
inversion test (`pointwise_inversion_2p128_item5_v1.py`) and the incomplete-sum test
(`incomplete_sum_2p128_firstorder_v1.py`) into the structurally-predicted residual channels.

### Probe E — interval-restricted inversion autocorrelation

$$R_{\text{inv}}(I) = \sum_{d \in I} \chi_k(w_{[d]G}) \cdot \chi_k(w_{[d^{-1}]G})$$

where $I = [d_0, d_0 + W) \subset [2^{k-1}, 2^k)$ is a **contiguous** dyadic-$d$ interval, $w \in
\{x, y\}$ (both characters tested), and $d^{-1} = d^{-1} \bmod n$.

**Why this is structurally different from the pointwise version.** The pointwise test
(`pointwise_inversion_2p128_item5_v1.py`) samples $M$ random $d$ from the band and pairs each with
$d^{-1}$, which lands at a pseudo-random location. Probe E instead takes a **contiguous block of
$d$-indices** and asks whether the *local* sign sequence in that block correlates with the sign
sequence at the inverted locations. Under the aperture framing (`STRUCTURAL_IMPLICATIONS` §5.3-5.4),
this is the composition of the non-algebraic channel ($d^{-1}$) with the aperture (contiguous
interval), at the scale where the Weil bound is vacuous.

**The honest complication (stated up front).** $d^{-1}$ is not monotone in $d$; a contiguous block
$\{d_0, d_0+1, \ldots, d_0+W-1\}$ maps under inversion to a pseudo-random scatter
$\{d_0^{-1}, (d_0+1)^{-1}, \ldots\}$. So $R_{\text{inv}}(I)$ is not a "local" correlation in the
usual sense — it pairs a contiguous block with a scattered set. This is by construction: it tests
whether the sign at $d$ (local) carries information about the sign at $d^{-1}$ (non-local), which is
exactly the CDH/inversion-flavored residual §5.3 names. The pointwise version loses the locality
entirely; the interval version preserves it on one side of the pair.

### Probe F — additive-twist incomplete sum

$$V(a, I) = \sum_{d \in I} \chi_2(y_{[d]G}) \cdot e_n(a \cdot d)$$

where $e_n(t) = e^{2\pi i t / n}$ is the additive character, $a \in \{1, \ldots, n-1\}$ is the twist
parameter, and $I \subset [2^{k-1}, 2^k)$ is a dyadic-$d$ interval. The statistic is $\max_a
|V(a, I)|$ over a sample of twist parameters $a$.

**Why this is new.** Every incomplete sum on file is untwisted ($a = 0$). The twisted version
connects the aperture question to the $V(a)$ eigenvalue machinery: the complete sum $V(a) =
\sum_{d=1}^{n-1} c(d)\,e_n(ad)$ satisfies $|V(a)| \leq 2\sqrt{p}$ (proved via #26), but the
incomplete sum $V(a, I)$ has no such bound when $|I| < \sqrt{p}\log p$. Probe F asks whether the
twisted incomplete sum concentrates beyond the $\sqrt{|I|}$ random expectation at the aperture scale.

---

## 1. Character convention (both characters)

- **$\chi_2(x)$:** the prior pointwise test used this. $\chi_2(x_P) = \chi_2(X_J)$ where $(X_J, Y_J,
  Z_J)$ are Jacobian coordinates (no inversion needed, since $\chi_2(Z_J^2) = 1$).
- **$\chi_2(y)$:** the $c(d)$ object from the $V(a)$ programme. $\chi_2(y_P) = \chi_2(Y_J) \cdot
  \chi_2(Z_J)$ (no inversion needed, since $\chi_2(Z_J^3) = \chi_2(Z_J)$).
- Probe E tests **both**. Probe F tests **$\chi_2(y)$ only** (it is the $V(a)$ object).

---

## 2. Probe E — design

**Intervals.** $M_{\text{int}} = 50$ random interval starts $d_0 \in [2^{k-1}, 2^k)$, each of width
$W = 2000$. For each, compute:
$$S_E(I) = \sum_{j=0}^{W-1} \chi_k(w_{[d_0+j]G}) \cdot \chi_k(w_{[(d_0+j)^{-1}]G})$$
using gmpy2 Jacobian arithmetic + batch inversion for the inverse points.

**Statistic.** $T_E = \max_I |S_E(I)|$ over the 50 intervals. Also report $\text{Var}(S_E)$ and
$\overline{S_E}$.

**Null.** For each interval, permute the $b = \chi_k(w_{[d^{-1}]})$ values against the $a =
\chi_k(w_{[d]})$ values within the interval (marginal-preserving). $R = 1000$ permutations per
interval. Rank $|S_E(I)|$ among the null. Also compute a global pooled rank.

**Controls (the firing-control discipline, mandatory):**
- **C-PLANT:** plant a coherent inversion signal at strength $f \in \{10\%, 5\%, 2\%\}$; must FIRE
  at $f \geq 5\%$, must NOT fire at $f = 0$.
- **C-NULLSD:** the null's empirical $\sigma$ must match $\sqrt{W}$ (catches a mis-scaled null —
  the fault that made item 4 of the pointwise programme fire falsely).
- **C-FIX:** exclude $d$ with $d^2 \equiv \pm 1 \pmod{n}$ (forced $+1$ summands, zero information).
- **C-DUP:** no two $d$ in the same $\mu_6$ class.

**Bands.** $k \in \{128, 160\}$.

---

## 3. Probe F — design

**Intervals.** Same structure: $M_{\text{int}} = 50$ intervals $I = [d_0, d_0+W)$, $W = 2000$.

**Twist parameters.** $K = 200$ random $a \in \{1, \ldots, n-1\}$ (avoiding $a$ near $0$ and $a$
dividing $n$).

**Statistic.** For each $(I, a)$:
$$V(a, I) = \sum_{j=0}^{W-1} c(d_0 + j) \cdot e^{2\pi i a (d_0+j) / n}$$
where $c(d) = \chi_2(y_{[d]G})$. The additive character $e_n(ad)$ is computed as
$\cos(2\pi ad/n) + i\sin(2\pi ad/n)$ — float in the monotone statistic only, ranked against null
(the same convention as `twist_orbit_spectrum_run_v1.py` and `n1_phase_cap`).

$T_F = \max_{I,a} |V(a, I)|$.

**Null.** For each interval, generate $R = 1000$ random $\pm 1$ sequences of length $W$, compute the
same twisted sum against the same $a$ values. Rank $|V(a, I)|$. (The null is iid $\pm 1$ on the
interval; this is appropriate because $c(d)$ has no forced structure *within* a small interval — the
$\mu_3$ forcing links $d$ to $md$, which jumps across the interval.)

**Controls:**
- **C-PLANT:** plant a single-frequency signal $c(d) = \text{sign}(\cos(2\pi a_0 d/n))$ at a known
  $a_0$ within the sampled set, at strength $f \in \{10\%, 5\%, 2\%\}$; must FIRE at the planted
  $(a_0, I)$.
- **C-NULLSD:** null $|V(a,I)|$ distribution should match $\sqrt{W}$ (random-walk scaling).

**Bands.** $k = 128$.

---

## 4. Interpretation lock

| outcome | verdict | grade |
|---|---|---|
| $T_E$ or $T_F$ ranks $\geq 99\%$ at $\geq 3/5$ OOS seeds, controls valid | **POSITIVE — replicated** | `[VERIFIED — OOS, secp]` |
| ranks $\geq 99\%$ on discovery but not OOS | **FALSE POSITIVE** | closed (same as pointwise $k=160$) |
| ranks $< 95\%$ everywhere, controls FIRE | **NULL — scoped** | `[SCOPED NULL — secp, aperture]` |
| C-PLANT or C-NULLSD fails | **NO VERDICT** | instrument invalid |

**Closure bar (asymmetric):**
- A POSITIVE is a structural anomaly in the aperture channel demanding a mechanism. It is NOT a
  break. It must be OOS-replicated (5 seeds) before promotion.
- A NULL is scoped: names object ($R_{\text{inv}}(I)$ or $V(a,I)$), class (max over intervals/twists),
  power ($W = 2000$, $M_{\text{int}} = 50$, $K = 200$), scale (secp, $k \in \{128,160\}$).

---

## 5. Compute budget

- Probe E: $M_{\text{int}} \times W = 50 \times 2000 = 100000$ points per arm, $\times 2$ (point +
  inverse) $\times 2$ (x and y characters) $= 400000$ Jacobian multiplications per arm. At
  $\sim 72\mu s$/modexp + batch inversion overhead, $\sim 60$s per arm. Two bands: $\sim 120$s.
- Probe F: $M_{\text{int}} \times W \times K = 50 \times 2000 \times 200 = 2 \times 10^7$ — but the
  FFT makes this $O(K \cdot W \log W)$ per interval. Actually: compute $c(d)$ once per interval
  ($W$ points), then FFT against $K$ frequencies. $\sim 50 \times 2000 + 50 \times 200 \log 200
  \approx 10^5 + 10^5 \approx 2 \times 10^5$ ops. Fast ($< 30$s).

**Total: $\sim 150$s per seed.** Five seeds: $\sim 12$ minutes.

---

## 6. Reproducibility

- Seed (discovery): `20260815`. OOS: `20260816`–`20260819`.
- $R = 1000$ permutation null draws per cell.
- $W = 2000$, $M_{\text{int}} = 50$, $K = 200$, $k \in \{128, 160\}$.
- secp256k1 parameters (gmpy2).
- Builds on the Jacobian arithmetic of `pointwise_inversion_2p128_item5_v1.py` and the
  interval-enumeration of `incomplete_sum_2p128_firstorder_v1.py`.
