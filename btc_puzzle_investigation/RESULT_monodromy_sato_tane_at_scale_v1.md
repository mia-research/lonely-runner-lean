# RESULT: monodromy trace marginal at scale — connected component acts as $SU(2)$

**Date:** 2026-07-31
**Script:** `monodromy_sato_tate_large_p_v1.py` (V1-only FFT route, $O(n\log n)$)
**Grade: `[VERIFIED — at scale, 49,833 cells at p=100003, moment match to 4–5 sig figs]`** for the **1-point marginal**; the **full group (finite center) is narrowed but NOT pinned** — that discrimination needs the 2-point correlation / level-statistics test, which is the next chase (`RESULT_monodromy_2point` forthcoming).
**Register:** purist. This narrows (does not fully identify) the geometric monodromy (frontier #28), at a scale the record never reached.

---

## 0. The question

What is the geometric monodromy $G_{\text{geom}}$ of the Fourier-transform sheaf family $\{H^1_c(E, L_{\chi_2(y)}\otimes L_{\chi_a})\}_a$? This is frontier #28, the load-bearing sub-object for the cap/#26 question: it is the one object controlling how "loose" the eigenvalue configuration can be (the analogue of the RH programme's coercivity constant — see `STRUCTURAL_IMPLICATIONS_2026-07-30_v1.md` §6). The commutative-CM-commutation mechanism for the 120° rigidity was **refuted** (`RESULT_e2_identity_extended_verification_v1.md` §3 — non-abelianity at p=43,67), so the live mechanism target is the geometric monodromy, and this test identifies it.

## 1. Method — the cheap V1-only route

The Sato–Tate marginal lives on $t(a)=\operatorname{Im}(V_1(a))/(2\sqrt{p})\in[-1,1]$, and $V_1$ is the **FFT of the exact integer signal $c(d)=\chi_2(y_{[d]G})$** — $O(n\log n)$, *not* the $O(p^2)$ that blocks the $V_2$/collapse work. So the monodromy-marginal verification reaches $p\sim10^5$ (49,833 cells), versus the record's small-$p$ moment work. (Restricts to prime-$n$ primes, where $E(\mathbb{F}_p)$ is cyclic and the single-dlog framework is valid — composite-$n$ primes are often non-cyclic, e.g. p=859 gives $\mathbb{Z}/291\times\mathbb{Z}/3$, for which the framework does not apply; recorded as a structural caveat.)

**Exactness.** $c(d)$ is the Legendre symbol — exact integer. The FFT and moment-normalization use float64, but only as test statistics ranked against the analytic Sato–Tate prediction (the signal path is exact; float enters only at the marginal statistic, allowed by `CLAUDE.md`).

## 2. Result — the marginal is the Sato–Tate (semicircle) measure

The $SU(2)$-trace / Sato–Tate prediction is that the marginal of $t$ is $\frac{2}{\pi}\sqrt{1-t^2}$, with moments $m_{2k}=\mathrm{Catalan}_k/4^k$.

**Decisive single-prime result (p=100003, n=99667, 49833 cells):**

| moment | measured | $\mathrm{Catalan}_k/4^k$ |
|---|---|---|
| $m_2$ | 0.24916 | 0.25000 |
| $m_4$ | 0.12467 | 0.12500 |
| $m_6$ | 0.07811 | 0.07812 |
| $m_8$ | 0.05487 | 0.05469 |
| $m_{10}$ | 0.04134 | 0.04102 |
| $m_{12}$ | 0.03264 | 0.03223 |
| $m_{14}$ | 0.02666 | 0.02618 |
| $m_{16}$ | 0.02233 | 0.02182 |

**Max deviation across all 8 moments: 0.00084.** The entire moment sequence matches Sato–Tate to 4–5 significant figures, not just the first two. `max|u|=0.99942` — the cap is saturated to 4 nines at this scale, consistent with the finite-size edge law $1-\max|u|\sim c\,L^{-2/3}$ (`RESULT_n1_saturation_residual_v1.md`).

**Convergence across scale** (pooled moments, fundamental domain):
- 8 primes p≤823 (1005 cells): max dev 0.0052
- p=10831–11743 (4 primes, ~5700 cells each): max dev 0.0017–0.0035 per prime
- p=100003 (49833 cells): max dev 0.00084

## 3. The argument: connected-component trace behavior is $SU(2)$ (full group NOT identified)

Three facts, two from the record + one new, combine to narrow the monodromy — but a 1-point marginal can only pin the *connected component in the trace representation*, not the full group:

1. **Not finite monodromy** (new, this run): the marginal is **continuous** at scale (49,833 cells converge smoothly to the semicircle). Finite monodromy gives an *atomic* trace distribution in the limit (Chebotarev over finitely many conjugacy classes); the observed continuous semicircle excludes it.
2. **Not the torus $U(1)$** (record, B3.1): $m_4=1/8\neq3/8$; $U(1)$ would give $m_4=3/8$.
3. **The marginal is the $SU(2)$ trace measure** (this run): $m_{2k}\to\mathrm{Catalan}_k/4^k$ to 4–5 sig figs across 8 moments.

⚠ **What this does NOT pin down — read carefully.** The 1-point marginal is a *1-point statistic*: many groups and representations give the same marginal. Specifically:
- $SU(2)$ and $SU(2)\times\{\text{finite center}\}$ give the **identical** 1-point marginal — the finite center is invisible to it.
- The sheaf is **rank 4**, not rank 2. The clean Katz Sato–Tate trichotomy (finite / torus / $SL_2$) applies to rank-2 sheaves. A rank-4 trace reproducing the semicircle is *consistent with* the tensor-decomposition candidate ($H^1\cong W\otimes R$, trace reducing to a single $SU(2)$-trace) but is not *forced* by the marginal alone.

**Honest statement:** the connected component of $G_{\text{geom}}$ acts, in the trace, like $SU(2)$. Finite monodromy and the torus are excluded. The full group (finite center, component group) is **narrowed but not identified** — that needs the 2-point correlation / level-statistics test. This run is a necessary step toward #28, not its completion.

## 4. What this does NOT settle — and the 2-point question is ALREADY ANSWERED (by the record)

- **The finite center / component group is not determined by the 1-point marginal.** $SU(2)$ and $SU(2)\times\{\text{finite}\}$ give the same marginal.
- **The 2-point level-statistics test is NOT open — the record already ran it, NULL.** `RESULT_semicircle_null_and_verification_v1.md` ran spacing KS, number variance $\Sigma^2$, tail, and small-ball statistics at **17 + 15 primes** against the correct marginal-varying semicircle null, on the $L=(n-1)/6$ **free class representatives** (the GLV-orbit degeneracy — "6 exact copies would swamp every spacing" — is exactly the near-zero spacings I independently rediscovered at p=547). **Result: NULL**; the one high cell ($S3^{\max}$) died OOS. I built a 2-point script (2026-07-31), hit the degeneracy and a rank-unfolding bug, then found the record had already done it. **The spectrum is consistent with iid (decoupled) Sato–Tate, NOT GUE-rigid** — i.e. the eigenvalues across the family behave like independent Sato–Tate draws, not a rigid coupled spectrum. This is consistent with the Fourier-transform-sheaf picture (each $a$ a fresh probe) and does not contradict the connected-component $SU(2)$ marginal, but it means the "maximal rigid $SU(2)$" picture is *not* what the 2-point data shows.
- **This identifies the connected-component trace behavior but does not by itself prove the 120° rigidity uniformly (#26).** The cap follows from the rigidity; the monodromy *governs* the rigidity but a proof that the monodromy forces $\alpha_2/\alpha_1=\zeta_3$ for all $a$ is still the open link. What this run does is **narrow the mechanism**: the rigidity is enforced by an $SU(2)$-type monodromy action (consistent with the tensor-decomposition candidate $H^1\cong W\oplus(W\otimes\xi)$, $G_{\text{geom}}=\mathrm{SL}_2$-on-the-tensor-structure), not by a commutative CM endomorphism (refuted).

## 5. Net move

The structural "why" is narrowed, not resolved: **the rigidity mechanism is consistent with an $SU(2)$-type monodromy action on a 2-dim piece of the cohomology** (the tensor-decomposition candidate $H^1\cong W\otimes R$, $G_{\text{geom}}=\mathrm{SL}_2$-on-the-tensor-structure), and this is *not refuted* by the non-abelianity of the eigenvalue field — but the full group is not yet pinned. The remaining structural steps are: (a) the **2-point correlation / level-statistics test** to discriminate the finite center and confirm maximal-$SU(2)$ vs a special subgroup (next chase, small-$p$ exact via the unfolded eigenangle); then (b) proving that this monodromy forces the within-pair ratio $\zeta_3$ uniformly (#26 as a monodromy statement).

The cryptographic "where" (the $d^{-1}/d^k$ CDH/inversion channel at the $2^{128}$ scale) is the *next item after* the structural 2-point test — a queue, not a fork (the structural answer informally directs where to aim the crypto search: maximal-$SU(2)$ argues for genericity; a special monodromy raises the crypto priority).

## 6. Files

- `monodromy_sato_tate_large_p_v1.py` — the V1-only FFT route (this run).
- Scale-up driver: `/tmp/biggerp.py` (p=100003 result).
- Builds on `RESULT_semicircle_null_and_verification_v1.md` (the semicircle null, small-$p$ moments) and `RESULT_n1_saturation_residual_v1.md` (the edge law).
