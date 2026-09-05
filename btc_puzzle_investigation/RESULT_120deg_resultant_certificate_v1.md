# RESULT: the 120° certificate, A2 — direct $\mathbb{Q}(\zeta_M)$ gcd cross-check

**Date:** 2026-08-01
**Script:** `verify_120deg_resultant_certificate_v1.sage` (Sage; reuses `audit_n1_vsign_v2_core`).
**Grade:** `[VERIFIED — independent direct-gcd route to the g ≥ 2 half, all 22 primes / both branches]`.
**Register:** purist. Item A2 of the 2026-08-01 plan; the CORRECTION's literal $\mathbb{Z}[\zeta_M]$ route, as an independent cross-check of A1's conjunction.

---

## 0. What this is

A1's conjunction (`RESULT_120deg_conjoined_certificate_v1.md`) reaches the $g \geq 2$ half via PART 1's symbolic factorization in $\mathbb{Z}[e_1,p,\omega]/(\omega^2+\omega+1)$ — a universal polynomial identity exhibiting the common quadratic factor $D(T)$. This script (A2) computes the $g \geq 2$ half by a **completely different route**: build $L^*(T)$ in $\mathbb{Q}(\zeta_M)[T]$ with $M=\operatorname{lcm}(n,3)=3n$, $\zeta_n$ and $\zeta_3$ **jointly pinned** as powers of a single generator ($\zeta_n=\zeta_M^3$, $\zeta_3=\zeta_M^n$), and compute $\gcd(L^*(T), L^*(\zeta_3 T))$ directly. Agreement between A1 and A2 validates the conjunction from two independent algebraic code paths.

This is the route the CORRECTION specified (after retracting its first, zero-ring revision). Sage's native cyclotomic-field arithmetic handles the $\Phi_M$ reductions, so no hand-rolled `reduce_cyclotomic` is needed.

## 1. The construction

For each prime $p$ ($n=\#E(\mathbb{F}_p)$ prime, $n\equiv1\bmod3$ so $M=3n$):
- $K_M=\mathbb{Q}(\zeta_M)$, $\zeta_M$ its generator; $\zeta_n=\zeta_M^3$, $\zeta_3=\zeta_M^n$ (joint pinning — the load-bearing constraint when $\gcd(n,3)>1$; here $\gcd=1$ but the pinning is still the correct construction).
- Sanity: $\zeta_n^n=1$, $\zeta_3^3=1$, $\zeta_3\neq1$.
- $V_k(a)=\sum_d h_k(d)\,\zeta_n^{ad}\in K_M$; $e_1=-V_1$, $e_2=(V_1^2+V_2)/2$, $e_3=\varepsilon p\,e_1$ ($\varepsilon=\chi_2(-1)$), $e_4=p^2$.
- $L^*(T)=T^4-e_1T^3+e_2T^2-e_3T+e_4\in K_M[T]$; $L^*(\zeta_3 T)$ by the substitution $T\mapsto\zeta_3 T$.
- $g=\gcd(L^*(T),L^*(\zeta_3 T))$ directly in $K_M[T]$; report $\deg g$.

Exact cyclotomic-field arithmetic only; no finite-field embedding or inflation in the signal path.

## 2. Result — $\deg\gcd = 2$ everywhere, both branches

| stratum | primes | $\varepsilon$ | $M$ range | $\deg\gcd$ at sampled $a$ | $g\ge2$ |
|---|---|---|---|---|---|
| IN-SAMPLE | 7 | $-1$ | 93–1641 | $[2,2,2]$ each | 7/7 |
| **STRATUM S** | **10** | **$-1$** | **2487–7671** | **$[2,2,2]$ each** | **10/10** |
| STRATUM C (+1) | 5 | $+1$ | 1839–4989 | $[2,2,2]$ each | 5/5 |

**All 22 primes, both branches: $\deg\gcd(L^*(T),L^*(\zeta_3 T))=2$** at every sampled $a$ (3 $\mu_6$-coset reps per prime as a sanity check; the lower bound is $a$-independent by PART 1). This independently confirms the $g\ge2$ half of the A1 conjunction, by direct cyclotomic-field gcd rather than symbolic factorization.

PARI stack set to 8 GB for the large-$M$ primes ($M$ up to 7671, $\varphi(M)\approx5000$); the default 8 MB overflowed at $M\approx5259$.

## 3. What this opens / closes

- **Closes (cross-check):** the $g\ge2$ half is confirmed by two independent routes — (i) A1/PART 1 symbolic factorization in $\mathbb{Z}[e_1,p,\omega]$, (ii) A2 direct $\gcd$ in $\mathbb{Q}(\zeta_M)$. They agree at all 22 primes. The grade promotion of A1 is independently validated.
- **Does not replace A1.** A2 supplies only the lower bound ($g\ge2$); the upper bound ($g\le2$, the census $\min_\ell g_\ell$) is unchanged. The conjunction A1 is what yields $g=2$.
- **Scope unchanged.** This certifies $g\ge2$ at sampled cells of 22 primes. It does not prove uniformity over all $a$, all $p\equiv7\bmod12$ (frontier #26 — a proof, not a measurement). The sampling (3 $a$'s per prime) is a sanity check, not the certificate — PART 1's universality is what makes $g\ge2$ uniform over $a$.

## 4. Files

- `verify_120deg_resultant_certificate_v1.sage` — the direct-gcd driver. `quick` arg runs IN_P only.
- `RESULT_120deg_resultant_certificate_v1.json` — per-prime $\deg\gcd$ records.
