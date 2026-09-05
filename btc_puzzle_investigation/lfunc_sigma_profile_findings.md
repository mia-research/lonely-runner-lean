# L-functions triangle — Q3 resolved: value-variance tracks n_L, NOT degree (2026-07-10)
Outstanding item from `secp256k1_Lfunction_intersections.md` §"What I need to turn
Q3/Q4 into computations". Script: `lfunc_sigma_profile.py`. Coefficients exact (int);
value-distribution measured in float (NOT the key signal path — allowed here).

## The question (Q3)
The doc predicted: the σ² coefficient of the spectral wall E(σ) "tracks the L-degree
through κ_∞", so the degree-2 Hecke L of ℚ(√−3) should show **2×** the ζ coefficient.
Test: build the prime Dirichlet sum S(s)=Σ_p ã_p p^{−s} and measure Var_t(Re S(σ+it)).

## Result — measured on four L-functions of known degree (X=40000, 4200 primes)
Selberg orthonormality constant n_L = mean_{p≤X} |ã_p|²  (analytic-normalized ã_p):
| L-function                              | degree | n_L (measured) |
|-----------------------------------------|:------:|:--------------:|
| ζ                                       |   1    | 1.00           |
| L(s,χ₋₃)                                |   1    | 1.00           |
| ζ_K = ζ·L(χ₋₃)  (Dedekind, REDUCIBLE)   |   2    | 1.99           |
| **L(s,ψ)=L(E), secp256k1 (PRIMITIVE)**  |   2    | **0.99**       |

Vertical variance Var_t(Re S(σ+it)) (analytic (½)Σ|ã_p|²p^{−2σ}, Monte-Carlo confirmed
at σ=0.75): ratio-to-ζ climbs toward 2 for ζ_K as σ→½, and **stays at ≈1 for L(E,ψ)**.

## Verdict
The log|S(σ+it)| σ-variance tracks the **Selberg constant n_L (# primitive factors)**,
**not** the degree / κ_∞ (# Γ-factors). This is Selberg's CLT: log|L(½+it)| is
asymptotically Gaussian with variance ½ log log T for ANY primitive Selberg-class L,
**independent of degree**. Degree enters the Γ-factors, but the value-distribution
variance sees n_L.

- The doc's "degree-2 ⇒ 2× ζ" holds ONLY for the reducible ζ_K = ζ·L(χ₋₃).
- The **primitive** degree-2 CM Hecke L(s,ψ) (the curve's own L) has variance = ζ's (1×).
- So instantiating the wall on secp256k1's L(s,ψ) does NOT double the σ²-coefficient;
  the doubling in the doc came from using the reducible Dedekind ζ_K by accident.

## Sharp statement for the II–III edge of the triangle
secp256k1's L is a **primitive** degree-2 CM Hecke L. By Selberg's CLT its log-modulus
vertical variance equals ζ's (n_L=1). The CM/degree structure lives in κ_∞ (Γ-factors)
and the χ₋₃-rigid a_ℓ, **not** in the leading σ²-variance. The correct L-invariant to
put in the framework's σ²-coefficient for a primitive L is **n_L, not the degree**.
