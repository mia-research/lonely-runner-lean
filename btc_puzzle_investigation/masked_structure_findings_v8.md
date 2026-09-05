# Masked-Structure — Findings v8: the 3-point group law vs the lift geometry

**Date:** 2026-07-16 · new DLP-adjacent object. Script: `collinear_lift_structure_v1.py`.
Framing (user): ECDLP is a fence, not a proven wall — a null is scoped to the statistic and
scale measured, not a verdict on the avenue.

## The object (never built) and why it's the right fence to look at

Prior probes were single-point (generic) and 2-point (difference set, generic). Untouched =
the **3-point group law** `P₁+P₂+P₃=O` (collinearity) — the structure under
**summation-polynomial / index-calculus** thinking, the actual ECDLP frontier, and the first
place *addition* can imprint on the lift. It uses x **and** y (the slope `(y₂−y₁)/(x₂−x₁)`).

**Sharp test, exact null:** by the Cap Law each curve point is core (`ε=0`) w.p. 3/4
**independently**, so a random triple is all-core w.p. `(3/4)³ = 27/64` and #flaps ~
`Binomial(3,1/4)`. **If collinear triples deviate, the group law sees the geometric label**
— which would couple a hard additive relation to a cheap geometric readout (the shape of an
index-calculus lever). Collinear triples sampled as `(P, Q, −(P+Q))`; matched null = 3
independent random curve points, scored by identical code.

## Result — the group law does NOT see the lift geometry, on two statistics, scaled

**(1) ε core/flap label** (K=40000 triples/prime):

| p | col all-core | null all-core | χ²(col‖null, 3dof) | col #flaps |
|---|---|---|---|---|
| 1009 | 0.3642 | 0.3602 | 2.16 | [.364 .439 .175 .022] |
| 5011 | 0.4012 | 0.3980 | 1.58 | [.401 .428 .154 .018] |
| 20011 | 0.4213 | 0.4174 | 2.81 | [.421 .421 .142 .016] |
| 60013 | 0.4161 | 0.4157 | 1.08 | [.416 .425 .143 .015] |

col all-core → 27/64 = 0.4219 (tracking the null the whole way); #flaps → Binomial
[.4219 .4219 .1406 .0156]; **χ²(3dof) = 1–3, non-significant, flat in p** (not growing).

**(2) the finer 3-point lift SUM** `W = z₁+z₂+z₃` in ℤ[ω] — the actual "additive correction":

| p | KS(\|W\|²/p: col vs null) | col median | null median |
|---|---|---|---|
| 2011 | 0.0068 | 0.354 | 0.348 |
| 10009 | 0.0065 | 0.343 | 0.341 |
| 50023 | 0.0077 | 0.336 | 0.330 |
| 100003 | 0.0047 | 0.337 | 0.341 |

KS = 0.005–0.008, **flat over p=2011→100003 (~50× in p)**; medians equal. The lift sum of a
collinear triple is distributed as that of a random triple.

## Bounded statement + scope

The group-law relation `P₁+P₂+P₃=O` does not couple to (a) the ε core/flap label
(χ²(3dof) ≤ ~3, non-significant, converging to the independent 27/64 prediction), nor to
(b) the 3-point lift-sum norm distribution (KS ≤ 0.008), at **p ≤ 100003**, K=30–40k,
matched null + scaling. **Not tested:** the sextant-triple joint distribution, the *phase* /
arrangement of `W` (only its norm), the actual **summation-polynomial factorization** over
F_p and its reduction mod small primes (a different, deeper object — see below), and secp's p.

This is a scoped fence observation: on these two statistics at these scales, the cheap
geometric readout does not leak the group-law relation. It is not a wall claim.

## Where the fence is still un-probed (DLP-adjacent, un-shut)

1. **Summation-polynomial algebraic structure** — `S₃(x₁,x₂,x₃)` factorization / Newton
   polygon over F_p and mod small primes. This turn tested the *geometric label* of collinear
   triples, not the *polynomial's* structure; the latter is the index-calculus object proper.
2. **The GLV scalar lattice `(a,b)`** — the 2-D short-vector coordinate of `d` itself
   (d ≡ a+bλ), its joint distribution vs the point. The one place the scalar is genuinely
   lower-dimensional.
3. **Amicable cross-domain interference** (F_p pattern vs F_n pattern) — standing E-probe.
4. **Additive-energy / collision counts** of the key difference set — the resonance detector
   for the key SET specifically (finer than flap/S3).
