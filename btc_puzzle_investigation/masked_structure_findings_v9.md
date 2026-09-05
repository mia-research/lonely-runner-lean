# Masked-Structure — Findings v9: summation-polynomial relation yield

**Date:** 2026-07-16 · the closest object to the actual ECDLP attack surface.
Script: `summation_relation_yield_v1.py`. Fence-not-wall: this quantifies a lever's exact
size, and a bounded lever is a fence observation, not a break.

## Object

Index calculus needs **relations**: collinear triples `P₁+P₂+P₃=O` (i.e. `S₃(x₁,x₂,x₃)=0`)
with all three x-coords in a **factor base** F. The relation *yield* (relations per `|F|³/p`)
decides feasibility. CM/GLV question: does a **β-invariant** F (closed under `x↦βx`, β³=1)
beat a random F of the same size — a factor-base compression lever? Known part: `Aut(E)=μ₆`
gives a constant-factor index-calculus speedup on j=0 curves; open part: anything beyond it.

## Result — a real but bounded CM lever; no advantage from a random base

Factor base ~√p, B=120 samples, relations = ordered collinear point-triples with all x in F.

| p | CM yield_rand | non-CM yield_rand | CM yield_β-inv | **ratio β-inv/rand** |
|---|---|---|---|---|
| 1009 | 7.11 | 7.52 | 11.45 | **1.61** |
| 4021 | 7.61 | 7.84 | 11.38 | **1.50** |
| 10009 | 7.84 | 7.84 | 11.60 | **1.48** |

**Two measured facts:**

1. **Random factor base: no CM advantage.** yield_rand is the same for CM and non-CM
   (~7–8) at every prime. CM structure, with a generic F, does not raise relation density.
2. **β-invariant factor base: a bounded lever.** ratio ≈ **1.5×**, *decreasing* (1.61→1.48)
   toward a constant, **not growing with p**, and **below the naïve automorphism factor 3**
   (`=|β-orbit|`). This is the shape of the known automorphism speedup — a constant factor —
   not an asymptotic one.

## Bounded statement + scope

On the CM curve, a β-invariant factor base yields ~1.5× more index-calculus relations per
element than a random one — a genuine but **constant, non-growing** lever (p=1009→10009,
F~√p, B=120). A random factor base shows no CM advantage. A constant factor does not change
the exponential cost of ECDLP, so this is a fence observation, not a gate.

**Not tested:** secp's p; larger / structured factor bases; the higher summation polynomials
`S₄, S₅…` (m-point decompositions) whose Gröbner/resultant structure is the real index-
calculus bottleneck — this probe solves `S₃` via the group law and counts, it does not
analyze the elimination structure of `S₄⁺`; whether the μ₆ (full Aut, including the y-sign)
rather than just β gives a different factor.

## Where this sits in the programme

This is the sixth low-order object built this session and the most DLP-adjacent. Same
verdict shape as the others: **the CM/GLV symmetry is the one real structure, and here it
gives a bounded constant lever (~1.5×) exactly where index calculus would use it — real,
quantified, and not asymptotic.** The genuinely un-probed frontier remains the higher
summation polynomials `S₄⁺` (the elimination/Gröbner structure, not just relation counting)
and the same objects at secp's p.
