# "Outside the symmetry" — free descended-character content of the μ6-invariant flap

Date: 2026-07-18. Pre-registered by `experiment-designer`. Tests the hypothesis: a leak/telling
structure lives OUTSIDE the symmetry, not in the μ6-invariant skeleton. Script `scratchpad/e_outside.py`.

## The provable framing (why the hypothesis is the right instinct)
Aut(E)=μ6 acts on the scalar by d↦λd and d↦−d. So ANY μ6-invariant readout of P=dG is constant on
the orbit {±d,±λd,±λ²d} — it cannot distinguish d from the other five. **Pinning d requires an
anti-invariant readout.** The invariant/symmetric part is provably leak-free FOR PINNING d; whatever
cheaply pins d, if anything does, must live outside the symmetry. This is forced by the group action.

## What this test checked (#1 — the invariant side)
Whether the μ6-INVARIANT objects (flap eps; μ6-symmetrized norm N̄) carry free multiplicative-character
content over the quotient Q=F_p*/μ6 — the descended characters (order | (p−1)/6) the symmetry does NOT
force to zero (Part B only tested the forced μ6-dual set χ2/χ3/χ6). Fold to period L=(p−1)/6 (excises DC
+ the forced-zero dual set); statistic R=max_{m≥1}P[m]/S (top descended char's power share) and
N_eff=S²/ΣP[m]² (subspace/orbit concentration guard); matched null = permute the L period-values across
quotient classes, B=20000; planted square-wave positive control.

| p | feature | R | exc_R/20000 | N_eff | exc_N/20000 | verdict |
|---|---|---|---|---|---|---|
| 100003 (≡3 mod4) | eps | 0.00040 | 19999 | 9465 | 20000 | within/below null (flat) |
| 100003 | N̄ | 0.00029 | 20000 | 11290 | 20000 | within/below null (flat) |
| 100057 (≡1 mod4) | eps | 0.00036 | 20000 | 9536 | 20000 | within/below null (flat) |
| 100057 | N̄ | 0.00026 | 20000 | 11303 | 20000 | within/below null (flat) |
| both | PLANT m0=1,7 | 0.405 | **0** | 3.0 | **0** | FIRES, recovers m0 (m=7→conj L−7 on p2) |

**Verdict (pre-registered): SCOPED NULL "geometric even on the quotient."** Planted controls fired
(apparatus alive; smallest detectable single-character share φ_min ≈ 10/L ≈ 6·10⁻⁴). Beyond the forced
μ6-dual zeros, eps and N̄ show NO descended-character concentration — in fact flatter than random
rearrangements — on both primes (in- and out-of-sample, across the p mod 4 change). POWER+SCOPE:
exhaustive x∈[1,p), p∈{100003,100057}, no concentration above share φ_min. NOT "the flap has no
structure" — its structure is entirely geometric (norm-band/sextant), with no multiplicative-character
component even in the part the symmetry leaves free.

## Crucial scope limit (what this does NOT address)
eps and N̄ are μ6-INVARIANT, so by the provable framing above they cannot pin d regardless of this
result. This test bounds the FIELD-arithmetic of the flap; it is **silent on d-leakage**. The faithful
test of the hypothesis is the ANTI-invariant side (#2): whether any cheap anti-invariant readout —
the only kind that can pin d — carries structure. So far the only evidence is E2's alignment floor for
5 cheap readouts (lsb x, sign y, Legendre x, sextant, eps) at ~log n/n on 2 small curves — a spot
check, not a sweep, and exactly the joint/two-point/unbounded-degree frontier the programme leaves open.

## Net
The symmetric skeleton is now closed off from two sides — forced-zero on the μ6-dual characters (Part B)
and flat on the free descended characters (here). Consistent with the theorem that it cannot carry d.
The hypothesis "the leak lives outside the symmetry" is CORRECT and proven at the level of group action;
this test confirms nothing lives in the invariant part; it does not probe the anti-invariant part where
d actually lives. That probe (#2) is the next pre-registered step and coincides with the open frontier.
