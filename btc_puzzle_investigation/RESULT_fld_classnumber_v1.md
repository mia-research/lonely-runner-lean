# The ⟨σ,χ2⟩ conservation is a class number: FLD(p) = ±6·h(−p) at p≡19 mod 24

Date: 2026-07-19. Scripts `_fld_involution_hunt_v1.py`, `_fld_classnumber_check_v1.py` (exact ints).
Continues `RESULT_reflection_conservation_hunt_v1` — which killed the within-F_p reflection
mechanism and named the target: reduce `FLD(p) = Σ_x σ(x)χ2(x)` and explain the p≡3 vs 7 mod 8
split. Target reached: the deeper object is the class number.

## Exact reduction (proven, verified all p)
For p ≡ 3 mod 4, x→−x swaps T+↔T− (σ odd) and sends χ2→−χ2 (χ2(−1)=−1), so
**`FLD = 2·Σ_{x∈T+} χ2(x)`** — verified `identity=OK` at every prime. T+ = {x : u(x)−v(x) > ½} is the
positive flap triangle in the Eisenstein fundamental domain. σ·χ2 is μ6-invariant (p≡3 mod4), and
T+ is μ3-invariant, so `FLD = 6·Σ_{μ3-orbits in T+} χ2` = 6·(#QR − #NQR μ3-orbits in T+).

## The law (empirical, exact match)
Over p ∈ [100,2000), p ≡ 1 mod 6:
- **|FLD(p)| = 6·h(−p)** for every p ≡ 19 mod 24 — **34/34**, h(−p) ∈ {1,3,5,7,9,11} (growing; not a
  small-value coincidence). h by reduced binary-form count; h(−163)=1 (Heegner) validates it.
- **FLD(p) = 0** for every p ≢ 19 mod 24 — **103/103** (covers p≡1,7,13 mod 24).

p ≡ 19 mod 24 ⇔ (p ≡ 3 mod 8) AND (p ≡ 1 mod 3). So the nonvanishing needs BOTH the quadratic
condition (χ2(2)=−1) AND the cubic/Eisenstein condition (μ3 present).

## Why no F_p symmetry enforced it (recap) and what does
No multiplicative c, and no D₆ reflection, flips σ·χ2 (both killed exactly), because conjugation
does not descend to F_p (it maps to the conjugate prime = twist). The enforcing object is the
class number of ℚ(√−p) — genuinely outside F_p, per the mantra.

## Mechanism (partly proven, the reduction is the remaining step)
- **χ2(2) = the p mod 8 factor** enters through **Dirichlet's class-number formula** for p≡3 mod 4:
  `Σ_{a=1}^{(p−1)/2} χ2(a) = (2 − χ2(2))·h(−p)`. The factor (2−χ2(2)) is exactly the p mod 8
  dependence the reflection hunt isolated: 1 at p≡7 mod 8, 3 at p≡3 mod 8.
- The triangle sum `Σ_{T+}χ2` is NOT the classical half-interval sum (they disagree at p≡7 mod 8,
  where the triangle sum is 0 but the interval sum is h(−p)≠0). The vanishing at p≡7 mod 24 is
  triangle-specific and requires the **μ3 (Eisenstein) cut** combined with χ2 — i.e. the arithmetic
  of the biquadratic field **ℚ(√−p, ω) = ℚ(√−p, √−3)**, whose splitting law is the p mod 24 condition.

## Proven / empirical / open
- PROVEN: `FLD = 2Σ_{T+}χ2 = 6Σ_{μ3-orbits in T+}χ2` (negation + μ3-invariance; verified exactly).
- EMPIRICAL (34+103, p<2000, exact): `|FLD| = 6h(−p)` at p≡19 mod24, else 0.
- OPEN (the reduction, a genuine number-theory step):
  1. Prove `Σ_{μ3-orbits in T+} χ2 = ±h(−p)` at p≡19 mod24 via the class-number formula in
     ℚ(√−p,√−3) (the triangle is the fundamental domain cut; the μ3-orbit count is the cubic part).
  2. Prove the exact zero at p≡7 mod 24 (χ2(2)=+1 with μ3 present) — the load-bearing 3-vs-7 mod 8
     separation, unexplained by any conductor-≤8 character alone.
  3. The **sign** of FLD (+/−) at p≡19 mod24 is a finer invariant, not yet identified
     (139:+ 163:+ 211:− 283:+ 331:− 547:− 571:− … ) — candidate: sign of the Dirichlet sum / a genus
     character.

## Scope / exactness
Exact integers throughout (σ, χ2, form-count h). p ∈ [100,2000), p ≡ 1 mod 6, 137 primes (FLD needs
only σ, χ2 — no n-prime filter). No float in the signal path.
