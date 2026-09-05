#!/usr/bin/env sage
# brick2_converse_v2 — v1 left leg as a free indeterminate (leg^2 != 1 symbolically). Fixed:
# leg is now an actual constant +-1, p a free variable, t = e1 free.
K.<w> = CyclotomicField(3)
S = PolynomialRing(K, ['t', 'p']); t, p = S.gens()
Tp = PolynomialRing(FractionField(S), 'T'); T = Tp.gen()
allok = True
for leg in (1, -1):
    for rho in (w, w**2):
        e1 = t; e2 = t**2 - leg*p; e3 = leg*p*t; e4 = p**2
        quartic = T**4 - e1*T**3 + e2*T**2 - e3*T + e4
        s1 = -rho*t
        s2 = rho**2 * e3/e1  # noqa: float — exact division in FractionField of a polynomial ring over Q(zeta_3), symbolic, not IEEE
        g1 = T**2 - s1*T + s2
        g2 = T**2 - rho*s1*T + rho**2*s2
        ok = (g1*g2 - quartic).is_zero()
        auto = (e3**2 - e4*e1**2).is_zero()
        allok &= ok
        print(f"leg={leg:+d} rho={rho}:  g1*g2 == quartic ? {ok}   |   e3^2==e4*e1^2 identically ? {auto}")
print()
print("CONVERSE HOLDS IDENTICALLY IN (t,p):" , allok)
print("=> at finite level, T2 (roots = S u rho*S)  <=>  e2 = e1^2 - leg*p  <=>  V2 = V1^2 - 2*leg*p,")
print("   with e3^2 = e4*e1^2 automatic and carrying no information.")
