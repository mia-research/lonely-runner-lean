#!/usr/bin/env sage
# brick2_converse_v1 — is the identity EQUIVALENT to the tensor structure, or only implied by it?
# Symbolic: with e1=t free, e2=t^2-leg*p, e3=leg*p*t, e4=p^2, check that the quartic factors
# IDENTICALLY as (T^2-s1*T+s2)(T^2-rho*s1*T+rho^2*s2) with s1=-rho*t, s2=rho^2*e3/e1, rho^3=1.
# If this is a polynomial identity in t, the converse holds and
#   T2 (finite level)  <=>  V2 = V1^2 - 2*leg*p   exactly, with nothing left over.
R.<t, p, leg> = QQ[]
K.<w> = CyclotomicField(3)          # w = rho, primitive cube root
S = PolynomialRing(K, ['t','p','leg']); t, p, leg = S.gens()
T = PolynomialRing(FractionField(S), 'T').gen()
for rho in (w, w**2):
    e1 = t; e2 = t**2 - leg*p; e3 = leg*p*t; e4 = p**2
    quartic = T**4 - e1*T**3 + e2*T**2 - e3*T + e4
    s1 = -rho*t
    s2 = rho**2 * e3/e1  # noqa: float — exact division in FractionField of a polynomial ring over Q(zeta_3), symbolic, not IEEE
    g1 = T**2 - s1*T + s2
    g2 = T**2 - rho*s1*T + rho**2*s2
    print(f"rho = {rho}:  g1*g2 == quartic ?  {(g1*g2 - quartic).is_zero()}")
    print(f"           roots(g2) = rho*roots(g1) by construction; "
          f"e3^2 - e4*e1^2 = {(e3**2 - e4*e1**2)}")
