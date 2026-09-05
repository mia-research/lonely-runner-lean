#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
cartier_manin_idea_check_v1.py — is the artifact's Cartier-Manin IDEA sound?

Two checks (exact, integer), idea-level not method-level:
 (A) Validate the Hasse-Witt method + the artifact's number: for E: y^2=x^3+7,
     the coeff of x^(p-1) in (x^3+7)^((p-1)/2) should equal t_E mod p.
     Artifact claims C(omega_1)=13=t_E at p=43. Check it, and across primes.
 (B) The A_new vanishing mechanism: coeff of x^(p-1) in x^a*(x^3+7)^((p-3)/4)
     for p=3 mod 4 — the artifact says it vanishes because deg < p-1. Verify the
     degree bound AND the vanishing, across primes. (Whether this coeff is exactly
     the A_new Hasse-Witt entry of the w^4 cover is the 'method' detail; the
     structural p=3 mod 4 vanishing is the 'idea'.)
"""
def poly_pow_coeff(fcoeffs, power, target_deg, pmod):
    # coefficient of x^target_deg in (f)^power mod pmod, f given as dict deg->coeff
    from collections import defaultdict
    acc = {0: 1}
    base = dict(fcoeffs)
    e = power
    # simple repeated multiply (powers are small here)
    res = {0: 1}
    for _ in range(power):
        new = defaultdict(int)
        for d1, c1 in res.items():
            for d2, c2 in base.items():
                if d1 + d2 <= target_deg:            # prune
                    new[d1+d2] = (new[d1+d2] + c1*c2) % pmod
        res = dict(new)
    return res.get(target_deg, 0) % pmod

def tE_of_x3p7(p):
    # exact trace via point count of y^2 = x^3 + 7 over F_p
    cnt = 1  # point at infinity
    for x in range(p):
        rhs = (x*x*x + 7) % p
        if rhs == 0:
            cnt += 1
        elif pow(rhs, (p-1)//2, p) == 1:
            cnt += 2
    return p + 1 - cnt

f = {3: 1, 0: 7}   # x^3 + 7

print("="*80)
print(" (A) Hasse-Witt of E: coeff x^(p-1) in (x^3+7)^((p-1)/2)  ==  t_E mod p ?")
print("="*80)
for p in [7, 11, 13, 19, 23, 31, 43, 67]:
    hw = poly_pow_coeff(f, (p-1)//2, p-1, p)
    t = tE_of_x3p7(p) % p
    tag = "SS(p=2mod3)" if p % 3 == 2 else "ord(p=1mod3)"
    print(f"  p={p:3d} ({tag}): HW={hw:3d}  t_E mod p={t:3d}  match={hw==t}  "
          f"{'[HW=0 => supersingular]' if hw==0 else ''}")

print("\n" + "="*80)
print(" (B) A_new mechanism: coeff x^(p-1) in x^a*(x^3+7)^((p-3)/4), p=3 mod 4")
print("     deg = 3*(p-3)/4 + a  vs  p-1   (artifact: strictly less => vanishes)")
print("="*80)
for p in [7, 11, 19, 23, 31, 43, 59, 67]:
    if p % 4 != 3:
        continue
    powr = (p-3)//4
    deg_max = 3*powr + 1
    c0 = poly_pow_coeff(f, powr, p-1, p)                 # a=0 term coeff of x^(p-1)
    # a=1: coeff of x^(p-1) in x*(...) = coeff of x^(p-2) in (...)
    c1 = poly_pow_coeff(f, powr, p-2, p)
    print(f"  p={p:3d}: (p-3)/4={powr:2d}  deg_max={deg_max:3d} < p-1={p-1:3d}: {deg_max < p-1}"
          f"   coeff(a=0)={c0}  coeff(a=1)={c1}  both_zero={c0==0 and c1==0}")
print("="*80)
