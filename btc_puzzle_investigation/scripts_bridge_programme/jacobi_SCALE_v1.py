#!/usr/bin/env python3
"""SCALE TEST for RESULT_jacobi_sign_law_semiprimitive_v1.
Everything there was verified on 12 primes with p <= 83.  This extends (S), the G(chi4) rule, and the
J(chi3,chi4) sign law to every p = 3 mod 4 up to a much larger bound, with the FC1 discrimination
control re-run at scale.  Exact arithmetic (Z[zeta_12]); no floats."""
import sys, math
exec(open('jacobi_semiprimitive_v1.py').read().split('print("=== (S)')[0])

def gauss_e(p, e12, els, dlog):
    coeff = [ZERO[:] for _ in range(p)]
    for x in els:
        coeff[(2*x[0]) % p] = zadd(coeff[(2*x[0]) % p], zpow_zeta12((dlog[x]*e12) % 12))
    diffs = [zsub(coeff[t], coeff[0]) for t in range(1, p)]
    v = diffs[0]
    if any(d != v for d in diffs): return None
    m = [-c for c in v]
    return m[0] if is_rat_int(m) else m

LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 300
def isp(n):
    if n < 2: return False
    for q in range(2, int(n**0.5)+1):
        if n % q == 0: return False
    return True
PR = [p for p in range(7, LIM+1) if p % 4 == 3 and isp(p)]
print(f"SCALE TEST: {len(PR)} primes p = 3 mod 4 in [7, {LIM}]   (the paper used 12 primes, p <= 83)")
print(f"  largest p = {PR[-1]}   |F_p^2| = {PR[-1]**2}\n")

S_ok = S_tot = 0; G4_ok = G4_tot = 0
J11_ok = J11_tot = 0; J7_ok = J7_tot = 0; FC1_ok = FC1_tot = 0
badS = []; badG = []; badJ = []
for p in PR:
    els, dlog, order = build_field(p)
    for d in (2, 3, 4, 6, 12):
        if (p+1) % d == 0:
            g = gauss_e(p, 12//d, els, dlog); pred = (-1)**((p+1)//d) * p
            S_tot += 1; S_ok += (g == pred)
            if g != pred: badS.append((p, d, g, pred))
            if d == 4:
                G4_tot += 1
                rec = p if p % 8 == 7 else -p
                G4_ok += (g == rec == pred)
                if not (g == rec == pred): badG.append((p, g, rec))
        elif (p-1) % d == 0:                       # FC1 discrimination control, at scale
            g = gauss_e(p, 12//d, els, dlog)
            FC1_tot += 1; FC1_ok += (not isinstance(g, int)) or abs(g) != p
    J = jacobi(p, 3, 4, els, dlog, order)
    Jv = J[0] if is_rat_int(J) else None
    if p % 12 == 11:
        J11_tot += 1; J11_ok += (Jv == p)
        if Jv != p: badJ.append((p, 11, Jv))
    else:
        J7_tot += 1; J7_ok += (Jv == -p)
        if Jv != -p: badJ.append((p, 7, Jv))
    if p % 25 == 0 or p == PR[-1]: sys.stdout.flush()

print(f"  (S)   g(chi_d) = (-1)^((p+1)/d) p , all d | p+1 : {S_ok}/{S_tot}   fails: {badS[:3]}")
print(f"  G4    record's barred rule (+p p=7mod8, -p 3mod8): {G4_ok}/{G4_tot}   fails: {badG[:3]}")
print(f"  J     p = 11 mod 12  ->  J = +p                  : {J11_ok}/{J11_tot}")
print(f"  J     p =  7 mod 12  ->  J = -p                  : {J7_ok}/{J7_tot}   fails: {badJ[:3]}")
print(f"  FC1   non-semiprimitive d does NOT give +-p      : {FC1_ok}/{FC1_tot}  (discrimination holds at scale)")
print(f"\n  primes tested: {len(PR)}  (was 12);  max p = {PR[-1]}  (was 83)")
