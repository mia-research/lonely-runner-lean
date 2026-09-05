#!/usr/bin/env python3
"""
_odd_sector_conservation_v1.py -- follow the S phenomenon into the ODD (y) sector.  Exact ints.

MANTRA: the leak / telling structure lives OUTSIDE the (even, x-only) symmetry. The odd sector
(j=1, the y-coordinate = the shadow half x is blind to, v16) is that outside. S = <sigma,chi2>_FIELD
is an EVEN/x-only conservation (p!=3 mod 8, 35/35). Does the SAME phenomenon recur in the odd sector?

THE ODD ANALOG. Over the curve, each x with chi2(x^3+7)=+1 gives TWO points (x,y),(x,-y). For an
odd-in-y readout the two cancel unless something breaks it. Take
    Sy := sum_{P != O} s_y(P) * chi2(y_P) ,   s_y = sign(y centered), both ODD in y.
Their product is EVEN in y, so per x:  s_y(y)chi2(y) + s_y(-y)chi2(-y)
   = sign(y)chi2(y) [1 - chi2(-1)]  =  0            if p = 1 mod 4  (chi2(-1)=+1)  -- FORCED
                                       2 sign(y)chi2(y)  if p = 3 mod 4            -- NOT forced
So Sy = 0 at p=1 mod 4 (forced, like FLD), and Sy = 2*sum_{x:QR} sign(y)chi2(y) at p=3 mod 4.

QUESTION (mantra step 1-2): at p=3 mod 4, is Sy an exact conservation with a p mod 8 (or other)
law -- a SECOND instance of the S phenomenon, now in the shadow sector? If yes, that is the deeper
structure the two share. If Sy is generic (Weil-scale, no exact zeros beyond chance), the S law is
x-only-special and does NOT extend to the shadow -- also a clean, informative result.

Method: exact integer Sy; parity/forcing structure derived and asserted; the "is it 0 more than
chance" question uses a MATCHED count (how many p=7 mod 8 vs p=3 mod 8 give Sy=0), reported with the
generic expectation. Sign path exact; float only for the generic-rate reference.

Also re-confirms the S reflection-kill summary for the record.
"""
import sys, math
from sympy import isprime
from sympy.ntheory.residue_ntheory import sqrt_mod
from _sigma_chi2_scan_v1 import chi2_table

def run(p):
    chi2 = chi2_table(p)
    half = (p - 1) // 2
    Sy = 0
    Ny = 0                              # number of QR-x (points come in pairs) -- for orbit parity
    for x in range(p):
        rhs = ((x * x % p) * x + 7) % p
        c = chi2(rhs)
        if c != 1:
            continue                    # c=0 impossible (no 2-torsion); c=-1 no points
        y = sqrt_mod(rhs, p)
        if y is None:
            continue
        y %= p
        for yy in (y, (p - y) % p):
            s = 1 if yy <= half else -1
            Sy += s * chi2(yy)
        Ny += 1
    n = p + 1 + sum(chi2(((x * x % p) * x + 7) % p) for x in range(p))
    if not isprime(n):
        return None
    return {'p': p, 'n': n, 'pmod4': p % 4, 'pmod8': p % 8, 'Sy': Sy, 'Ny': Ny}

def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 6000
    rows = []
    for p in range(lo, hi):
        if p % 6 != 1 or not isprime(p) or p == 7:
            continue
        r = run(p)
        if r:
            rows.append(r)
    print(f"# Sy = sum_P s_y(P) chi2(y_P), p in [{lo},{hi}), p=1 mod 6, n prime. kept={len(rows)}")
    print(f"# {'p':>6} {'m4':>3} {'m8':>3} {'Ny':>5} {'Sy':>6} {'Sy==0':>6} {'Sy^2/p':>8}")
    from fractions import Fraction as Fr
    p1 = p3 = 0
    for r in rows:
        if r['pmod4'] == 1:
            assert r['Sy'] == 0, f"FORCED zero (p=1 mod4) VIOLATED at p={r['p']}: Sy={r['Sy']}"
            p1 += 1
        else:
            p3 += 1
        c2p = Fr(r['Sy'] * r['Sy'], r['p'])
        print(f"  {r['p']:>6} {r['pmod4']:>3} {r['pmod8']:>3} {r['Ny']:>5} {r['Sy']:>6} "
              f"{str(r['Sy']==0):>6} {str(c2p.limit_denominator(100)):>8}")
    print()
    print(f"FORCED zeros p=1 mod 4 : {p1}/{p1} (Sy=0, all -- as derived)")
    r3 = [r for r in rows if r['pmod4'] == 3]
    z3 = [r for r in r3 if r['Sy'] == 0]
    print(f"NON-forced p=3 mod 4   : {len(r3)} primes, Sy==0 in {len(z3)}")
    # does the S law's p mod 8 split appear here too?
    for m8 in (3, 7):
        s = [r for r in r3 if r['pmod8'] == m8]
        z = [r for r in s if r['Sy'] == 0]
        # generic expectation for an integer sum of scale sqrt(p): P(0) ~ c/sqrt(Ny)
        exp = sum(1 / math.sqrt(max(1, r['Ny'])) for r in s)
        print(f"   p={m8} mod 8: {len(s):>3} primes, Sy==0 in {len(z):>3}  (generic ~ {exp:.2f})")
    print()
    print("READ: if p=7 mod 8 shows Sy==0 far above generic (like the S law's 35/35), the shadow")
    print("sector carries the SAME conservation -> deeper shared symmetry. If Sy is generic, S is")
    print("x-only-special and does NOT extend to the odd/shadow half (also informative, scoped).")
    print()
    print("S-law reflection-kill (recorded): NO D_6 lattice symmetry of F_p enforces S. Rotations")
    print("= mu6 (S lives outside them); reflections z->zeta6^k zbar do NOT descend because")
    print("L=(pi_p) != Lbar=(pi_p bar) (p splits in Z[omega]). Confirmed: _reflection_symmetry_hunt_v1.")

if __name__ == '__main__':
    main()
