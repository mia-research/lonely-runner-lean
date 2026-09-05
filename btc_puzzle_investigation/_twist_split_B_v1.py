#!/usr/bin/env python3
"""
_twist_split_B_v1.py -- the object behind "FLD == CRV". Exact ints only.

v33/v34 dismissed "FLD == CRV" as chance (6/22, 2/26 out-of-sample). That tested the WRONG
object. The algebra:

    1 - chi2(x^3+7)  =  0 on E's x-set,  2 on the TWIST's x-set   (no 2-torsion => never 1)
    FLD - CRV = sum_x sigma chi2 [1 - chi2(x^3+7)] = 2 * B ,
    B := sum_{x : chi2(x^3+7) = -1} sigma(x) chi2(x)          <- the sum over the SEXTIC TWIST

So  FLD == CRV  <=>  B == 0.  "Are two numbers equal" was a bad question; B is the object.

Decompose the field sum by which curve x lives on:
    A := sum_{x : chi2(x^3+7)=+1} sigma chi2      (E's x-set)
    B := sum_{x : chi2(x^3+7)=-1} sigma chi2      (twist's x-set)
    FLD = A + B ,  CRV = A - B          [exact identity, verified]

PARITY STRUCTURE (derived, pre-registered before the run):
  at p=3 mod 4, sigma*chi2 is mu6(F_p)-invariant. The twist x-set W = {x : chi2(x^3+7)=-1} is
  mu3-stable, since (beta x)^3 + 7 = x^3 + 7. It is NOT negation-stable: (-x)^3+7 = -(x^3-7).
  mu3 acts freely on F_p^*. Hence  B = 3 * sum_{mu3-orbits in W cap flap} (+-1) , so
        3 | B    and    B/3 = NW (mod 2),   NW := #(W cap flap)/3.
  => B = 0 REQUIRES NW even. Same shape as the S law (v34 section 4).

THE TEST: is B == 0 whenever parity ALLOWS it (NW even)? If yes, this is a SECOND instance of
the same unexplained conservation, not a fluke. Same for A with NE := #(E-x cap flap)/3.

Power: for NW even, a generic signed sum gives P(B=0) ~ 2/sqrt(2 pi NW). Reported per prime and
summed, so "observed vs expected" is a number, not an impression.
"""
import sys
from sympy import isprime
from _sigma_chi2_scan_v1 import chi2_table, build, sigma_fn

def run(p):
    chi2 = chi2_table(p)
    n = p + 1 + sum(chi2(((x * x % p) * x + 7) % p) for x in range(p))
    if not isprime(n): return None
    eis, eps, beta, R1, R2, DET = build(p)
    sig, orient = sigma_fn(p, eis, eps, R1, R2, DET)
    if sig is None: return {'p': p, 'FAIL': 'orientation'}
    A = B = 0
    NE = NW = 0
    for x in range(p):
        w = chi2(((x * x % p) * x + 7) % p)
        s = sig(x)
        if s == 0: continue
        v = s * chi2(x)
        if w == 1: A += v; NE += 1
        elif w == -1: B += v; NW += 1
    FLD = A + B
    CRV = A - B
    assert NE % 3 == 0 and NW % 3 == 0, f"flap-cap-curve sets not mu3-stable at p={p}"
    assert A % 3 == 0 and B % 3 == 0, f"3 does not divide A or B at p={p}"
    return {'p': p, 'n': n, 'pmod4': p % 4, 'pmod8': p % 8, 'orient': orient,
            'A': A, 'B': B, 'FLD': FLD, 'CRV': CRV, 'NE': NE // 3, 'NW': NW // 3}

def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 6000
    rows = []
    for p in range(lo, hi):
        if p % 6 != 1 or not isprime(p) or p == 7: continue
        r = run(p)
        if r is None or 'FAIL' in (r or {}): continue
        rows.append(r)
    print(f"# p in [{lo},{hi}), p=1 mod 6, n prime. NE/NW = # mu3-orbits of the flap on E's / the TWIST's x-set.")
    print(f"# {'p':>6} {'m8':>3} {'NE':>5} {'NW':>5} {'NW%2':>5} {'A':>6} {'B':>6} {'B==0':>6} "
          f"{'FLD':>6} {'CRV':>6} {'FLD==CRV':>9}")
    for r in rows:
        print(f"  {r['p']:>6} {r['pmod8']:>3} {r['NE']:>5} {r['NW']:>5} {r['NW']%2:>5} "
              f"{r['A']:>6} {r['B']:>6} {str(r['B']==0):>6} {r['FLD']:>6} {r['CRV']:>6} "
              f"{str(r['FLD']==r['CRV']):>9}")
        assert (r['B'] // 3) % 2 == r['NW'] % 2, f"B parity obstruction violated at p={r['p']}"
        assert (r['A'] // 3) % 2 == r['NE'] % 2, f"A parity obstruction violated at p={r['p']}"
    print()
    import math
    for label, key, nkey in (('B (TWIST x-set)', 'B', 'NW'), ('A (E x-set)', 'A', 'NE')):
        ev = [r for r in rows if r[nkey] % 2 == 0]
        od = [r for r in rows if r[nkey] % 2 == 1]
        z_ev = sum(1 for r in ev if r[key] == 0)
        z_od = sum(1 for r in od if r[key] == 0)
        exp = sum(2 / math.sqrt(2 * math.pi * r[nkey]) for r in ev if r[nkey] > 0)
        print(f"{label}:")
        print(f"   parity EVEN (zero ALLOWED) : {len(ev):>3} primes, {key}==0 in {z_ev:>3}"
              f"   | generic expectation {exp:.2f}")
        print(f"   parity ODD  (zero FORBIDDEN): {len(od):>3} primes, {key}==0 in {z_od:>3}  (must be 0)")
    print()
    print("Compare: the S law (v34 s4) had EVEN->0 in 22/22 vs generic 1.86 == an exact law.")

if __name__ == '__main__':
    main()
