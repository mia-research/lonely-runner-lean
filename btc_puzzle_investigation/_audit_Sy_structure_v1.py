#!/usr/bin/env python3
"""
_audit_Sy_structure_v1.py -- I called Sy 'generic'. That is a dismissal word. CHARACTERIZE it.

The bias I'm auditing (feedback_negative_bias_enlarge_nulls): I ran ONLY a null test on Sy
(is Sy==0 more than chance?) and, seeing no, wrote 'generic / no leak'. A bound is a MAGNITUDE,
not 'no structure' -- structure lives in a VALUE LAW / symmetry-type / subspace I never looked at.

Sy = sum_P s_y(P) chi2(y_P).  At p=3 mod4:  Sy = 2 * sum_{x: x^3+7 is QR} chi2(y0(x)),
y0 = the root in (0,p/2). This is a real character sum. Questions I SHOULD have asked:
  1. Does Sy have an exact VALUE law (Sy mod m; Sy vs a,b,t,f, class number h(-p) etc.)?
  2. Is Sy/2 bounded by 2*sqrt(p) (Weil) -- i.e. is it AT a magnitude, and does that magnitude
     carry a scaling exponent? (magnitude != nothing)
  3. Is Sy's SIGN structured (a p-mod law), even if |Sy| is generic?
  4. Does Sy correlate with the KNOWN shadow bit or with H(x) type quartic objects?
Exact ints; float only for the reported magnitude ratios.
"""
import sys, math
from sympy import isprime
from sympy.ntheory.residue_ntheory import sqrt_mod
from lift_sextant_rhombus_law_proof_v2 import cornacchia_4p_D3
from _sigma_chi2_scan_v1 import chi2_table

def run(p):
    chi2 = chi2_table(p)
    half = (p - 1) // 2
    Sy = 0
    for x in range(p):
        rhs = ((x * x % p) * x + 7) % p
        if chi2(rhs) != 1: continue
        y = sqrt_mod(rhs, p) % p
        for yy in (y, (p - y) % p):
            s = 1 if yy <= half else -1
            Sy += s * chi2(yy)
    n = p + 1 + sum(chi2(((x * x % p) * x + 7) % p) for x in range(p))
    if not isprime(n): return None
    pi = cornacchia_4p_D3(p); a, b = pi
    tr = p + 1 - n
    return {'p': p, 'n': n, 'Sy': Sy, 'pmod8': p % 8, 'pmod4': p % 4, 'pmod24': p % 24,
            'a': a, 'b': b, 'tr': tr}

def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 4000
    rows = [r for p in range(lo, hi) if p % 6 == 1 and isprime(p) and p != 7
            for r in [run(p)] if r]
    r3 = [r for r in rows if r['pmod4'] == 3]           # Sy nonforced here
    print(f"# Sy structure audit, p=3 mod4 (nonforced), {len(r3)} primes in [{lo},{hi})")
    print(f"# {'p':>6} {'m8':>3} {'Sy':>6} {'Sy/2':>6} {'Sy/2 mod':>9} {'|Sy|/2sqrtp':>11} {'sign':>5}")
    for r in r3:
        s2 = r['Sy'] // 2
        ratio = abs(r['Sy']) / (2 * math.sqrt(r['p']))
        print(f"  {r['p']:>6} {r['pmod8']:>3} {r['Sy']:>6} {s2:>6} {s2%6:>9} {ratio:>11.3f} {('+' if r['Sy']>0 else ('-' if r['Sy']<0 else '0')):>5}")

    print("\n--- CHARACTERIZATION (not a null test) ---")
    # (1) is Sy/2 always divisible by something? gcd
    from math import gcd
    from functools import reduce
    g = reduce(gcd, [abs(r['Sy']) for r in r3 if r['Sy'] != 0])
    print(f"(1) gcd of all |Sy| (p=3 mod4): {g}   -> Sy is always a multiple of {g}")
    # (2) magnitude: is |Sy|/2 <= 2 sqrt(p)? (Weil). scaling of |Sy| with sqrt(p)?
    ratios = [abs(r['Sy']) / (2 * math.sqrt(r['p'])) for r in r3 if r['Sy'] != 0]
    print(f"(2) |Sy|/(2 sqrt p): max {max(ratios):.3f}, mean {sum(ratios)/len(ratios):.3f}"
          f"  (a MAGNITUDE at the Weil scale, not 'nothing')")
    # (3) SIGN law: is sign(Sy) a function of p mod 8 / 24?
    print("(3) sign(Sy) by p mod 8:")
    for m8 in (3, 7):
        s = [r for r in r3 if r['pmod8'] == m8 and r['Sy'] != 0]
        pos = sum(1 for r in s if r['Sy'] > 0); neg = len(s) - pos
        print(f"      p={m8} mod8: {len(s):>3} nonzero, + : {pos:>3}, - : {neg:>3}"
              f"  {'<-- SIGN LAW?' if pos==0 or neg==0 else ''}")
    print("(3b) sign(Sy) by p mod 24:")
    for m in sorted(set(r['pmod24'] for r in r3)):
        s = [r for r in r3 if r['pmod24'] == m and r['Sy'] != 0]
        if not s: continue
        pos = sum(1 for r in s if r['Sy'] > 0); neg = len(s) - pos
        print(f"      p={m:>2} mod24: + {pos:>3} / - {neg:>3}  {'<-- ALL ONE SIGN' if pos==0 or neg==0 else ''}")
    # (4) exact value law: Sy vs 2a-... etc? check Sy == +-2b, +-2a, +-2(2a-b) etc
    print("(4) exact value matches Sy vs CM forms:")
    from collections import Counter
    c = Counter()
    for r in r3:
        for name, v in [('2b', 2*r['b']), ('-2b', -2*r['b']), ('2a', 2*r['a']), ('-2a', -2*r['a']),
                        ('2(2b-a)', 2*(2*r['b']-r['a'])), ('2tr', 2*r['tr']), ('-2tr', -2*r['tr']),
                        ('2(a-2b)', 2*(r['a']-2*r['b']))]:
            if r['Sy'] == v: c[name] += 1
    print(f"      {dict(c)}  (out of {len(r3)})")

if __name__ == '__main__':
    main()
