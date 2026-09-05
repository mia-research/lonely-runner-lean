#!/usr/bin/env python3
"""
_flap_count_formula_hunt_v1.py -- find the EXACT closed form for the flap count (toward H1).

H1 (v36, verified 44/44): for p=3 mod 4, flap = 6*ORB with ORB even <=> p=7 mod 8, i.e.
   flap = 0 mod 12  <=>  p = 7 mod 8 ,   flap = 6 mod 12  <=>  p = 3 mod 8.
The flap count = #{x in F_p : eis(x) in the flap region |u-v|>1/2 of the rhombus} is a
Gauss-circle-type lattice-point count. To DERIVE H1 we first need the exact flap(p).

This script gathers flap(p) exactly and correlates it with the CM data:
   pi_p = a + b*omega,  N(pi_p)=a^2-ab+b^2 = p,  t = 2a-b (Frobenius trace),  4p = t^2 + 3f^2.
Hunts:  4*flap - p  vs  {t, a, b, f, and their residues};  flap vs (p +- t +- 1)/4 forms;
        flap mod small numbers vs p mod 8/12/24.  Exact ints only.
"""
import sys
from fractions import Fraction as Fr
from sympy import isprime, primitive_root
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv, cornacchia_4p_D3, enorm
from _sigma_chi2_scan_v1 import chi2_table, build, sigma_fn

def flap_count(p, eps):
    return sum(1 for x in range(p) if eps(x) != 0)

def run(p):
    chi2 = chi2_table(p)
    n = p + 1 + sum(chi2(((x * x % p) * x + 7) % p) for x in range(p))
    if not isprime(n): return None
    eis, eps, beta, R1, R2, DET = build(p)
    sig, orient = sigma_fn(p, eis, eps, R1, R2, DET)
    if sig is None: return {'p': p, 'FAIL': 'orient'}
    flap = flap_count(p, eps)
    # CM data
    pi = cornacchia_4p_D3(p)            # (a,b) with a^2-ab+b^2 = p
    a, b = pi
    t = 2 * a - b                       # a trace candidate (sign/rep ambiguity noted)
    # canonical trace: t^2 <= 4p and t = p+1-n_curve? use the actual curve n
    tr = p + 1 - n
    # 4p = tr^2 + 3 f^2
    f2 = (4 * p - tr * tr)
    f = None
    if f2 % 3 == 0:
        import math
        fr = math.isqrt(f2 // 3)
        if fr * fr * 3 == f2: f = fr
    return {'p': p, 'n': n, 'flap': flap, 'ORB': flap // 6, 'a': a, 'b': b, 't_pi': t,
            'tr': tr, 'f': f, 'pmod8': p % 8, 'pmod12': p % 12, 'pmod24': p % 24,
            'orient': orient, '4flap_p': 4 * flap - p}

def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 2500
    rows = []
    for p in range(lo, hi):
        if p % 6 != 1 or not isprime(p) or p == 7: continue
        r = run(p)
        if r and 'FAIL' not in r: rows.append(r)
    print(f"# flap-count formula hunt, p in [{lo},{hi}), p=1 mod6, n prime. kept={len(rows)}")
    print(f"# {'p':>6} {'m8':>3} {'m24':>4} {'flap':>5} {'ORB':>4} {'ORB%2':>5} "
          f"{'tr':>6} {'f':>5} {'a':>6} {'b':>6} {'4flap-p':>8} {'orient':>6}")
    for r in rows:
        print(f"  {r['p']:>6} {r['pmod8']:>3} {r['pmod24']:>4} {r['flap']:>5} {r['ORB']:>4} "
              f"{r['ORB']%2:>5} {r['tr']:>6} {str(r['f']):>5} {r['a']:>6} {r['b']:>6} "
              f"{r['4flap_p']:>8} {r['orient']:>6}")

    # hunt 1: is 4*flap - p a simple function of t, f, a, b?
    print("\n--- hunt: 4*flap - p vs CM invariants ---")
    for r in rows[:0]:
        pass
    import math
    for r in rows:
        d = r['4flap_p']
        cands = []
        for name, val in [('tr', r['tr']), ('-tr', -r['tr']), ('2a-p?', 2*r['a']-r['p']),
                          ('a', r['a']), ('b', r['b']), ('a-b', r['a']-r['b']),
                          ('3f', 3*r['f'] if r['f'] else None), ('-3f', -3*r['f'] if r['f'] else None),
                          ('f', r['f']), ('t_pi', r['t_pi']), ('-t_pi', -r['t_pi'])]:
            if val is not None and val == d: cands.append(name)
        # just record matches
        r['dmatch'] = cands
    from collections import Counter
    allm = Counter(m for r in rows for m in r.get('dmatch', []))
    print("  exact matches for (4*flap - p):", dict(allm))

    # hunt 2: ORB parity law -- unified over ALL p (not just p=3 mod4)?
    print("\n--- ORB parity vs residues (ALL p=1 mod6) ---")
    for mod in (8, 12, 24):
        print(f"  p mod {mod}:")
        for res in sorted(set(r['p'] % mod for r in rows)):
            s = [r for r in rows if r['p'] % mod == res]
            ev = sum(1 for r in s if r['ORB'] % 2 == 0)
            od = len(s) - ev
            tag = 'ALL-EVEN' if od == 0 else ('ALL-ODD' if ev == 0 else 'mixed')
            print(f"     {res:>3}: {len(s):>3} primes, ORB even {ev:>3} / odd {od:>3}   {tag}")

if __name__ == '__main__':
    main()
