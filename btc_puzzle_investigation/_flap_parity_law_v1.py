#!/usr/bin/env python3
"""
_flap_parity_law_v1.py -- the unified flap-parity law and its reduction toward a proof. Exact ints.

THE LAW (unified over ALL p=1 mod 6, supersedes H1's p=3 mod 4 restriction):
    (-1)^ORB  =  chi2(2)  =  (-1)^((p^2-1)/8) ,     ORB = flap/6.
Equivalently ORB even <=> 2 is a QR mod p <=> p = +-1 mod 8.

REDUCTION toward an Eisenstein-lattice-point proof:
  * The flap = {x : |u-v|>1/2} splits into two triangles T+ (u-v>1/2) and T- (v-u>1/2),
    sigma=+1 / -1. Field negation x->-x sends (u,v)->(-u,-v), swapping T+ <-> T-, no fixed
    point in F_p^* => |T+| = |T-| = flap/2.
  * mu3 (beta = omega^2 rotation) fixes sigma (sigma(beta x)=sigma(x)), so it preserves T+ and
    acts FREELY on T+ cap lattice (only fixed pt is 0, not in flap) => 3 | |T+| and
        ORB = |T+| / 3 = flap/6.
  * So ORB mod 2 = (|T+|/3) mod 2. The claim (-1)^ORB = chi2(2) is a statement about the parity
    of a lattice-point count in a triangle -- the Eisenstein/Gauss-lemma setting where chi2(2)
    arises as (-1)^(#lattice points in a triangle).

This file (a) VERIFIES the law out-of-sample, (b) verifies each reduction step exactly
(|T+|=|T-|, 3||T+|, ORB=|T+|/3), (c) checks the finer Eisenstein hook: is |T+| itself controlled
mod 6 by p mod 24? -- the data an actual proof must reproduce.
"""
import sys
from fractions import Fraction as Fr
from sympy import isprime
from _sigma_chi2_scan_v1 import chi2_table, build, sigma_fn

def analyze(p):
    chi2 = chi2_table(p)
    n = p + 1 + sum(chi2(((x * x % p) * x + 7) % p) for x in range(p))
    if not isprime(n): return None
    eis, eps, beta, R1, R2, DET = build(p)
    sig, orient = sigma_fn(p, eis, eps, R1, R2, DET)
    if sig is None: return {'p': p, 'FAIL': 'orient'}
    # split the flap by sigma sign, exactly
    Tplus = [x for x in range(p) if sig(x) == 1]
    Tminus = [x for x in range(p) if sig(x) == -1]
    flap = len(Tplus) + len(Tminus)
    # reduction-step checks
    negation_swaps = all(sig((p - x) % p) == -sig(x) for x in range(1, p))   # x->-x swaps T+/T-
    bp = beta % p
    mu3_fixes = all(sig(bp * x % p) == sig(x) for x in range(1, p))          # beta fixes sigma
    ORB = flap // 6
    chi2_2 = chi2(2 % p)
    law = ((-1) ** ORB == chi2_2)
    return {'p': p, 'n': n, 'flap': flap, 'ORB': ORB, 'Tp': len(Tplus), 'Tm': len(Tminus),
            'pmod8': p % 8, 'pmod24': p % 24, 'chi2_2': chi2_2, 'law': law,
            'neg_swaps': negation_swaps, 'mu3_fixes': mu3_fixes,
            'Tp_eq_Tm': len(Tplus) == len(Tminus), '3divTp': len(Tplus) % 3 == 0,
            'ORB_eq': ORB == len(Tplus) // 3, 'Tp_mod6': len(Tplus) % 6, 'orient': orient}

def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 2500
    label = sys.argv[3] if len(sys.argv) > 3 else ""
    rows = []
    for p in range(lo, hi):
        if p % 6 != 1 or not isprime(p) or p == 7: continue
        r = analyze(p)
        if r and 'FAIL' not in r: rows.append(r)
    print(f"# {label} p in [{lo},{hi}), p=1 mod6, n prime. kept={len(rows)}")
    # (a) the law
    law_ok = sum(1 for r in rows if r['law'])
    print(f"(a) LAW  (-1)^ORB == chi2(2):                 {law_ok}/{len(rows)}")
    # (b) reduction steps
    for key, desc in [('neg_swaps', 'x->-x swaps T+/T- (sigma odd)'),
                      ('mu3_fixes', 'beta fixes sigma (mu3 preserves T+)'),
                      ('Tp_eq_Tm', '|T+| == |T-|'),
                      ('3divTp', '3 | |T+|  (mu3 free on T+)'),
                      ('ORB_eq', 'ORB == |T+|/3')]:
        ok = sum(1 for r in rows if r[key])
        print(f"(b) {desc:<40}: {ok}/{len(rows)}")
    # (c) finer hook: |T+| mod 6 vs p mod 24
    print("(c) |T+| mod 6 by p mod 24 (what a proof must reproduce):")
    from collections import defaultdict
    d = defaultdict(list)
    for r in rows: d[r['pmod24']].append(r['Tp'] % 6)
    for res in sorted(d):
        vals = set(d[res])
        print(f"      p={res:>2} mod24: |T+|%6 in {sorted(vals)}   (ORB%2 -> {sorted(set((v//3)%2 for v in [x for x in d[res]]))})"
              if False else f"      p={res:>2} mod24: |T+|%6 in {sorted(vals)}")
    # violations if any
    bad = [r['p'] for r in rows if not r['law']]
    if bad: print("  LAW VIOLATIONS:", bad)

if __name__ == '__main__':
    main()
