#!/usr/bin/env python3
"""
_field_bigrading_v1.py -- THE FIELD-LEVEL SELECTION RULE (the symmetry behind the conservations).

Follows the conservations found by isotypic_selection_rule_v1 / _sigma_chi2_scan_v1 to the
symmetry that enforces them. Exact ints only.

THE CLAIM (Claim F). p = 1 mod 6, so F_p^* contains mu6 = <beta,-1> (beta^3=1). This acts on
F_p BY MULTIPLICATION. Give each x-readout a FIELD BIDEGREE (i,k) in Z/2 x Z/3:

    F(-x)    = (-1)^i F(x)        i = FIELD PARITY   (x -> -x)
    F(beta x)= omega^k F(x)       k = mu3 weight

Then, because x -> zeta*x is a bijection of F_p for zeta in mu6:

  (F1)  FIELD part:  sum_{x in F_p} F(x) conj(G(x))                = 0  unless (i,k)_F = (i,k)_G
  (F2)  CURVE part:  sum_{x in F_p} F(x) conj(G(x)) chi2(x^3+7)    = 0  unless      k_F = k_G

The asymmetry between (F1) and (F2) is the whole point:
  - beta*x  :  (beta x)^3 + 7 = x^3 + 7          => weight INVARIANT => mu3 survives on the curve
  - -x      :  (-x)^3   + 7 = -(x^3 - 7)         => the SEXTIC TWIST y^2 = x^3 - 7
So field negation is NOT induced by any curve automorphism; it exchanges E with its twist, and
the Z/2 half of the field rule is BROKEN on the curve part. Aut(E)=mu6 reaches x only through
mu3 (since [-1] moves y, not x). Hence:

    FIELD part: 6 sectors.   CURVE part: 3 sectors.   The missing Z/2 IS the twist.

CONSEQUENCES, both previously recorded as separate facts, now one rule:
  * B1 = sum_x sigma(x) = 0            : sigma is (1,0), the constant 1 is (0,0) => mismatch.
  * <sigma,chi2>_FIELD = 0 iff p=1 mod 4 : chi2 has field parity i = ((p-1)/2) mod 2.
        p=1 mod 4 => chi2 is (0,0), sigma is (1,0) => mismatch => EXACT 0.
        p=3 mod 4 => chi2 is (1,0)  = sigma's bidegree => NOT forced.
  * C = <sigma,1>_CURVE != 0 generally : the curve part has only the mu3 rule, and sigma and 1
        share k=0, so nothing forces it. C is a Weil-scale character sum.

FALSIFICATION of Claim F: any pair with exactly-verified DIFFERENT field bidegrees whose FIELD
sum is nonzero; or different mu3 weights whose CURVE sum is nonzero.
"""
import sys
from fractions import Fraction as Fr
from sympy import isprime, primitive_root
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv, enorm, sextant
from _sigma_chi2_scan_v1 import chi2_table, build, sigma_fn

OM = [(1, 0), (0, 1), (-1, -1)]
ZETA6 = (1, 1)
Z0, Z1 = (0, 0), (1, 0)
def zmul(z, w):
    a, b = z; c, d = w
    return (a * c - b * d, a * d + b * c - b * d)
def zconj(z): a, b = z; return (a - b, -b)
def zadd(z, w): return (z[0] + w[0], z[1] + w[1])
def zscale(z, k): return (z[0] * k, z[1] * k)
def zeta6_pow(e):
    z = Z1
    for _ in range(e % 6): z = zmul(z, ZETA6)
    return z

def readouts_x(p, eis, eps, beta, sig):
    """x-readouts only. Every value an exact Z[omega] element."""
    chi2 = chi2_table(p)
    g = primitive_root(p)
    ind = [0] * p
    a = 1
    for i in range(p - 1):
        ind[a] = i; a = a * g % p
    def one(x):   return Z1
    def c2(x):    return (chi2(x), 0)
    def c3(x):    return Z0 if x % p == 0 else OM[ind[x % p] % 3]
    def c6(x):    return Z0 if x % p == 0 else zeta6_pow(ind[x % p] % 6)
    def eisx(x):  return eis(x)
    def nrm(x):   return (enorm(eis(x)), 0)
    def sxt(x):   u, v = eis(x); return zeta6_pow(sextant(u, v))
    def epsr(x):  return (eps(x), 0)
    def sgm(x):   return (sig(x), 0)
    def xid(x):   return (x, 0)
    return [('one', one), ('x', xid), ('chi2', c2), ('chi3', c3), ('chi6', c6),
            ('eis', eisx), ('nrm', nrm), ('sxt_z6', sxt), ('eps', epsr), ('sigma', sgm)]

def field_bidegree(p, name, F, beta):
    """Exact defect count over ALL x in F_p for each (i,k). Returns the unique (i,k) with
    defect 0, or None (ungraded -> report, do not call it 'structureless')."""
    D = {}
    for i in (0, 1):
        for k in (0, 1, 2):
            d = 0
            for x in range(p):
                f0 = F(x)
                if F((-x) % p) != zscale(f0, (-1) ** i): d += 1; continue
                if F(beta * x % p) != zmul(OM[k], f0): d += 1
            D[(i, k)] = d
    hits = [jk for jk, d in D.items() if d == 0]
    return (hits[0] if len(hits) == 1 else None), D

def run(p):
    chi2 = chi2_table(p)
    n = p + 1 + sum(chi2(((x * x % p) * x + 7) % p) for x in range(p))
    if not isprime(n): return None
    eis, eps, beta, R1, R2, DET = build(p)
    sig, orient = sigma_fn(p, eis, eps, R1, R2, DET)
    if sig is None: return {'p': p, 'FAIL': 'orientation'}
    R = readouts_x(p, eis, eps, beta, sig)
    bd = {}; DD = {}
    for nm, F in R:
        bd[nm], DD[nm] = field_bidegree(p, nm, F, beta)
    w = [chi2(((x * x % p) * x + 7) % p) for x in range(p)]
    vals = {nm: [F(x) for x in range(p)] for nm, F in R}
    FLD = {}; CRV = {}
    for a, _ in R:
        for b, _ in R:
            f = Z0; c = Z0
            va, vb = vals[a], vals[b]
            for t in range(p):
                z = zmul(va[t], zconj(vb[t]))
                f = zadd(f, z); c = zadd(c, zscale(z, w[t]))
            FLD[(a, b)] = f; CRV[(a, b)] = c
    return {'p': p, 'n': n, 'pmod4': p % 4, 'pmod36': p % 36, 'orient': orient,
            'bd': bd, 'D': DD, 'FLD': FLD, 'CRV': CRV, 'names': [nm for nm, _ in R],
            'beta': beta}

def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 1200
    tot_f = bad_f = tot_c = bad_c = 0
    tot_fnf = zero_fnf = tot_cnf = zero_cnf = 0
    print(f"# Claim F test, p in [{lo},{hi}), p=1 mod 6, n prime")
    print(f"# {'p':>5} {'m4':>3} {'chi2 bd':>9} {'sigma bd':>9} {'eps bd':>7} {'eis bd':>7} "
          f"{'Fviol':>6} {'Cviol':>6}")
    for p in range(lo, hi):
        if p % 6 != 1 or not isprime(p) or p == 7: continue
        r = run(p)
        if r is None: continue
        if 'FAIL' in r: print(f"  {p:>5}  FAIL {r['FAIL']}"); continue
        bd, nm = r['bd'], r['names']
        vf = vc = 0
        for a in nm:
            for b in nm:
                if bd[a] is None or bd[b] is None: continue
                # (F1) FIELD rule: full field bidegree must match
                if bd[a] != bd[b]:
                    tot_f += 1
                    if r['FLD'][(a, b)] != Z0: vf += 1; bad_f += 1
                else:
                    tot_fnf += 1
                    if r['FLD'][(a, b)] == Z0: zero_fnf += 1
                # (F2) CURVE rule: only the mu3 weight must match
                if bd[a][1] != bd[b][1]:
                    tot_c += 1
                    if r['CRV'][(a, b)] != Z0: vc += 1; bad_c += 1
                else:
                    tot_cnf += 1
                    if r['CRV'][(a, b)] == Z0: zero_cnf += 1
        print(f"  {p:>5} {r['pmod4']:>3} {str(bd['chi2']):>9} {str(bd['sigma']):>9} "
              f"{str(bd['eps']):>7} {str(bd['eis']):>7} {vf:>6} {vc:>6}")
    print()
    print(f"(F1) FIELD rule : {tot_f} mismatched-bidegree pairs, {bad_f} VIOLATIONS")
    print(f"(F2) CURVE rule : {tot_c} mismatched-mu3-weight pairs, {bad_c} VIOLATIONS")
    print()
    print(f"non-forced FIELD pairs: {tot_fnf}, of which exactly zero anyway: {zero_fnf}")
    print(f"non-forced CURVE pairs: {tot_cnf}, of which exactly zero anyway: {zero_cnf}")
    print("  (a non-forced exact zero = a conservation Claim F does NOT explain = next probe)")

if __name__ == '__main__':
    main()
