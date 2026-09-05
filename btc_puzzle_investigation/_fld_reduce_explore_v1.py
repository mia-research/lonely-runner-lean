#!/usr/bin/env python3
"""
_fld_reduce_explore_v1.py -- reduce FLD toward h(-p). Exact ints/Fractions only.

Goals (all decidable, reported not asserted):
 (1) recompute FLD three ways and confirm: FLD = 2 sum_{T+} chi2 = 6 sum_{mu3-orbits in T+} chi2.
 (2) pin T+ arithmetically: t(X):=p*(u-v) is a DIFFERENCE of two sawtooths c_{s1}(X)-c_{s2}(X)
     with slopes s1,s2 tied to the reduced Eisenstein basis (the hexagonal directions). Report s1,s2
     and their relation to the prime pi_p = (reduced basis).
 (3) Dirichlet handle: D := sum_{a=1}^{(p-1)/2} chi2(a).  Classical: D = (2-chi2(2)) h(-p).
     Compare FLD/6 to h, and D to (2-chi2(2))h, and see how the triangle sum sits against D.
 (4) Jacobi handle: J(chi2,chi3)=sum_x chi2(x)chi3(1-x) in Z[omega]=A+B*omega, norm p. Report A,B
     and any relation of FLD to A,B split by p mod 24 (does an FLD-carrying component vanish at 7?).
"""
import sys
from fractions import Fraction as Fr
from sympy import isprime, primitive_root
from _sigma_chi2_scan_v1 import chi2_table, build, sigma_fn


def classnum_neg(p):
    D = -p; h = 0; a = 1
    while 3 * a * a <= p:
        for b in range(-a, a + 1):
            num = b * b - D
            if num % (4 * a):
                continue
            c = num // (4 * a)
            if c < a:
                continue
            if (abs(b) == a or a == c) and b < 0:
                continue
            h += 1
        a += 1
    return h


def csaw(r, p):
    """centered residue of r mod p in (-p/2, p/2]."""
    r %= p
    return r - p if r > p // 2 else r


def analyze(p):
    chi2 = chi2_table(p)
    eis, eps, beta, R1, R2, DET = build(p)
    sig, orient = sigma_fn(p, eis, eps, R1, R2, DET)
    if sig is None:
        return None

    def co(w):
        a, b = w
        return Fr(a * R2[1] - b * R2[0], DET), Fr(b * R1[0] - a * R1[1], DET)

    FLD = sum(sig(x) * chi2(x) for x in range(p))
    Tp = [x for x in range(1, p) if sig(x) == 1]
    twoTp = 2 * sum(chi2(x) for x in Tp)
    # mu3-orbit recompute: orbits under x->beta x; chi2 const on orbit; count orbit reps in T+
    bp = beta % p
    seen = set(); orb_sum = 0
    for x in range(1, p):
        if x in seen:
            continue
        orb = {x, bp * x % p, bp * bp * x % p}
        seen |= orb
        if sig(x) == 1:            # whole orbit in T+ (sigma mu3-invariant)
            orb_sum += chi2(x)
    sixOrb = 6 * orb_sum

    # (2) t(X)=p(u-v) as difference of two sawtooths; find slopes s1,s2 with u={s1 X/p}, v={s2 X/p}
    # u = X*R2[1]/p (mod 1, centered); v = -X*R1[1]/p (mod1). slopes:
    s1 = R2[1] % p
    s2 = (-R1[1]) % p
    # verify u(X) == centered(s1 X)/p and v(X)==centered(s2 X)/p for all X
    oku = all(co((eis(x)))[0] == Fr(csaw(s1 * x, p), p) for x in range(p))
    okv = all(co((eis(x)))[1] == Fr(csaw(s2 * x, p), p) for x in range(p))

    # (3) Dirichlet
    D = sum(chi2(a) for a in range(1, (p - 1) // 2 + 1))
    h = classnum_neg(p) if p % 4 == 3 else None
    chi2_2 = chi2(2)

    # (4) Jacobi J(chi2,chi3) in Z[omega]
    g = primitive_root(p)
    ind = [0] * p
    acc = 1
    for e in range(p - 1):
        ind[acc] = e; acc = acc * g % p
    def chi3pow(x):                # returns k in {0,1,2} with chi3(x)=omega^k, 0->None
        x %= p
        return None if x == 0 else ind[x] % 3
    c = [0, 0, 0]
    for x in range(p):
        if x == 1 or x == 0:
            continue
        k = chi3pow(1 - x)
        if k is None:
            continue
        c[k] += chi2(x)
    A = c[0] - c[2]; Bc = c[1] - c[2]         # J = A + B omega
    normJ = A * A - A * Bc + Bc * Bc

    return dict(p=p, m24=p % 24, FLD=FLD, twoTp=twoTp, sixOrb=sixOrb, h=h, D=D,
                chi2_2=chi2_2, s1=s1, s2=s2, oku=oku, okv=okv, A=A, B=Bc, normJ=normJ,
                Dcheck=(D == (2 - chi2_2) * h) if h else None)


def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 700
    print("# FLD reduction explore. FLD =? 2sumTp =? 6orbSum; slopes s1,s2; Dirichlet D=(2-chi2(2))h; Jacobi A,B.")
    print(f"# {'p':>4} {'m24':>3} {'FLD':>5} {'2Tp':>5} {'6orb':>5} {'h':>3} {'D':>4} {'(2-c2)h':>7} "
          f"{'Dok':>4} {'s1':>4} {'s2':>4} {'saw':>4} {'A':>4} {'B':>4} {'N(J)':>5}")
    for p in range(lo, hi):
        if p % 6 != 1 or not isprime(p) or p == 7:
            continue
        r = analyze(p)
        if r is None:
            continue
        saw = 'OK' if (r['oku'] and r['okv']) else 'no'
        d2 = (2 - r['chi2_2']) * r['h'] if r['h'] is not None else None
        print(f"  {r['p']:>4} {r['m24']:>3} {r['FLD']:>5} {r['twoTp']:>5} {r['sixOrb']:>5} "
              f"{str(r['h']):>3} {r['D']:>4} {str(d2):>7} {str(r['Dcheck']):>4} "
              f"{r['s1']:>4} {r['s2']:>4} {saw:>4} {r['A']:>4} {r['B']:>4} {r['normJ']:>5}")


if __name__ == "__main__":
    main()
