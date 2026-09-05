#!/usr/bin/env python3
"""
_fld_L1_fold_v1.py -- the a->2a summation fold applied to T+ (the step I skipped). Exact ints.

t(X)=p(u-v)=au(X)-bv(X), au=c(s1 X), bv=c(s2 X) centered residues. Doubling identity:
    c(2y) = 2 c(y) - p*e(y),   e(y) = +1 if c(y)>p/4, -1 if c(y)<-p/4, else 0.
So au(2X)=2 au(X) - p e1(X),  bv(2X)=2 bv(X) - p e2(X), and
    t(2X) = 2 t(X) - p*(e1(X)-e2(X)).
The e_i are QUARTER-interval (p/4) indicators -- the same objects F4=Sum_(p/4,p/2)chi2 counts.
VERIFY the identities, then look for the exact relation between S+=Sum_{T+}chi2 and F4.
"""
import sys
from fractions import Fraction as Fr
from sympy import isprime
from _sigma_chi2_scan_v1 import chi2_table, build, sigma_fn


def cen(y, p):
    y %= p
    return y - p if y > p // 2 else y


def e_of(c, p):
    if c > p // 4:
        return 1
    if c < -(p // 4):
        return -1
    return 0


def study(p):
    chi2 = chi2_table(p)
    eis, eps, beta, R1, R2, DET = build(p)
    sig, orient = sigma_fn(p, eis, eps, R1, R2, DET)
    if sig is None:
        return

    def co(w):
        a, b = w
        return Fr(a * R2[1] - b * R2[0], DET), Fr(b * R1[0] - a * R1[1], DET)

    sgn = -1 if orient == '-' else 1                 # flap coord s = u + sgn*v (orientation-correct)
    au = [0] * p; bv = [0] * p
    for X in range(p):
        u, v = co(eis(X)); au[X] = int(u * p); bv[X] = int(v * p)
    # slopes constant?
    s1 = {au[X] * pow(X, p - 2, p) % p for X in range(1, p)}
    s2 = {bv[X] * pow(X, p - 2, p) % p for X in range(1, p)}
    saw = (len(s1) == 1 and len(s2) == 1)
    # doubling identity for au, bv
    dbl_au = all(au[(2 * X) % p] == 2 * au[X] - p * e_of(au[X], p) for X in range(1, p))
    dbl_bv = all(bv[(2 * X) % p] == 2 * bv[X] - p * e_of(bv[X], p) for X in range(1, p))

    S = sum(sig(X) * chi2(X) for X in range(p))     # = FLD
    Sp = S // 2 if p % 4 == 3 else None              # Sum_{T+}chi2 (p=3 mod4)
    half = (p - 1) // 2
    F4 = sum(chi2(a) for a in range(p // 4 + 1, half + 1))

    # The fold: reindex Y=2X in S+ = Sum_X chi2(X) 1{t(X)>p/2}.
    #   Sum_X chi2(X) 1{t(2X)>p/2} = chi2(2) S+     (Y=2X bijection, chi2(2X)=chi2(2)chi2(X))
    # Compute LHS directly and confirm; then t(2X)>p/2 <=> 2 t(X) - p D(X) > p/2, D=e1-e2.
    if Sp is not None:
        t = [au[X] + sgn * bv[X] for X in range(p)]         # flap coord, orientation-correct
        D = [e_of(au[X], p) + sgn * e_of(bv[X], p) for X in range(p)]
        lhs = sum(chi2(X) for X in range(1, p) if (2 * t[X] - p * D[X]) > p // 2)
        tid = all(t[(2 * X) % p] == 2 * t[X] - p * D[X] for X in range(1, p))
        print(f"p={p:>4} m24={p%24} c2(2)={chi2(2):>2} saw={saw} dbl_au={dbl_au} dbl_bv={dbl_bv} "
              f"t(2X)id={tid} | S+={Sp:>4} F4={F4:>4} chi2(2)*S+={chi2(2)*Sp:>4} "
              f"fold_lhs={lhs:>4} lhs==c2*S+:{lhs==chi2(2)*Sp}")


def main():
    ps = [int(x) for x in sys.argv[1:]] or [103, 127, 151, 139, 163, 211, 283, 331]
    for p in ps:
        if isprime(p) and p % 6 == 1:
            study(p)


if __name__ == "__main__":
    main()
