#!/usr/bin/env python3
"""
_fld_involution_hunt_v1.py -- reduce FLD = sum_x sigma(x)chi2(x) and hunt the involution that
forces FLD=0 at p=7 mod 8.  Exact ints only.

DERIVED IDENTITY (to verify): for p=3 mod 4, x->-x swaps T+ <-> T- and chi2(-x)=-chi2(x), so
    FLD = 2 * sum_{x in T+} chi2(x)  =  2 * (#QR in T+  -  #NQR in T+).
FLD=0 at p=7 mod 8 then means T+ carries equal QR/NQR.  sigma*chi2 is mu6-invariant (p=3 mod4),
so FLD = 6 * (imbalance over mu6-orbits).  A chi2-flipping, sigma*chi2-flipping involution that
exists iff chi2(2)=+1 (iff sqrt2 in F_p) would force the balance.  HUNT it (rule 13): test map
families x->c*x^{-1}, x->c-x, x->c*x, x->(x+a)/(x+b) restricted, and sqrt2-scalings.
"""
import sys
from sympy import isprime
from _sigma_chi2_scan_v1 import chi2_table, build, sigma_fn


def objects(p):
    chi2 = chi2_table(p)
    n = p + 1 + sum(chi2(((x * x % p) * x + 7) % p) for x in range(p))
    if not isprime(n):
        return None
    eis, eps, beta, R1, R2, DET = build(p)
    sig, orient = sigma_fn(p, eis, eps, R1, R2, DET)
    if sig is None:
        return None
    return chi2, sig


def sqrt_mod(a, p):
    a %= p
    if a == 0:
        return 0
    if pow(a, (p - 1) // 2, p) != 1:
        return None
    if p % 4 == 3:
        return pow(a, (p + 1) // 4, p)
    # Tonelli for p=1 mod4 (not needed for p=3 mod4 curves, kept for completeness)
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2; s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t % p
        while t2 != 1:
            t2 = t2 * t2 % p; i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, b * b % p, t * b * b % p, r * b % p
    return r


def explore(p):
    o = objects(p)
    if not o:
        return
    chi2, sig = o
    sc = [sig(x) * chi2(x) for x in range(p)]
    Tplus = [x for x in range(1, p) if sig(x) == 1]
    FLD = sum(sc)
    twoTp = 2 * sum(chi2(x) for x in Tplus)
    r2 = sqrt_mod(2, p)
    tag = f"p={p:>4} m8={p%8} sqrt2={'yes' if r2 is not None else 'no ':>3}"
    print(f"{tag}  FLD={FLD:>4}  2*sum_Tp chi2={twoTp:>4}  identity={'OK' if FLD==twoTp else 'FAIL'}"
          f"  |T+|={len(Tplus)}")

    def flips(mapfn):
        try:
            return all(sc[mapfn(x)] == -sc[x] for x in range(1, p) if sc[x] != 0)
        except Exception:
            return False

    hits = []
    # 1) multiplicative x->c x  (expect none, per reflection/mult kills)
    for c in range(2, p):
        if flips(lambda x, c=c: (c * x) % p):
            hits.append(("mult", c, chi2(c)))
    # 2) inversive x->c x^{-1}
    for c in range(1, p):
        if flips(lambda x, c=c: (c * pow(x, p - 2, p)) % p):
            hits.append(("inv", c, chi2(c)))
    # 3) additive x->c-x
    for c in range(p):
        if flips(lambda x, c=c: (c - x) % p):
            hits.append(("sub", c, None))
    # report a compact summary of hit families
    fam = {}
    for kind, c, ch in hits:
        fam.setdefault(kind, []).append((c, ch))
    for kind in ("mult", "inv", "sub"):
        lst = fam.get(kind, [])
        if lst:
            # show chi2(c) pattern for the flipping constants
            chis = sorted(set(ch for _, ch in lst if ch is not None))
            print(f"       FLIP family '{kind}': {len(lst)} constants   chi2(c) in {chis}"
                  f"   e.g. c={lst[0][0]}")
        else:
            print(f"       FLIP family '{kind}': none")


def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 1000
    print("# FLD involution hunt. Identity FLD == 2 sum_{T+} chi2, and which map families flip sigma*chi2.")
    print("# contrast p=3 mod8 (FLD!=0, no sqrt2) vs p=7 mod8 (FLD=0, sqrt2 exists).")
    for p in range(lo, hi):
        if p % 6 != 1 or not isprime(p) or p == 7:
            continue
        if p % 4 != 3:
            continue          # FLD forced 0 at p=1 mod4; focus on the p=3 mod4 split (3 vs 7 mod8)
        explore(p)


if __name__ == "__main__":
    main()
