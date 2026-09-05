#!/usr/bin/env python3
"""
_fld_L1_explore_v1.py -- crack L1: |Sum_{T+} chi2| = F4 = Sum_{(p/4,p/2)} chi2. Exact ints/Fr.

Approach: characterize T+ arithmetically.
 t(X) := p*(u(X)-v(X)) is an integer in (-p,p), and t(X) = c(a X) - c(b X) (diff of two centered
 residues) so t(X) == M*X mod p with M = a+b... but lives in (-p,p).  We:
  (1) find M with t(X) ≡ M X (mod p) for all X (constant?),
  (2) look at T+ = {t>p/2} in the coordinate y=M X mod p in [0,p): is it a union of intervals?
  (3) at p=7 mod8 test an involution on T+ flipping chi2 (mult by 2, by sqrt2, by -1 within T+),
  (4) at p=19 mod24 test T+ (or its M-image) == a quarter-interval up to a multiplier c (chi2(c)=+-1).
"""
import sys
from fractions import Fraction as Fr
from sympy import isprime
from _sigma_chi2_scan_v1 import chi2_table, build, sigma_fn


def sqrt_mod(a, p):
    a %= p
    if pow(a, (p - 1) // 2, p) != 1:
        return None
    if p % 4 == 3:
        return pow(a, (p + 1) // 4, p)
    return None


def study(p):
    chi2 = chi2_table(p)
    eis, eps, beta, R1, R2, DET = build(p)
    sig, orient = sigma_fn(p, eis, eps, R1, R2, DET)
    if sig is None:
        return

    def co(w):
        a, b = w
        return Fr(a * R2[1] - b * R2[0], DET), Fr(b * R1[0] - a * R1[1], DET)

    t = [0] * p
    for X in range(p):
        u, v = co(eis(X))
        t[X] = int((u - v) * p)                       # integer in (-p, p)
    Tp = [X for X in range(1, p) if sig(X) == 1]      # t(X) > p/2
    # (1) M with t(X) ≡ M X mod p
    Ms = set((t[X] * pow(X, p - 2, p)) % p for X in range(1, p))
    M = Ms.pop() if len(Ms) == 1 else None
    print(f"\np={p} m24={p%24} chi2(2)={chi2(2)} |T+|={len(Tp)}  M(t≡MX)={'const='+str(M) if M is not None else 'NOT constant ('+str(len(Ms)+1)+' vals)'}")

    # (2) y = M X mod p in [0,p); is T+ an interval / union in y?
    if M is not None:
        ys = sorted((M * X) % p for X in Tp)
        # find contiguous runs
        runs = []
        s = ys[0]; prev = ys[0]
        for y in ys[1:]:
            if y == prev + 1:
                prev = y
            else:
                runs.append((s, prev)); s = y; prev = y
        runs.append((s, prev))
        print(f"   T+ in y=MX: {len(runs)} runs; e.g. {runs[:4]}{'...' if len(runs)>4 else ''}"
              f"  (interval endpoints ~ p/4={p//4}, p/2={p//2}, 3p/4={3*p//4})")

    # (3) p=7 mod8: hunt an involution on T+ flipping chi2 (mult by c mapping T+ -> T+)
    r2 = sqrt_mod(2, p)
    if p % 8 == 7:
        Tset = set(Tp)
        found = []
        cand = [2, pow(2, p - 2, p)]
        if r2:
            cand += [r2, pow(r2, p - 2, p), (p - r2) % p]
        for c in cand:
            img = set((c * X) % p for X in Tp)
            if img == Tset:
                found.append((c, chi2(c), 'PRESERVES T+'))
        # also: any c at all with c*T+ == T+ and chi2(c)=-1 ?
        allc = [c for c in range(2, p) if set((c * X) % p for X in Tp) == Tset]
        neg = [c for c in allc if chi2(c) == -1]
        print(f"   [p=7mod8] sqrt2={r2}. c preserving T+ (stab): {allc}  of which chi2(c)=-1: {neg}")

    # (4) p=19 mod24: is T+ (in some multiplier image) a quarter interval?
    if p % 24 == 19 and M is not None:
        half = (p - 1) // 2
        F4set = set(range(p // 4 + 1, half + 1))
        # try to match c*T+ to F4set or its negation/scaling
        for c in range(1, p):
            img = set((c * X) % p for X in Tp)
            if img == F4set:
                print(f"   [p=19] c={c} maps T+ EXACTLY onto (p/4,p/2)!  chi2(c)={chi2(c)}")
                break


def main():
    ps = [int(x) for x in sys.argv[1:]] or [103, 127, 139, 163, 211]
    for p in ps:
        if isprime(p) and p % 6 == 1:
            study(p)


if __name__ == "__main__":
    main()
