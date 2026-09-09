r"""
rt_tail_v1 -- MEASURING the object that the missing rate bound must control.

Theorem 4 (see reports/n8_o_rate.md) splits every primitive unit 4-tuple by the rank of
    L_R(e) = < n in Z^4 : n.e = 0, ||n||_inf <= R >.
 * rank L_R = 3  =>  max e_rho <= 3 sqrt(3) R^3   (a FINITE set, checkable)
 * rank L_R <= 2 =>  o(e) = o_inf(L_R^sat) + Tail_R(e),
   with o_inf computed exactly by rt_limit_v2 and Tail_R the sum of the character
   expansion over resonances OUTSIDE L_R^sat -- all of which have height > R.

The pair part of Tail_R is PROVED to be at most (9/16)/R (Theorem 3).  The |supp| = 3
and |supp| = 4 parts are the open piece.  This script measures the whole tail exactly.

For each tuple: find lam_1 <= lam_2 <= lam_3, the successive sup-norm minima of L(e);
take R = lam_3 - 1, the largest R with rank L_R <= 2; compute o_inf(L_R^sat) exactly and
report  Tail = o - o_inf  against R.  Every number is an exact Fraction.

usage:  python3 rt_tail_v1.py [NSAMPLE] [SMAX] [SEED]
"""
import sys, itertools, random
from fractions import Fraction as F
from math import gcd
from functools import reduce

import rt_limit_v2 as RL
from ob_fast_v1 import o_fast

RHO = (1, 3, 5, 7)
NS = int(sys.argv[1]) if len(sys.argv) > 1 else 300
SMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 400
SEED = int(sys.argv[3]) if len(sys.argv) > 3 else 11


def resonances(e, H):
    """every n with n.e = 0 and ||n||_inf <= H (n_1 solved from the other three)."""
    out = []
    for n3 in range(-H, H + 1):
        for n5 in range(-H, H + 1):
            for n7 in range(-H, H + 1):
                s = n3 * e[1] + n5 * e[2] + n7 * e[3]
                if s % e[0]:
                    continue
                n1 = -s // e[0]
                if abs(n1) > H:
                    continue
                if n1 == n3 == n5 == n7 == 0:
                    continue
                out.append((n1, n3, n5, n7))
    return out


def rank_of(vs):
    if not vs:
        return 0
    M = [list(v) for v in vs]
    B, rk = RL.kernel_basis(M)
    return rk


def minima(e, HMAX=64):
    """the three successive sup-norm minima of L(e), by increasing H."""
    lam = []
    cur = []
    H = 0
    while len(lam) < 3 and H < HMAX:
        H += 1
        new = resonances(e, H)
        r = rank_of(new)
        while len(lam) < r:
            lam.append(H)
        cur = new
    return lam, cur


def limit_of(M):
    rk = rank_of(M) if M else 0
    if rk == 0:
        return F(24, 256), 0
    if rk == 1:
        B, _ = RL.kernel_basis([list(m) for m in M])
        # a generator of the saturated rank-1 lattice
        Bt = [[B[r][c] for r in range(4)] for c in range(len(B[0]))]
        Lb, _ = RL.kernel_basis(Bt)
        n0 = tuple(Lb[r][0] for r in range(4))
        return RL.rank1_limit(n0), 1
    if rk == 2:
        B, _ = RL.kernel_basis([list(m) for m in M])
        Bt = [[B[r][c] for r in range(4)] for c in range(len(B[0]))]
        Lb, _ = RL.kernel_basis(Bt)
        rows = [[Lb[r][c] for r in range(4)] for c in range(len(Lb[0]))]
        return RL.rank2_limit(rows), 2
    return None, 3


if __name__ == "__main__":
    rng = random.Random(SEED)
    print(f"rt_tail_v1  NSAMPLE={NS}  SMAX={SMAX}  seed={SEED}")
    print("R = lam_3 - 1 is the LARGEST height with rank L_R <= 2.")
    print("Tail = o - o_inf(L_R^sat).  Proved pair part of the bound: 9/(16 R).\n")
    print(f"{'e':>26} {'rank':>4} {'lam':>12} {'R':>4} {'o':>10} {'o_inf':>10} "
          f"{'|Tail|':>10} {'|Tail|*R':>9} {'9/(16R)':>8}")
    rows = []
    seen = set()
    tries = 0
    while len(rows) < NS and tries < 60 * NS:
        tries += 1
        e = tuple(8 * rng.randrange(0, SMAX // 8 + 1) + r for r in RHO)
        if len(set(e)) != 4 or reduce(gcd, e) != 1 or e in seen:
            continue
        seen.add(e)
        lam, _ = minima(e, HMAX=40)
        if len(lam) < 3:
            continue
        R = lam[2] - 1
        if R < 1:
            continue
        M = resonances(e, R)
        lim, rk = limit_of(M)
        if lim is None:
            continue
        o = o_fast(e)
        tail = o - lim
        rows.append((e, rk, tuple(lam), R, o, lim, tail))
    rows.sort(key=lambda t: -abs(t[6]) * t[3])
    for e, rk, lam, R, o, lim, tail in rows[:30]:
        print(f"{str(e):>26} {rk:>4} {str(lam):>12} {R:>4} {float(o):>10.6f} "
              f"{float(lim):>10.6f} {float(abs(tail)):>10.6f} "
              f"{float(abs(tail)*R):>9.4f} {float(F(9,16)/R):>8.4f}")
    if rows:
        worst = max(abs(t[6]) * t[3] for t in rows)
        print(f"\nsampled {len(rows)} tuples with rank L_R <= 2")
        print(f"  max over the sample of  |Tail| * R  =  {float(worst):.4f}")
        print(f"  (a bound |Tail| <= C/R with C = {float(worst):.4f} would hold on this "
              f"sample; C <= 1/12 * R is what (H'') needs at each R)")
        byR = {}
        for e, rk, lam, R, o, lim, tail in rows:
            byR.setdefault(R, []).append(abs(tail))
        print(f"\n  {'R':>4} {'n':>5} {'max|Tail|':>12} {'max|Tail|*R':>12}")
        for R in sorted(byR):
            v = byR[R]
            print(f"  {R:>4} {len(v):>5} {float(max(v)):>12.6f} {float(max(v)*R):>12.4f}")
