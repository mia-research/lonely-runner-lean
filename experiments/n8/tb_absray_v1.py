r"""
tb_absray_v1 -- how big is the SHARPEST termwise bound on Tail_3?

The bound tested here is
        |Tail_3(e)|  <=  ABS(e) := SUM over primitive rays p in L(e) \ M of |Ray(p)| ,
        M = sat L_3(e),
with Ray(p) the EXACT closed form of tb_ray_v1 (the k-series already summed, so this
is strictly sharper than putting absolute values on individual frequencies).  This
script reports ABS truncated at ray height N -- a LOWER bound for ABS -- against the
1/12 budget.  If the truncation alone exceeds 1/12 then no termwise bound of this
shape can prove (H3u), and the obstruction is cancellation between rays.

Refined caps.  n.e = 0 with every e_rho odd forces SUM n_rho even, so the number of
odd coordinates of a resonance is even; and a primitive p cannot have every support
coordinate = 2 mod 4.  Restricting the residue maximisation to the patterns that
survive gives the caps used here.

usage: python3 tb_absray_v1.py [SMAX] [N] [MODE]
       MODE = "box"  exhaustive over primitive unit tuples with max e_rho <= SMAX
       MODE = "list" a fixed list of interesting tuples
"""
import sys, itertools
from fractions import Fraction as F
from math import gcd
from functools import reduce

import rt_limit_v2 as RL
from tb_ray_v1 import ray_value, primitive_rays
from ob_fast_v1 import o_fast

RHO = (1, 3, 5, 7)
BUDGET = F(1, 12)
FLOOR = F(3, 32)


def refined_caps():
    """max |Ray(p)| * PROD_{rho in supp}|p_rho| over residue patterns p mod 4 that a
    PRIMITIVE resonance of an all-odd speed tuple can actually have."""
    out = {}
    for s in (2, 3, 4):
        best, arg = F(0), None
        for T in itertools.combinations(range(4), s):
            for res in itertools.product((1, 2, 3), repeat=s):
                nodd = sum(1 for r in res if r % 2)
                if nodd % 2:
                    continue                       # SUM n_rho must be even
                if nodd == 0:
                    continue                       # then p is not primitive
                p = [0, 0, 0, 0]
                for t, r in zip(T, res):
                    p[t] = r
                v = abs(ray_value(tuple(p)))
                prod = 1
                for t in T:
                    prod *= p[t]
                if v * prod > best:
                    best, arg = v * prod, tuple(p)
        out[s] = (best, arg)
    return out


def low_res(e, R):
    out = []
    for n3 in range(-R, R + 1):
        for n5 in range(-R, R + 1):
            for n7 in range(-R, R + 1):
                s = n3 * e[1] + n5 * e[2] + n7 * e[3]
                if s % e[0]:
                    continue
                n1 = -s // e[0]
                if abs(n1) > R or (n1 == n3 == n5 == n7 == 0):
                    continue
                out.append((n1, n3, n5, n7))
    return out


def in_lattice(rows, v):
    """is v in the lattice spanned by the (HNF) integer rows?  Rows are echelon."""
    v = list(v)
    for r in rows:
        j = next(i for i in range(4) if r[i])
        if v[j] % r[j]:
            return False
        q = v[j] // r[j]
        for i in range(4):
            v[i] -= q * r[i]
    return not any(v)


def m3_of(e):
    res = low_res(e, 3)
    if not res:
        return [], 0, FLOOR
    M = [list(v) for v in res]
    k, rk = RL.lattice_key(M)
    if rk >= 3:
        return None, rk, None
    rows = [list(r) for r in k]
    lim = RL.rank1_limit(tuple(rows[0])) if rk == 1 else RL.rank2_limit(rows)
    return rows, rk, lim


def abs_tail(e, N, rows):
    tot = F(0)
    per = {2: F(0), 3: F(0), 4: F(0)}
    for p in primitive_rays(e, N):
        if rows and in_lattice(rows, p):
            continue
        v = abs(ray_value(p))
        tot += v
        per[sum(1 for x in p if x)] += v
    return tot, per


def gen(smax):
    Qs = [range((smax - r) // 8 + 1) for r in RHO]
    for qs in itertools.product(*Qs):
        e = tuple(8 * q + r for q, r in zip(qs, RHO))
        if len(set(e)) == 4 and reduce(gcd, e) == 1:
            yield e


if __name__ == "__main__":
    SMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    MODE = sys.argv[3] if len(sys.argv) > 3 else "box"

    caps = refined_caps()
    print("refined ray caps  (max |Ray(p)| * PROD|p_rho| over realisable p mod 4):")
    for s in (2, 3, 4):
        c, a = caps[s]
        print(f"   s = {s}:  cap = {c} = {float(c):.7f}   attained at p mod 4 = {a}")
    print(f"\nbudget 1/12 = {float(BUDGET):.7f};  ABS truncated at ray height {N}\n")

    tuples = list(gen(SMAX)) if MODE == "box" else [
        (1, 3, 5, 7), (1, 11, 5, 7), (17, 3, 5, 7), (9, 3, 5, 7),
        (25, 11, 77, 7), (41, 43, 13, 15), (1, 19, 5, 7), (241, 163, 205, 199)]
    print(f"population: {'speed box max e_rho <= %d' % SMAX if MODE=='box' else 'fixed list'},"
          f" primitive only, {len(tuples)} tuples, "
          f"true max speed {max(max(t) for t in tuples)}")

    recs = []
    for e in tuples:
        rows, rk, lim = m3_of(e)
        if rows is None:
            continue                                # rank-3 finite arm
        o = o_fast(e)
        tail = o - lim
        a, per = abs_tail(e, N, rows)
        recs.append((a, tail, rk, lim, o, per, e))
    recs.sort(reverse=True)
    print(f"tuples in the rank<=2 arm: {len(recs)}")
    print(f"\n   {'e':>22} rk {'o_inf':>8} {'Tail_3':>10} {'ABS_trunc':>10} "
          f"{'s=2':>9} {'s=3':>9} {'s=4':>9}")
    for a, tail, rk, lim, o, per, e in recs[:25]:
        print(f"   {str(e):>22} {rk:>2} {str(lim):>8} {float(tail):>10.6f} "
              f"{float(a):>10.6f} {float(per[2]):>9.6f} {float(per[3]):>9.6f} "
              f"{float(per[4]):>9.6f}"
              f"{'   ABS > 1/12' if a > BUDGET else ''}")
    over = sum(1 for r in recs if r[0] > BUDGET)
    print(f"\n   tuples whose TRUNCATED ABS already exceeds 1/12: {over} / {len(recs)}")
    print(f"   max Tail_3 in this population: {float(max(r[1] for r in recs)):.7f}")
    print(f"   max ABS_trunc:                 {float(max(r[0] for r in recs)):.7f}")
