r"""
tb_deep_v1 -- exact Tail_3 on DEEP members of a prescribed resonance class.

Given a saturated rank-<=2 lattice M' (two generating vectors on the command line),
enumerate the primitive unit 4-tuples e in its kernel, ordered by max speed, and for
each compute EXACTLY

    M   = sat L_3(e)  (rank <= 2 required),   o_inf(M),   o(e),   Tail_3 = o - o_inf(M)

and compare with 1/12.  This is the arm that turns a class-level Delta into an
explicit witness.

All arithmetic exact (Fraction / int).  o comes from ob_fast_v1.o_fast and is
re-verified against ob_core_v1.o_x with a boundary audit on the reported extremes.

POPULATION LABEL: this is a PARAMETER box in alpha (|alpha_i| <= PMAX) intersected
with a speed cap; the true maximum speed reached is printed.

usage:  python3 tb_deep_v1.py "1,-1,0,-2" "0,1,-1,-2" [PMAX] [SPEEDCAP]
        python3 tb_deep_v1.py "1,-1,0,-2" -          [PMAX] [SPEEDCAP]   (rank 1)
"""
import sys, itertools
from fractions import Fraction as F
from math import gcd, lcm
from functools import reduce

import rt_limit_v2 as RL
from ob_fast_v1 import o_fast, audit
from ob_core_v1 import o_x

RHO = (1, 3, 5, 7)
BUDGET = F(1, 12)
FLOOR = F(3, 32)


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


def m3_of(e):
    res = low_res(e, 3)
    if not res:
        return (), 0, FLOOR
    k, rk = RL.lattice_key([list(v) for v in res])
    if rk >= 3:
        return None, rk, None
    rows = [list(r) for r in k]
    lim = RL.rank1_limit(tuple(rows[0])) if rk == 1 else RL.rank2_limit(rows)
    return k, rk, lim


def guard(e):
    D = 4 * reduce(lcm, e)
    return max(4 * x for x in e) * D < 2 ** 62


if __name__ == "__main__":
    gens = [[int(x) for x in sys.argv[1].split(",")]]
    if sys.argv[2] != "-":
        gens.append([int(x) for x in sys.argv[2].split(",")])
    PMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 200
    CAP = int(sys.argv[4]) if len(sys.argv) > 4 else 4000

    key, rk = RL.lattice_key(gens)
    rows = [list(r) for r in key]
    lim_class = (RL.rank1_limit(tuple(rows[0])) if rk == 1
                 else RL.rank2_limit(rows) if rk == 2 else FLOOR)
    print(f"class M' (saturated, rank {rk}): {key}")
    print(f"   o_inf(M') = {lim_class} = {float(lim_class):.7f}")

    B, krk = RL.kernel_basis(gens)
    r = len(B[0])
    print(f"   kernel basis columns ({r}-dimensional):")
    for i in range(4):
        print(f"      {B[i]}")

    found = []
    rngs = [range(-PMAX, PMAX + 1)] * r
    for al in itertools.product(*rngs):
        e = tuple(sum(B[i][c] * al[c] for c in range(r)) for i in range(4))
        if any(x <= 0 for x in e) or max(e) > CAP:
            continue
        if any(x % 8 != RHO[i] % 8 for i, x in enumerate(e)):
            continue
        if len(set(e)) != 4 or reduce(gcd, e) != 1:
            continue
        found.append(e)
    found = sorted(set(found), key=lambda e: max(e))
    print(f"   witnesses in the alpha box |alpha| <= {PMAX} with max speed <= {CAP}:"
          f" {len(found)}   true max speed reached {max(max(e) for e in found) if found else '-'}")

    recs = []
    for e in found:
        if not guard(e):
            continue
        k3, rk3, l3 = m3_of(e)
        if k3 is None:
            continue                                  # rank-3 finite arm
        o = o_fast(e)
        recs.append((o - l3, o, l3, rk3, k3, e))
    recs.sort(reverse=True)
    print(f"   of these, in the rank L_3 <= 2 arm: {len(recs)}")
    if not recs:
        sys.exit()
    print(f"\n   {'e':>26} {'maxsp':>6} rk3 {'o':>12} {'o_inf(L3)':>10} "
          f"{'Tail_3':>11}   verdict")
    for t, o, l3, rk3, k3, e in recs[:20]:
        v = "VIOLATES (H3u)" if t > BUDGET else ""
        print(f"   {str(e):>26} {max(e):>6} {rk3:>3} {float(o):>12.7f} "
              f"{str(l3):>10} {float(t):>11.7f}   {v}")
    mx = recs[0]
    print(f"\n   MAX Tail_3 = {mx[0]} = {float(mx[0]):.8f} at {mx[5]}"
          f"   (budget 1/12 = {float(BUDGET):.8f})")
    print(f"   violations of Tail_3 <= 1/12 in this enumeration: "
          f"{sum(1 for r in recs if r[0] > BUDGET)}")
    e = mx[5]
    print(f"\n   independent re-verification at the argmax {e}:")
    print(f"      ob_fast_v1.o_fast = {mx[1]}")
    print(f"      ob_core_v1.o_x    = {o_x(e)}   equal: {o_x(e) == mx[1]}")
    print(f"      boundary audit (cells, interior breakpoints, entry!=exit) = {audit(e)}")
