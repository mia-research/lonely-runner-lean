r"""
tb_caps_v1 -- the ray caps, and two unconditional theorems that follow from them.

Setting (tb_ray_v1).  For a primitive p in Z^4 with support T, s = |T|,

    Ray(p) := SUM_{k != 0} Ghat(k p)  =  c(p mod 4, s) / PROD_{rho in T} p_rho

with the numerator depending ONLY on p mod 4.  So, writing PI(p) = PROD_{T} |p_rho|,

    |Ray(p)| = C(p mod 4) / PI(p) <= cap(s) / PI(p),
    cap(2) = 3/32,  cap(3) = 1/16,  cap(4) = 5/32,   and cap(s) <= 5/32 always.

ADMISSIBILITY.  A resonance p of a primitive unit 4-tuple e (e_rho = rho mod 8,
e_rho > 0) satisfies: p != 0, gcd = 1, SUM p_rho rho = 0 mod 8, |supp p| >= 2, and p
has both a positive and a negative coordinate.  (rt_limit_v2.admissible.)

TWO CONSEQUENCES, both unconditional in the height:

  THEOREM R1.  For every admissible primitive n0,
        |o_inf(<n0>) - 3/32| = |Ray(n0)| <= 7/96,
  so every rank-1 class limit lies in [3/32 - 7/96, 3/32 + 7/96] = [1/48, 1/6].
  The upper end 1/6 is attained, and only by the two +-1 relations.
  PROOF.  If ht(n0) >= 3 then PI(n0) >= 3, so |Ray| <= (5/32)/3 = 5/96 < 7/96.  The
  remaining vectors have ht <= 2: a finite list, checked exhaustively below. QED

  THEOREM A (the rank-1 increment).  If ht(n0) >= 4 then |Ray(n0)| <= 1/32.
  PROOF.  A coordinate = 0 mod 4 forces Ray = 0 (A(m) = 0 there), so either Ray = 0
  or max|n0_rho| is not divisible by 4, hence >= 5, hence PI >= 5 and
  |Ray| <= (5/32)/5 = 1/32.  The exact maximum over 4 <= ht <= HCHK is computed below
  and the range ht > HCHK is covered by (5/32)/(HCHK+1). QED

  COROLLARY (resolves the 65/256 question for rank 1).  No rank-1 resonance class,
  at ANY height, has o_inf = 65/256 = 0.25390625: the rank-1 limits are at most 1/6.

usage: python3 tb_caps_v1.py [HCHK]
"""
import sys, itertools
from fractions import Fraction as F
from functools import reduce
from math import gcd

import rt_limit_v2 as RL
from tb_ray_v1 import ray_value, ray_cap, ray_cap_adm

HCHK = int(sys.argv[1]) if len(sys.argv) > 1 else 9
FLOOR = F(3, 32)


def pi_of(p):
    q = 1
    for x in p:
        if x:
            q *= abs(x)
    return q


if __name__ == "__main__":
    print("caps  (max over p mod 4 of |Ray(p)| * PI(p)):")
    raw = {s: ray_cap(s) for s in (2, 3, 4)}
    caps = {s: ray_cap_adm(s)[0] for s in (2, 3, 4)}
    for s in (2, 3, 4):
        print(f"   cap({s}) = {caps[s]} = {float(caps[s]):.7f}   attained at p mod 4 = "
              f"{ray_cap_adm(s)[1]}   (unrestricted-residue value {raw[s]})")
    CAP = max(caps.values())
    print(f"   CAP = max = {CAP} = {float(CAP):.7f}\n")

    # ---- exhaustive over admissible p of height <= HCHK
    best = F(0)
    argmax = []
    byht = {}
    for p in itertools.product(range(-HCHK, HCHK + 1), repeat=4):
        if not RL.admissible(p):
            continue
        v = abs(ray_value(p))
        h = max(abs(x) for x in p)
        d = byht.setdefault(h, [F(0), None])
        if v > d[0]:
            d[0], d[1] = v, p
        if v > best:
            best, argmax = v, [p]
        elif v == best and v > 0:
            argmax.append(p)
    print(f"exhaustive over admissible p with height <= {HCHK}:")
    print(f"   max |Ray(p)| = {best} = {float(best):.7f}")
    print(f"   attained at (up to the +- pair): "
          f"{sorted(set(tuple(x if argmax[0][0] >= 0 else -x for x in q) for q in argmax))[:6]}")
    print(f"   PI at the argmax: {pi_of(argmax[0])}")
    print(f"\n   {'ht':>3} {'max |Ray|':>12} {'float':>10}  argmax")
    for h in sorted(byht):
        v, a = byht[h]
        print(f"   {h:>3} {str(v):>12} {float(v):>10.7f}  {a}")

    # ---- the tail of the height range, covered by PI >= ht
    tailb = CAP / (HCHK + 1)
    print(f"\n   every admissible p with height > {HCHK} has PI(p) >= {HCHK+1} "
          f"(a coordinate = 0 mod 4 gives Ray = 0), so |Ray| <= CAP/{HCHK+1} = "
          f"{tailb} = {float(tailb):.7f}")
    print(f"   {'BELOW' if tailb < best else 'NOT below'} the height-<= {HCHK} maximum"
          f"  ==>  global max |Ray| = {best} = {float(best):.7f}")

    print(f"\nTHEOREM R1.  every rank-1 class limit lies in "
          f"[{FLOOR - best}, {FLOOR + best}] = "
          f"[{float(FLOOR-best):.7f}, {float(FLOOR+best):.7f}]")
    print(f"   upper end {FLOOR + best} = {float(FLOOR+best):.7f};  "
          f"65/256 = {float(F(65,256)):.7f} is {'ABOVE' if F(65,256) > FLOOR+best else 'below'}"
          f" it, so 65/256 is NOT a rank-1 class limit at any height.")

    # ---- THEOREM A
    best4 = F(0)
    arg4 = None
    for h in sorted(byht):
        if h >= 4 and byht[h][0] > best4:
            best4, arg4 = byht[h]
    tb = CAP / (HCHK + 1)
    print(f"\nTHEOREM A.  over admissible p with 4 <= height <= {HCHK}: "
          f"max |Ray| = {best4} = {float(best4):.7f}  at {arg4}")
    print(f"   height > {HCHK}: |Ray| <= {tb} = {float(tb):.7f}")
    bnd = max(best4, tb)
    print(f"   ==> ht(n0) >= 4  implies  |Ray(n0)| <= {bnd} = {float(bnd):.7f}"
          f"   (and the crude form CAP/5 = {CAP/5} = {float(CAP/5):.7f})")

    # ---- PI = 1 classification
    print("\nPI(p) = 1 (all support coordinates +-1) -- the admissible ones:")
    one = [p for p in itertools.product((-1, 0, 1), repeat=4)
           if RL.admissible(p) and pi_of(p) == 1]
    for p in one:
        print(f"   {p}   Ray = {ray_value(p)} = {float(ray_value(p)):+.7f}"
              f"   o_inf(<p>) = {FLOOR + ray_value(p)}")
    print(f"   count: {len(one)} (= 2 sign pairs of the two +-1 relations)")
