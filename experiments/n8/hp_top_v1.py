r"""hp_top_v1 -- ranked table of the largest o, u+o, u+2o over PRIMITIVE unit tuples,
and the same restricted to tuples outside the dilation orbit of (1,3,5,7).
Exact Fractions.  usage: python3 hp_top_v1.py QMAX TOPN"""
import itertools, sys
from math import gcd
from fractions import Fraction as F
from hp_scan_v1 import invariants, gcd4, R4

QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6
TOPN = int(sys.argv[2]) if len(sys.argv) > 2 else 15

def orbit_of_1357(sp4):
    """is sp4 = lambda*(1,3,5,7) re-indexed, for some odd lambda?  Equivalently
    sp4[i] = lam*rho_i' with a permutation.  Test: exists odd lam with
    {lam*1,lam*3,lam*5,lam*7} = set(sp4) as integers."""
    g = gcd4(sp4)
    return sorted(e // g for e in sp4) == [1, 3, 5, 7]

rows = []
for qs in itertools.product(range(QMAX + 1), repeat=4):
    sp4 = tuple(8 * q + r for q, r in zip(qs, R4))
    if len(set(sp4)) != 4:
        continue
    o, u, nO, nU, ow = invariants(sp4)
    rows.append((sp4, gcd4(sp4), o, u, nO, nU, orbit_of_1357(sp4)))

def show(title, key, filt):
    sub = [r for r in rows if filt(r)]
    sub.sort(key=lambda r: -key(r))
    print(f"\n{title}   ({len(sub)} tuples)")
    seen = set()
    n = 0
    for r in sub:
        v = key(r)
        if v not in seen:
            seen.add(v); n += 1
        if n > TOPN: break
        print(f"   {str(r[0]):22s} g={r[1]:2d} o={str(r[2]):>12s} u={str(r[3]):>10s}"
              f"  nO={r[4]:2d} nU={r[5]:2d}  val={float(v):.6f} = {v}")

prim = lambda r: r[1] == 1
prim_no_orbit = lambda r: r[1] == 1 and not r[6]
show("max o, primitive", lambda r: r[2], prim)
show("max u+o, primitive", lambda r: r[3] + r[2], prim)
show("max u+2o, primitive", lambda r: r[3] + 2 * r[2], prim)
show("max u+2o, primitive minus orbit(1,3,5,7)", lambda r: r[3] + 2 * r[2], prim_no_orbit)
show("max u+2o, ALL tuples minus orbit", lambda r: r[3] + 2 * r[2],
     lambda r: not r[6])
