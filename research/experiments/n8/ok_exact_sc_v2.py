r"""
ok_exact_sc_v2 -- broad sweep of the EXACT criterion |S^c| < 1/2, and of its m -> infinity
limit.  Reuses ok_exact_sc_v1.analyse (exact rationals, entry evaluation, audited).

As m -> infinity the three A-sets equidistribute against (O,V,U), so
      |S^c|  ->  (1/4) o  +  (1/4) v  +  (1/2) u  =:  Lim
and the leaf closes in the limit iff  o + v + 2u < 2.   Generic o = v = 3/32, u tiny.
"""
from fractions import Fraction as F
from math import gcd
from functools import reduce
from ok_exact_sc_v1 import analyse
import sys

LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 32
MMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 100

tuples = []
for e1 in range(1, LIM+1, 8):
    for e3 in range(3, LIM+1, 8):
        for e5 in range(5, LIM+1, 8):
            for e7 in range(7, LIM+1, 8):
                e = (e1,e3,e5,e7)
                if reduce(gcd, e) == 1: tuples.append(e)

print(f"# {len(tuples)} primitive unit 4-tuples, speeds <= {LIM}; m = 4,12,...,{MMAX}")
fails = []; rows = []
worst_lim = None; maxo = maxv = maxu = None
for E in tuples:
    worst = None
    for m in range(4, MMAX+1, 8):
        o, v, u, al, be, AnU, Sc = analyse(E, m)
        if worst is None or Sc > worst[0]: worst = (Sc, m)
        if Sc >= F(1,2): fails.append((E, m, Sc, o, v, u))
    o, v, u, al, be, AnU, Sc = analyse(E, 4)
    lim = F(1,4)*o + F(1,4)*v + F(1,2)*u
    rows.append((worst[0], worst[1], E, o, v, u, lim))
    if worst_lim is None or lim > worst_lim[0]: worst_lim = (lim, E, o, v, u)
    if maxo is None or o > maxo[0]: maxo = (o, E)
    if maxv is None or v > maxv[0]: maxv = (v, E)
    if maxu is None or u > maxu[0]: maxu = (u, E)

rows.sort(key=lambda r: -r[0])
print(f"\n(E,m) pairs with |S^c| >= 1/2 : {len(fails)}")
for E, m, Sc, o, v, u in fails:
    print(f"    E={E} m={m}   |S^c| = {Sc} = {float(Sc):.6f}   o={o} v={v} u={u}")

print(f"\nTOP 8 tuples by max_m |S^c|:")
print(f"{'E':20} {'m*':>4} {'max|S^c|':>12} {'~':>9} {'o':>9} {'v':>9} {'u':>9}")
for Sc, m, E, o, v, u, lim in rows[:8]:
    print(f"{str(E):20} {m:>4} {str(Sc):>12} {float(Sc):9.6f} {float(o):9.6f} {float(v):9.6f} {float(u):9.6f}")

print(f"\nmax o = {maxo[0]} = {float(maxo[0]):.6f} at {maxo[1]}")
print(f"max v = {maxv[0]} = {float(maxv[0]):.6f} at {maxv[1]}")
print(f"max u = {maxu[0]} = {float(maxu[0]):.6f} at {maxu[1]}")
print(f"\nis v == o always? {all(r[3]==r[4] for r in rows)}")
lm, E, o, v, u = worst_lim
print(f"max limit value (1/4)o+(1/4)v+(1/2)u = {lm} = {float(lm):.6f} at {E}   (need < 1/2)")
print(f"  equivalently max (o + v + 2u) = {o+v+2*u} = {float(o+v+2*u):.6f}  (need < 2)")
