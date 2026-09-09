r"""
ok_isolation_v1 -- ISOLATION LEMMA test.

Claim.  Refine [0,1) by B = union_rho { 2k/e_rho }, the breakpoints of a_rho = floor(e_rho x/2)
mod 4.  Crossing a breakpoint of exactly ONE rho changes a_rho by 1 mod 4, hence changes
nu_rho to a DIFFERENT value; since on O the four nu's already exhaust (Z/2)^2, the moved
nu_rho must collide with another.  So no two O-cells are adjacent across a single-rho
breakpoint.  The only escapes are breakpoints shared by >= 2 speeds, which are the multiples
of 2/gcd(e_rho,e_sigma).

Reported: adjacent O-cell pairs, split by whether the shared breakpoint is single or multi.
"""
from fractions import Fraction as F
from math import gcd
from functools import reduce
from itertools import combinations
import sys

MUV = (0,1,2,3)

def analyse(e):
    bps = {}
    for i, ei in enumerate(e):
        k = 0
        while F(2*k, ei) < 1:
            bps.setdefault(F(2*k, ei), set()).add(i); k += 1
    pts = sorted(bps)
    pts.append(F(1))
    good = []
    for j in range(len(pts)-1):
        lo = pts[j]
        a = [int(ei*lo/2) % 4 for ei in e]
        nu = [a[i] ^ MUV[i] for i in range(4)]
        good.append(len(set(nu)) == 4)
    single_adj = multi_adj = 0
    for j in range(len(pts)-2):
        if good[j] and good[j+1]:
            owners = bps[pts[j+1]]
            if len(owners) == 1: single_adj += 1
            else: multi_adj += 1
    # wrap-around cell (last -> first, across x=0 which every speed owns)
    return single_adj, multi_adj, sum(good), len(good)

LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 48
tup = []
for e1 in range(1, LIM+1, 8):
    for e3 in range(3, LIM+1, 8):
        for e5 in range(5, LIM+1, 8):
            for e7 in range(7, LIM+1, 8):
                e = (e1,e3,e5,e7)
                if reduce(gcd, e) == 1: tup.append(e)
tot_s = tot_m = 0; worst = None; ratio = None
for e in tup:
    s, m, g, n = analyse(e)
    tot_s += s; tot_m += m
    r = F(g, n)
    if ratio is None or r > ratio[0]: ratio = (r, e, g, n)
print(f"# {len(tup)} primitive tuples, speeds <= {LIM}")
print(f"adjacent O-cell pairs across a SINGLE-speed breakpoint : {tot_s}   <-- lemma says 0")
print(f"adjacent O-cell pairs across a MULTI-speed breakpoint  : {tot_m}   <-- allowed")
print(f"\nmax O-cell COUNT fraction: {ratio[0]} = {float(ratio[0]):.6f} "
      f"({ratio[2]}/{ratio[3]} cells) at {ratio[1]}   [lemma bound ~1/2]")
