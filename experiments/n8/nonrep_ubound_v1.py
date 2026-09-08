"""
nonrep_ubound_v1  --  the quantity u = |U|, U = {x : the FOUR unit runners already
block all of Z/8}, and the rho0=4 identity.

rho0 = 4 facts (exact, from bad(4,t)):
   t mod 8 in {1,2,5,6} -> bad = {}         : call this x-set A
   t mod 8 in {0,7}     -> bad = evens      : A'
   t mod 8 in {3,4}     -> bad = odds       : A''
With e_4 = 8q+4, floor(e_4 x) runs over 0..e_4-1 each on an interval of length 1/e_4,
so |A| = (4q+2)/(8q+4) = 1/2, |A'| = |A''| = (2q+1)/(8q+4) = 1/4, EXACTLY, for every q.

Hence   |S| >= |A| - |A n U| = 1/2 - |A n U| >= 1/2 - u.

This script measures u over all four-unit-speed tuples and looks for the maximum
and for the tuples with u > 0.  Exact integer/rational arithmetic.
"""
from math import lcm, gcd
from fractions import Fraction as F
import itertools, sys
from collections import Counter

MASK = {(rho, t): sum(1 << r for r in range(8) if (rho * r + t) % 8 in (0, 7))
        for rho in (1, 3, 5, 7) for t in range(8)}
ALL = 255

def u_of(speeds):
    """measure of {x : bad(1,t1) u bad(3,t3) u bad(5,t5) u bad(7,t7) = Z/8}"""
    D = lcm(*speeds)
    pts = set()
    for e in speeds:
        pts.update(range(0, D, D // e))
    p = sorted(pts); p.append(D)
    mk = [[MASK[(rho, t)] for t in range(8)] for rho in (1, 3, 5, 7)]
    tot = 0
    for i in range(len(p) - 1):
        a = p[i]; cov = 0
        for j in range(4):
            cov |= mk[j][((speeds[j] * a) // D) % 8]
        if cov == ALL:
            tot += p[i + 1] - a
    return F(tot, D)

# verify the |A| = 1/2 identity directly for several e_4
print("[identity] e_4 = 8q+4 :  |A| = |{x: floor(e4 x) mod 8 in {1,2,5,6}}| ")
for q in range(0, 9):
    e = 8 * q + 4
    cA = sum(1 for j in range(e) if j % 8 in (1, 2, 5, 6))
    cAp = sum(1 for j in range(e) if j % 8 in (0, 7))
    cApp = sum(1 for j in range(e) if j % 8 in (3, 4))
    print(f"   q={q} e={e}: |A|={F(cA,e)}  |A'|={F(cAp,e)}  |A''|={F(cApp,e)}"
          f"   {'OK' if (F(cA,e),F(cAp,e),F(cApp,e))==(F(1,2),F(1,4),F(1,4)) else 'FAIL'}")

QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 12
rows = []
for qs in itertools.product(range(QMAX + 1), repeat=4):
    sp = tuple(8 * q + r for q, r in zip(qs, (1, 3, 5, 7)))
    if len(set(sp)) != 4: continue
    rows.append((u_of(sp), sp))
nz = sorted([r for r in rows if r[0] > 0], reverse=True)
print(f"\nunit speeds q<= {QMAX} (<= {8*QMAX+7}) : {len(rows)} tuples")
print(f"   tuples with u > 0 : {len(nz)}   ({len(nz)}/{len(rows)})")
print(f"   MAX u = {nz[0][0]} = {float(nz[0][0]):.6f}")
print("   the 25 largest u, with gcd-reduced form:")
for uu, sp in nz[:25]:
    g = 0
    for e in sp: g = gcd(g, e)
    print(f"      u = {str(uu):>12} = {float(uu):.6f}  speeds {sp}  gcd={g}  reduced={tuple(e//g for e in sp)}")
print(f"\n   distribution of u among the {len(nz)} nonzero: {Counter(str(r[0]) for r in nz).most_common(12)}")
