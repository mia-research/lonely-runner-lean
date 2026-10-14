r"""
ok_reflect_v1 -- WHY is v = o?  Candidate mechanism: the reflection x -> 1-x carries O to V.

bad(e,t) = { r : e*r + t = 0 or 7  (mod 8) }.  For x not a breakpoint, floor(e(1-x)) = e-1-floor(ex).
O = { ODD  subset of union bad },   V = { EVEN subset of union bad }.

Test 1: is the SET V equal to the reflection 1-O (up to endpoints)?
Test 2: cell-local algebraic identity  bad(e, e-1-t) = 4 - bad(e,t)  (i.e. r -> 4-r)?
        If bad(e,e-1-t) = { 4-r : r in bad(e,t) } then, since r -> 4-r maps ODD onto ODD
        and EVEN onto EVEN, reflection would preserve O, not swap O and V.  So the right
        candidate is r -> c-r for an ODD c, which swaps parities.
"""
from fractions import Fraction as F
from math import gcd
from functools import reduce
import itertools

FULL = frozenset(range(8)); ODD = frozenset({1,3,5,7}); EVEN = frozenset({0,2,4,6})

def bad(e, t):
    return frozenset(r for r in range(8) if (e*r + t) % 8 in (0, 7))

# ---- Test 2 first: pure algebra on (e mod 8, t mod 8), no geometry ------------------
print("Test 2: for which shift c is  bad(e, e-1-t) == { c-r : r in bad(e,t) }  for ALL e,t?")
for c in range(8):
    ok = all(bad(e, (e-1-t) % 8) == frozenset((c-r) % 8 for r in bad(e, t))
             for e in (1,3,5,7) for t in range(8))
    if ok: print(f"   c = {c}: HOLDS for all e in (1,3,5,7), all t mod 8")
print()

# ---- Test 1: geometry ---------------------------------------------------------------
def cells(S):
    pts = {F(0), F(1)}
    for e in S:
        for j in range(1, e+1):
            q = F(j, e)
            if 0 < q < 1: pts.add(q)
    p = sorted(pts); return list(zip(p, p[1:]))
def fl(e, a): v = e*a; return v.numerator // v.denominator

def OV(E):
    """return list of (lo,hi,inO,inV) over the cells"""
    out = []
    for a, b in cells(E):
        cov = set()
        for e in E: cov |= bad(e, fl(e, a))
        out.append((a, b, ODD <= cov, EVEN <= cov))
    return out

print("Test 1: is V the mirror image of O under x -> 1-x ?")
bad_ct = 0; tested = 0
for E in [(1,3,5,7),(1,11,5,7),(17,3,5,7),(9,11,13,15),(1,3,13,15),(25,19,13,7)]:
    segs = OV(E)
    # O as a union of intervals; check inV(cell) == inO(mirror cell)
    mism = 0
    for a, b, inO, inV in segs:
        # mirror of [a,b) is (1-b, 1-a]; sample its interior
        mid = 1 - (a + b)/2
        cov = set()
        for e in E:
            # value at an interior point of the mirrored cell
            t = fl(e, mid) if mid not in (F(0),F(1)) else 0
            cov |= bad(e, t)
        if (ODD <= cov) != inV: mism += 1
        tested += 1
    print(f"   E={str(E):18} cells={len(segs):5}  mismatches (V(x) vs O(1-x)) = {mism}")
    bad_ct += mism
print(f"   TOTAL mismatches over {tested} cells: {bad_ct}")
