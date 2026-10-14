"""A NECESSARY condition for band 2, far smaller than the full covering.

If R is clear at any point of [1,15] then R_final <= that point < 16, so band 2 needs EVERY
candidate in [1,15] to be non-clear.  Take the candidates where the largest reading sits on a band
edge:  R_k = (8k+1)/S.  There s_7 = S reads exactly 8k+1 -- clear by construction.  With
v_i = s_i/S in (1/8, 1) and v_7 = 1,

        s_i . R_k  =  (8k+1) . v_i

so band 2 requires: for every k with 1 <= (8k+1)/S <= 15, SOME i in {2..6} has (8k+1)v_i within 1
of a multiple of 8.

Five numbers must kill about fourteen points.  Compute which k each v kills, then ask whether five
v's can cover all of them."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
import numpy as np
from itertools import combinations
def kills(v, ks):
    """set of k in ks that v kills: (8k+1)v within 1 of a multiple of 8"""
    out=set()
    for k in ks:
        x=(8*k+1)*v
        m=x%8.0
        if m<1.0 or m>7.0: out.add(k)
    return frozenset(out)
for S in (7.2, 7.45, 7.5, 7.75, 7.95):
    ks=[k for k in range(0,40) if 1.0 <= (8*k+1)/S <= 15.0]
    print(f"\n  S = {S}:  candidates R_k = (8k+1)/S in [1,15] -> k in {ks}  ({len(ks)} points)")
    # how many can one v kill?
    grid=np.arange(1/8+1e-6, 1.0, 1e-5)
    best=(0,None,None)
    seen={}
    for v in grid:
        kv=kills(v,ks)
        if len(kv)>best[0]: best=(len(kv),v,kv)
        seen.setdefault(kv, v)
    print(f"    most k's a single v can kill: {best[0]} of {len(ks)}   (at v = {best[1]:.5f}, killing {sorted(best[2])})")
    print(f"    distinct kill-sets over the grid: {len(seen)}")
    # can five v's cover all ks?
    sets=[(kv,v) for kv,v in seen.items() if kv]
    sets.sort(key=lambda z:-len(z[0]))
    sets=sets[:4000]
    target=set(ks)
    found=None
    # greedy first
    cur=set(); pick=[]
    while cur!=target:
        b=max(sets, key=lambda z: len(z[0]-cur))
        if not (b[0]-cur): break
        cur|=b[0]; pick.append(b[1])
        if len(pick)>8: break
    print(f"    greedy cover needs {len(pick)} v's (band 2 allows only 5); covered {len(cur)} of {len(ks)}")
    if len(pick)<=5 and cur==target:
        print(f"      GREEDY SUCCEEDS with {len(pick)}: {[round(x,5) for x in pick]}")
