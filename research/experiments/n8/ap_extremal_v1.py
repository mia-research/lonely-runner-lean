"""Owner: "AP is global isolation's most efficient version -- is there more to that?"

Global isolation <=> the reduced speeds are a complete residue system mod n (WHICH_GRIDS sec1).
Eight distinct integers covering all residues mod 8 need spread >= 7, and spread = 7 forces eight
CONSECUTIVE integers -- the AP of gap 1.  So the AP should be the UNIQUE minimal-spread globally
isolated arrangement.  And if so, what is its S = d_max/d_min?"""
from fractions import Fraction as F
from math import gcd
from itertools import combinations
from collections import Counter

def reduced(v):
    g=0
    for a,b in combinations(v,2): g=gcd(g,abs(b-a))
    if g==0: return None,None
    return [(x-v[0])//g for x in v], g
def globally_isolated(v):
    u,g=reduced(v)
    if u is None: return False
    return len(set(x%8 for x in u))==8
def maxS(v):
    best=0
    for i in range(8):
        ds=[abs(v[j]-v[i]) for j in range(8) if j!=i]
        best=max(best, max(ds)/min(ds))
    return best

print("=== all globally isolated 8-subsets of [0,16), by reduced spread ===")
byspread={}
for v in combinations(range(0,16),8):
    if not globally_isolated(v): continue
    u,g=reduced(v)
    sp=max(u)-min(u)
    d=byspread.setdefault(sp,[])
    d.append(v)
print(f"   {'reduced spread':>15} {'count':>7} {'is every one an AP?':>21} {'max-over-subjects S':>21}")
for sp in sorted(byspread)[:6]:
    vs=byspread[sp]
    aps=all(sorted(reduced(v)[0])==list(range(min(reduced(v)[0]),min(reduced(v)[0])+8)) for v in vs)
    Ss=sorted({round(maxS(v),4) for v in vs})
    print(f"   {sp:>15} {len(vs):>7} {str(aps):>21} {str(Ss[:4]):>21}")

print()
print("=== the minimal-spread case, spelled out ===")
mn=min(byspread)
print(f"   minimal reduced spread among globally isolated arrangements: {mn}")
print(f"   number attaining it: {len(byspread[mn])}   all consecutive (an AP of gap g)? "
      f"{all(sorted(reduced(v)[0])==list(range(min(reduced(v)[0]),min(reduced(v)[0])+8)) for v in byspread[mn])}")
print(f"   their max-over-subjects S: {sorted({round(maxS(v),6) for v in byspread[mn]})}")
print()
print("=== is S = 7 the MINIMUM of max-over-subjects S among globally isolated arrangements? ===")
best=None
for sp in sorted(byspread):
    for v in byspread[sp]:
        s=maxS(v)
        if best is None or s<best[0]: best=(s,v,sp)
print(f"   minimum max-S = {best[0]}  at v = {best[1]}  (reduced spread {best[2]})")
print()
print("   Theorem 4.8 clears a subject at its bound when S <= 7.")
print("   So the AP sits EXACTLY on that threshold -- it is the sharp case, with zero slack.")
