r"""
ok_height_v3 -- height test, lean: supports 2 and 3 only (support 4 dropped for speed, so h
is an UPPER bound on the true height -- noted, since a support-4 all-+-1 resonance can have
height 1).  h(E) = min prod|p_j| over primitive p with p.e=0, no p_j = 0 mod 4.
"""
from fractions import Fraction as F
from itertools import combinations, product
from functools import reduce
from math import gcd
from collections import defaultdict
import statistics, sys

H=6
C=[x for x in range(-H,H+1) if x!=0 and x%4!=0]
def arcs(e): return [(F(8*j+1,8*e), F(8*j+7,8*e)) for j in range(e)]
def inter(A,B):
    out=[]; i=j=0
    while i<len(A) and j<len(B):
        lo=max(A[i][0],B[j][0]); hi=min(A[i][1],B[j][1])
        if lo<hi: out.append((lo,hi))
        if A[i][1]<B[j][1]: i+=1
        else: j+=1
    return out
def G_measure(E):
    cur=arcs(E[0])
    for e in E[1:]:
        cur=inter(cur,arcs(e))
        if not cur: return F(0)
    return sum((b-a for a,b in cur), F(0))
def height(E):
    best=10**9
    for i,j in combinations(range(7),2):
        g=gcd(E[i],E[j]); a=E[i]//g; b=E[j]//g
        if a%4 and b%4 and a*b<best: best=a*b
    for idx in combinations(range(7),3):
        x,y,z=(E[i] for i in idx)
        for ka in C:
            for kb in C:
                r=-(ka*x+kb*y)
                if r % z: continue
                kc=r//z
                if kc==0 or kc%4==0: continue
                if gcd(gcd(abs(ka),abs(kb)),abs(kc))!=1: continue
                pr=abs(ka*kb*kc)
                if pr<best: best=pr
    return best

LIM=int(sys.argv[1]) if len(sys.argv)>1 else 18
rows=[]
for E in combinations(range(1,LIM+1),7):
    if reduce(gcd,E)!=1: continue
    if not any(e%8==0 for e in E): continue
    rows.append((height(E), float(G_measure(list(E))), E))
print(f"{len(rows)} Case-2 tuples in [1..{LIM}], supports 2-3, coords to |{H}|\n")
b=defaultdict(list)
for h,g,E in rows: b[h].append((g,E))
print(f"{'h(E)':>7} {'tuples':>8} {'min |G|':>10} {'mean |G|':>10}  argmin")
for h in sorted(b)[:12]:
    v=b[h]; mn=min(v)
    print(f"{h:>7} {len(v):>8} {mn[0]:10.6f} {statistics.mean(x for x,_ in v):10.6f}  {mn[1]}")
tgt=float(F(93,14560)); ref=0.75**7
print(f"\ntarget {tgt:.6f};  (3/4)^7 = {ref:.6f}")
for thr in (1,2,3,4,6,8):
    hi=[g for h,g,E in rows if h>thr]
    if hi: print(f"  h > {thr}: {len(hi):6} tuples, min |G| = {min(hi):.6f} "
                 f"({min(hi)/tgt:5.1f}x target, {min(hi)/ref:.2f} of (3/4)^7)")
