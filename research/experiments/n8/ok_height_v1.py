r"""
ok_height_v1 -- test the height conjecture proposed in WHERE_THE_PROOF_IS_v1.

h(E) = min over primitive p != 0 with p.e = 0 and no p_j = 0 mod 4, of prod_{j in supp} |p_j|.
Ray law: |R(p)| <= cap(s)/prod|p_j|, so a tuple whose smallest-height resonance is LARGE has
a small tail by construction.  Conjecture: h(E) large => |G| near (3/4)^7 = 0.13348.

Enumerated over coordinates in [-H,H] (so h is capped; report the cap when nothing is found).
"""
from fractions import Fraction as F
from itertools import combinations, product
from functools import reduce
from math import gcd
import statistics

H=4
COORDS=[x for x in range(-H,H+1) if x!=0 and x%4!=0]
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

CAP=10**6
def height(E):
    best=CAP
    for s in (2,3,4):
        for idx in combinations(range(7),s):
            sub=[E[i] for i in idx]
            for p in product(COORDS,repeat=s):
                if sum(x*y for x,y in zip(p,sub))!=0: continue
                if reduce(gcd,[abs(x) for x in p])!=1: continue
                pr=1
                for x in p: pr*=abs(x)
                if pr<best: best=pr
    return best

rows=[]
for E in combinations(range(1,23),7):
    if reduce(gcd,E)!=1: continue
    if not any(e%8==0 for e in E): continue
    rows.append((height(E), float(G_measure(list(E))), E))
print(f"{len(rows)} Case-2 tuples in [1..22];  coordinates enumerated to |{H}|\n")
from collections import defaultdict
b=defaultdict(list)
for h,g,E in rows: b[h].append((g,E))
print(f"{'h(E)':>8} {'tuples':>8} {'min |G|':>10} {'mean |G|':>10}  argmin")
for h in sorted(b):
    v=b[h]; mn=min(v)
    lab = f">{H**2}" if h==CAP else str(h)
    print(f"{lab:>8} {len(v):>8} {mn[0]:10.6f} {statistics.mean(x for x,_ in v):10.6f}  {mn[1]}")
tgt=float(F(93,14560))
print(f"\ntarget {tgt:.6f};  (3/4)^7 = {0.75**7:.6f}")
lo=[g for h,g,E in rows if h<=4]; hi=[g for h,g,E in rows if h>4]
print(f"h <= 4 : {len(lo):6} tuples, min |G| = {min(lo):.6f} ({min(lo)/tgt:.1f}x target)")
print(f"h >  4 : {len(hi):6} tuples, min |G| = {min(hi):.6f} ({min(hi)/tgt:.1f}x target)")
