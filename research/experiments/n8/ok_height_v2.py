r"""
ok_height_v2 -- height conjecture, fast.  Solve for the last coordinate rather than
enumerating it, and cover supports 2, 3, 4.

h(E) = min over primitive p != 0, p.e = 0, no p_j = 0 mod 4, of prod_{supp}|p_j|.
Ray law |R(p)| <= cap(s)/prod|p_j|, so large h => small tail by construction.
Conjecture: h large => |G| near (3/4)^7 = 0.13348.
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

CAP=10**9
def height(E):
    best=CAP
    # support 2
    for i,j in combinations(range(7),2):
        g=gcd(E[i],E[j]); a=E[i]//g; b=E[j]//g
        if a%4 and b%4 and a*b<best: best=a*b
    # support 3 and 4: solve for the last coordinate
    for s in (3,4):
        for idx in combinations(range(7),s):
            sub=[E[i] for i in idx]; last=sub[-1]
            for p in product(C,repeat=s-1):
                r=-sum(x*y for x,y in zip(p,sub[:-1]))
                if r % last: continue
                kl=r//last
                if kl==0 or kl%4==0: continue
                q=list(p)+[kl]
                if reduce(gcd,[abs(x) for x in q])!=1: continue
                pr=1
                for x in q: pr*=abs(x)
                if pr<best: best=pr
    return best

LIM=int(sys.argv[1]) if len(sys.argv)>1 else 20
rows=[]
for E in combinations(range(1,LIM+1),7):
    if reduce(gcd,E)!=1: continue
    if not any(e%8==0 for e in E): continue
    rows.append((height(E), float(G_measure(list(E))), E))
print(f"{len(rows)} Case-2 tuples in [1..{LIM}];  coordinates to |{H}|\n")
b=defaultdict(list)
for h,g,E in rows: b[h].append((g,E))
print(f"{'h(E)':>7} {'tuples':>8} {'min |G|':>10} {'mean |G|':>10}  argmin")
for h in sorted(b)[:14]:
    v=b[h]; mn=min(v)
    print(f"{h:>7} {len(v):>8} {mn[0]:10.6f} {statistics.mean(x for x,_ in v):10.6f}  {mn[1]}")
tgt=float(F(93,14560))
print(f"\ntarget {tgt:.6f};  (3/4)^7 = {0.75**7:.6f}")
for thr in (2,3,4,6,8,12):
    hi=[g for h,g,E in rows if h>thr]
    if hi:
        print(f"  h > {thr:2}: {len(hi):6} tuples, min |G| = {min(hi):.6f} "
              f"({min(hi)/tgt:5.1f}x target, {min(hi)/0.75**7:.2f} of (3/4)^7)")
