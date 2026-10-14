#!/usr/bin/env python3
"""Is K measuring difficulty, or just distance from the anchor?
Compute K_min and |G| for every Case-2 tuple in [1..18] and cross them."""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd, floor
def goodset(E):
    iv=[]
    for e in E:
        for k in range(0,e+1):
            lo,hi=max(F(8*k-1,8*e),F(0)),min(F(8*k+1,8*e),F(1))
            if lo<hi: iv.append((lo,hi))
    iv.sort(); m=[]
    for lo,hi in iv:
        if m and lo<m[-1][1]: m[-1][1]=max(m[-1][1],hi)
        else: m.append([lo,hi])
    g=[]; cur=F(0)
    for lo,hi in m:
        if cur<=lo: g.append((cur,lo))
        cur=max(cur,hi)
    if cur<=1: g.append((cur,F(1)))
    return [(a,b) for a,b in g if a<=b and not(a==b==0) and not(a==b==1)]
def kindex(e,r,eps):
    lo=F(1-r,8*e); k=floor((eps-lo)*e)
    for kk in (k-1,k,k+1):
        if lo+F(kk,e) <= eps <= lo+F(3,4*e)+F(kk,e): return kk
    return None
def KminG(E):
    G=goodset(E); best=None
    for a in (1,3,5,7):
        p=F(a,8)
        for lo,hi in G:
            for eps in ({F(0)} if lo<=p<=hi else set()) | {lo-p,hi-p}:
                if not (lo<=p+eps<=hi): continue
                ks=[kindex(e,(e*a)%8,eps) for e in E]
                if any(k is None for k in ks): continue
                K=max(abs(k) for k in ks)
                if best is None or K<best: best=K
    return best, sum(b-a for a,b in G)

rows=[]
for E in combinations(range(1,19),7):
    if reduce(gcd,E)!=1 or all(e%8 for e in E): continue
    K,M=KminG(E)
    if K is not None: rows.append((K,M,E))
rows.sort(key=lambda r:r[1])
n=len(rows)
print(f"Case-2 tuples in [1..18] with K computed: {n}")
print(f"\nmax K_min within each |G| band (lowest |G| = hardest):")
import statistics
bands=[(0,0.02),(0.02,0.05),(0.05,0.08),(0.08,0.11),(0.11,0.14)]
for lo,hi in bands:
    sub=[r for r in rows if lo<=float(r[1])<hi]
    if not sub: continue
    mk=max(sub,key=lambda r:r[0])
    print(f"  |G| in [{lo:.2f},{hi:.2f}): {len(sub):>6} tuples   max K = {mk[0]}  at {mk[2]}"
          f"   (|G|={float(mk[1]):.5f})")
hard=[r for r in rows if float(r[1])<=2*float(rows[0][1])]
print(f"\nHARDEST tuples (|G| <= 2x the minimum {float(rows[0][1]):.6f}): {len(hard)}")
print(f"  max K among them = {max(r[0] for r in hard)}")
for r in sorted(hard,key=lambda r:-r[0])[:5]:
    print(f"    K={r[0]}  |G|={float(r[1]):.6f}  {r[2]}")
# rank correlation
ks=[r[0] for r in rows]; gs=[float(r[1]) for r in rows]
def rank(v):
    order=sorted(range(len(v)),key=lambda i:v[i]); rk=[0]*len(v)
    for p,i in enumerate(order): rk[i]=p
    return rk
rk,rg=rank(ks),rank(gs)
mk,mg=statistics.mean(rk),statistics.mean(rg)
num=sum((a-mk)*(b-mg) for a,b in zip(rk,rg))
den=(sum((a-mk)**2 for a in rk)*sum((b-mg)**2 for b in rg))**.5
print(f"\nSpearman(K_min, |G|) = {num/den:+.4f}   (positive => bigger K goes with LARGER |G| = easier)")
