"""
v2: confirm pentagon kills (1,±2) robustly + check witness-l structure + the 8
small-q Table-4 pairs.
"""
from math import gcd
from fractions import Fraction as F

def frac(x): return x - (x.numerator // x.denominator)
def S(l, p, q, r):
    u = 2*l + 1
    return frac(F(r*u, 2*q)), frac(F(p*u, 2*q))
XLO, XHI, YLO, YHI = F(1,6), F(1,2), F(1,6), F(1,3)
def inR(X, Y): return XLO <= X <= XHI and YLO <= Y <= YHI
def cap_R_empty(p, q, r): return all(not inR(*S(l,p,q,r)) for l in range(q))
def in_G(i, j, p, q, r):
    return any((m*r) % q == i % q and (m*p) % q == j % q for m in range(q))
def is_pair(ii, jj, p, q, r):
    if not in_G(ii, jj, p, q, r): return False
    for k in range(-abs(ii), abs(ii)+1):
        for l in range(-abs(jj), abs(jj)+1):
            if (k,l)==(0,0) or (abs(k)==abs(ii) and abs(l)==abs(jj)): continue
            if in_G(k,l,p,q,r): return False
    return True
def pent_wit_count(p, p2, q, r, s):
    e1=F(r*(s-q),3*q*s); e0=F(p*(s-q),3*q*s); e2=F(p2*(s-q),3*q*s)
    out=[]
    for l in range(q):
        X,Y=S(l,p,q,r)
        if X>=F(1,6)-e1 and Y>=F(1,6)-e0 and Y<=F(1,3)+e2 and X<=F(5,6) \
           and F(1,3*s)<=(F(5,6)-X)/r+(Y-F(1,6))/p and F(1,3*s)<=(F(5,6)-X)/r+(F(1,3)-Y)/p2:
            out.append(l)
    return out

for (ii,jj) in [(1,2),(1,-2)]:
    survs=[]
    for q in range(18,61):
        for p in range(1,q):
            if 3*p>=q or gcd(p,q)!=1: continue
            for r in range(q+1,(3*q)//2+1):
                if 2*r>=3*q: continue
                if is_pair(ii,jj,p,q,r) and cap_R_empty(p,q,r):
                    survs.append((p,q,r))
    fails=0; mincounts=[]
    for (p,q,r) in survs:
        for p2 in range(p+1,q):
            for s in range(r+1,3*q+1):
                w=pent_wit_count(p,p2,q,r,s)
                if not w: fails+=1
                else: mincounts.append(len(w))
    print(f"pair {ii},{jj}: survivors(q<61)={len(survs)}, (p2,s)-completions with NO pentagon witness: {fails}")
    if mincounts:
        print(f"   pentagon witnesses per completion: min={min(mincounts)} max={max(mincounts)} mean={sum(mincounts)/len(mincounts):.1f}")

# the 8 small-q Table-4 pairs: do they have pentagon witnesses?
print("\n=== small-q Table-4 pairs: pentagon witness check ===")
for (ii,jj) in [(2,3),(2,-3),(3,4),(3,-4),(4,3),(4,-3)]:
    survs=[]
    for q in range(18,30):
        for p in range(1,q):
            if 3*p>=q or gcd(p,q)!=1: continue
            for r in range(q+1,(3*q)//2+1):
                if 2*r>=3*q: continue
                if is_pair(ii,jj,p,q,r) and cap_R_empty(p,q,r):
                    survs.append((p,q,r))
    if not survs: continue
    fails=0; tot=0
    for (p,q,r) in survs:
        for p2 in range(p+1,q):
            for s in range(r+1,3*q+1):
                tot+=1
                if not pent_wit_count(p,p2,q,r,s): fails+=1
    print(f"  pair {ii},{jj}: survivors={len(survs)} ({[s[:3] for s in survs]}), no-witness completions: {fails}/{tot}")
