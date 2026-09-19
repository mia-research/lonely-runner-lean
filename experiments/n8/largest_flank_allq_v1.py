"""Rigidity of largest-flank shadowing, with NO cap on the denominator.
Search over integer difference sets directly: flank e, six distinct nonzero movers d with
|d| <= e, d != e.  Every reduced denominator q = e/gcd(|d|,e) <= e occurs, so capping q is gone.
Question: is every shadowing configuration one of the 32 cores {+-1/2} x {+-1/8,+-3/8,+-5/8,+-7/8}?"""
from math import gcd
from fractions import Fraction
import sys
def mask(d,e):
    M=8*e; m=0
    for k in range(e):
        r=(d*(8*k+1))%M
        if min(r,M-r)<e: m|=1<<k
    return m
def core_ratios(e):
    S=set()
    for h in (Fraction(1,2),Fraction(-1,2)):
        S.add(frozenset())
    return S
NMAX=int(sys.argv[1]) if len(sys.argv)>1 else 24
nonc=[]; total=0
DEN=set(); EV=set()
for e in range(1,NMAX+1):
    full=(1<<e)-1
    cand=[d for d in range(-e,e+1) if d!=0 and d!=e]
    ms=[(d,mask(d,e)) for d in cand]
    ms=[(d,m) for d,m in ms if m!=0]                 # movers that block nothing are irrelevant
    ms.sort(key=lambda t:-bin(t[1]).count("1"))
    best=bin(ms[0][1]).count("1") if ms else 0
    res=[]
    def dfs(i,chosen,cov,depth):
        global total
        if cov==full:
            res.append(tuple(chosen)); total+=1; return
        if depth==6 or i>=len(ms): return
        need=e-bin(cov).count("1")
        if need>(6-depth)*best: return
        for j in range(i,len(ms)):
            d,m=ms[j]
            if (6-depth-1)*best < e-bin(cov|m).count("1"): continue
            chosen.append(d); dfs(j+1,chosen,cov|m,depth+1); chosen.pop()
    dfs(0,[],0,0)
    for ds in res:
        R=sorted(Fraction(d,e) for d in ds)
        A={abs(r) for r in R}
        ok=(Fraction(1,2) in A) and all(Fraction(p,8) in A for p in (1,3,5,7))
        DEN.update(r.denominator for r in R); EV.add(e)
        if not ok: nonc.append((e,ds,R))
print(f"exhaustive flanks e = 1..{NMAX}, six distinct movers |d| <= e:")
print(f"  shadowing configurations found: {total}")
print(f"  NOT containing a core: {len(nonc)}")
print(f"  denominators of ratios, over ALL configurations: {sorted(DEN)}")
print(f"  flank values e that admit ANY shadowing: {sorted(EV)}")
for e,ds,R in nonc[:10]:
    print(f"     e={e} ds={ds} ratios={[str(r) for r in R]}")
