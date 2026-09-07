"""
n=8: is there a SPECTRAL GAP on the only case that needs proving?

Reduction [PROVED, one line]: for q in {2..8} and gcd(a,q)=1,
      ||v * a/q|| = |v a mod q| / q >= 1/q,
so if q divides no element of T then t = a/q witnesses LRC(8) -- strictly for
q <= 7, with equality for q = 8.  Hence any T needing an argument contains a
multiple of q for every q in {2..8}; the maximal levels are q = 5, 6, 7, 8.
In particular EVERY set with no multiple of 8 is settled by t = 1/8.

This script measures  min M(T)  over sets that DO contain a multiple of 8 (plus
the other forced levels), i.e. over the residual hard case.  If that minimum is
bounded away from 1/8, the residual case is NOT sharp and an analytic proof of it
may be non-tight.  Exact rational arithmetic; no floating point in any decision.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
import sys

def fn(x):
    r = x - (x.numerator//x.denominator)
    return r if r <= F(1,2) else 1-r

def gaps_of(T, n=8):
    iv=[]
    for v in T:
        w=F(1,n*v)
        for k in range(0,v+1):
            lo,hi=F(k,v)-w, F(k,v)+w
            if hi<=0 or lo>=1: continue
            iv.append((max(lo,F(0)),min(hi,F(1))))
    iv.sort()
    out,cur=[],F(0)
    for lo,hi in iv:
        if lo>cur: out.append((cur,lo))
        if hi>cur: cur=hi
    if cur<1: out.append((cur,F(1)))
    return out

def M_exact(T, n=8):
    gs=gaps_of(T,n)
    if not gs: return F(1,n)
    dens=set(2*v for v in T)
    for a,b in combinations(T,2): dens.add(a+b); dens.add(abs(a-b))
    dens.discard(0)
    best=F(1,n)
    for glo,ghi in gs:
        c={glo,ghi}
        for d in dens:
            k0=int(glo*d)
            for k in range(k0,k0+3):
                t=F(k,d)
                if glo<=t<=ghi: c.add(t)
        for t in c:
            m=min(fn(v*t) for v in T)
            if m>best: best=m
    return best

def main(V):
    LV=(5,6,7,8)
    best=None; rec=[]
    ncand=0
    for T in combinations(range(1,V+1),7):
        if not all(any(v%q==0 for v in T) for q in LV): continue
        g=0
        for v in T: g=gcd(g,v)
        if g!=1: continue
        ncand+=1
        m=M_exact(T)
        rec.append((m,T))
        if best is None or m<best:
            best=m; print(f"  new min M={m} (~{float(m):.6f})  T={T}", flush=True)
    rec.sort()
    print(f"\nV={V}: {ncand} sets contain multiples of 5,6,7 AND 8, gcd 1")
    print(f"min M over the residual hard case = {best} (~{float(best):.6f})   vs 1/8 = 0.125")
    print("10 smallest:")
    for m,T in rec[:10]: print(f"   {str(m):>10} ~{float(m):.6f}  {T}")

if __name__=="__main__":
    main(int(sys.argv[1]) if len(sys.argv)>1 else 40)
