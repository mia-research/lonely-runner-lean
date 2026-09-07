"""
n=8: how small can M(T) get on the RESIDUAL case?

Residual case R = T holds a multiple of 5, of 6, of 7 and of 8 (gcd 1).  Every set
outside R is settled in one line by t = 1/q or t = 1/8, and every tight instance
found so far lies outside R.  If  inf{M(T) : T in R} > 1/8  then the good set has
nonempty interior throughout R and a measure ("good fraction") argument is available
there -- which is exactly what the n=11 architecture needs and what the tight
instances deny it globally.

This is a SEARCH for small M, not a null test: the informative outcome is finding
residual sets with M near 1/8.  Three probes:
  (a) targeted -- perturb each known tight instance into R by one substitution;
  (b) random    -- uniform residual draws at several speed bounds;
  (c) hill-climb -- single-element replacement descent on M, many restarts.
Exact rational arithmetic; no floating point in any decision.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
import random, sys

def fn(x):
    r = x - (x.numerator//x.denominator)
    return r if r <= F(1,2) else 1-r

def gaps_of(T, n=8):
    iv=[]
    for v in T:
        w=F(1,n*v)
        for k in range(0,v+1):
            lo,hi=F(k,v)-w,F(k,v)+w
            if hi<=0 or lo>=1: continue
            iv.append((max(lo,F(0)),min(hi,F(1))))
    iv.sort(); out=[]; cur=F(0)
    for lo,hi in iv:
        if lo>cur: out.append((cur,lo))
        if hi>cur: cur=hi
    if cur<1: out.append((cur,F(1)))
    return out

def M(T, n=8):
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

def in_R(T):
    if len(set(T))!=7: return False
    if not all(any(v%q==0 for v in T) for q in (5,6,7,8)): return False
    g=0
    for v in T: g=gcd(g,v)
    return g==1

TIGHT=[(1,2,3,4,5,6,7),(1,2,3,4,5,7,12),(1,4,5,6,7,11,13)]

def probe_a(mult_cap=200):
    print("(a) targeted: one substitution turning each tight instance into R")
    best=[]
    for T in TIGHT:
        for i in range(7):
            for new in range(1, mult_cap+1):
                cand=tuple(sorted(T[:i]+T[i+1:]+(new,)))
                if not in_R(cand): continue
                best.append((M(cand),cand,T,T[i],new))
    best.sort()
    for m,c,T,old,new in best[:8]:
        print(f"    M={str(m):>10} ~{float(m):.6f}   {c}   (from {T}: {old} -> {new})")
    return best[0][0] if best else None

def probe_b(Vs, N, seed=11):
    print("(b) random residual draws")
    rng=random.Random(seed); out={}
    for V in Vs:
        bm=None; bt=None; got=0; tries=0
        while got<N and tries<N*400:
            tries+=1
            T=tuple(sorted(rng.sample(range(1,V+1),7)))
            if not in_R(T): continue
            got+=1
            m=M(T)
            if bm is None or m<bm: bm,bt=m,T
        out[V]=(bm,bt,got)
        print(f"    V={V:4d}  drawn={got:5d}  min M={str(bm):>10} ~{float(bm):.6f}  {bt}")
    return out

def probe_c(V, restarts, seed=23):
    print("(c) hill-climb, single-element replacement")
    rng=random.Random(seed); gbest=None; gT=None
    for _ in range(restarts):
        while True:
            T=tuple(sorted(rng.sample(range(1,V+1),7)))
            if in_R(T): break
        cur=M(T)
        improved=True
        while improved:
            improved=False
            for i in range(7):
                for new in range(1,V+1):
                    cand=tuple(sorted(T[:i]+T[i+1:]+(new,)))
                    if not in_R(cand): continue
                    m=M(cand)
                    if m<cur: cur,T,improved=m,cand,True
        if gbest is None or cur<gbest: gbest,gT=cur,T
    print(f"    V={V}  restarts={restarts}  best M={str(gbest)} ~{float(gbest):.6f}  {gT}")
    return gbest,gT

if __name__=="__main__":
    a=probe_a(); print()
    b=probe_b([40,80,160],1500); print()
    c=probe_c(60,12)
    print(f"\n1/8 = 0.125.  Smallest residual M seen across all probes: "
          f"{min([x for x in [a, min(v[0] for v in b.values()), c[0]] if x])}")
