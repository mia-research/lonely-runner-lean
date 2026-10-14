"""Three-way method control: A (exact interval merge) vs B (exact BSM) vs C (integer BSM).

Reconstructs the control asserted in docs/n8/METHODS_AUDIT_2026_09_12.md S2, which was
recorded as [VERIFIED] (495 sets, 0 disagreements) with no saved script.  The exact 495-set
population is not recoverable, so this re-runs the CLAIM (the three agree, and BSM reports no
cell anomalies) over a freshly generated population.

A: resolution_law.py good()      -- merge open bad intervals, count good components
B: bsm_transit.py  bsm_good()    -- boundary points + open cells, 3 probes per cell
C: bsm_fast.py     bsm_count()   -- same, over the common denominator 16*lcm(D), integer
"""
import random, sys
from fractions import Fraction as F
from math import gcd
from functools import reduce

# ---- A -------------------------------------------------------------------
def bad_intervals(s):
    out=[]
    for k in range(0,s+1):
        lo,hi=max(F(8*k-1,8*s),F(0)),min(F(8*k+1,8*s),F(1))
        if lo<hi: out.append((lo,hi))
    return out

def good_A(S):
    iv=[]
    for s in S: iv+=bad_intervals(s)
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

# ---- B -------------------------------------------------------------------
def boundary_set(D):
    B={F(0),F(1)}
    for d in D:
        for k in range(0,d+1):
            for s in (-1,1):
                t=F(8*k+s,8*d)
                if 0<=t<=1: B.add(t)
    return sorted(B)

def lonely_at(D,t):
    for d in D:
        r=(d*t)%1
        if min(r,1-r)<F(1,8): return False
    return True

def bsm_good_B(D):
    B=boundary_set(D); anomalies=0; cell_ok=[]
    for i in range(len(B)-1):
        lo,hi=B[i],B[i+1]
        vals=[lonely_at(D,lo+(hi-lo)*F(p,4)) for p in (1,2,3)]
        if len(set(vals))!=1: anomalies+=1
        cell_ok.append(vals[1])
    pt_ok=[lonely_at(D,t) for t in B]
    out=[]; cur=None
    for i,t in enumerate(B):
        left =cell_ok[i-1] if i>0 else False
        right=cell_ok[i]   if i<len(cell_ok) else False
        if pt_ok[i]:
            if cur is None: cur=t
            if not right: out.append((cur,t)); cur=None
        else:
            if cur is not None: out.append((cur,B[i-1] if not left else t)); cur=None
    if cur is not None: out.append((cur,B[-1]))
    out=[(a,b) for a,b in out if not(a==b==F(0)) and not(a==b==F(1))]
    return out,anomalies

# ---- C -------------------------------------------------------------------
def _lcm(a,b): return a*b//gcd(a,b)

def bsm_count_C(D):
    L=reduce(_lcm,D); M=16*L; B={0,M}
    for d in D:
        step=M//d
        for k in range(0,d+1):
            for s in (-1,1):
                t=k*step+s*(step//8)
                if 0<=t<=M: B.add(t)
    B=sorted(B)
    def ok(n):
        for d in D:
            r=(d*n)%M
            if 8*min(r,M-r)<M: return False
        return True
    pt=[ok(t) for t in B]
    cell=[ok((B[i]+B[i+1])//2) for i in range(len(B)-1)]
    n=0; inrun=False
    for i in range(len(B)):
        right=cell[i] if i<len(cell) else False
        if pt[i] and not inrun: n+=1; inrun=True
        if inrun and not right: inrun=False
    return n

# ---- population ----------------------------------------------------------
def primitive_sets(n_sets, size, span, rng):
    out=set()
    guard=0
    while len(out)<n_sets and guard<n_sets*200:
        guard+=1
        D=tuple(sorted(rng.sample(range(1,span+1),size)))
        if reduce(gcd,D)==1: out.add(D)
    return sorted(out)

def main():
    rng=random.Random(20260912)
    spans=[10,20,30,40,50,60,70]
    pop=[]
    for sp in spans:
        for size in (2,3,5,7):
            if size<=sp:
                pop+=primitive_sets(18,size,sp,rng)
    pop=sorted(set(pop))
    dAB=dBC=dAC=anom=0; bad=[]
    for D in pop:
        D=list(D)
        a=len(good_A(D))
        gb,an=bsm_good_B(D); b=len(gb)
        c=bsm_count_C(D)
        anom+=an
        if a!=b: dAB+=1; bad.append(("A!=B",D,a,b,c))
        if b!=c: dBC+=1; bad.append(("B!=C",D,a,b,c))
        if a!=c: dAC+=1; bad.append(("A!=C",D,a,b,c))
    print(f"population: {len(pop)} primitive constraint sets, sizes 2/3/5/7, spans {spans}")
    print(f"A vs B disagreements: {dAB}")
    print(f"B vs C disagreements: {dBC}")
    print(f"A vs C disagreements: {dAC}")
    print(f"BSM cell anomalies  : {anom}")
    for r in bad[:12]: print("  MISMATCH", r)
    return 1 if (dAB or dBC or dAC or anom) else 0

if __name__=="__main__":
    sys.exit(main())
