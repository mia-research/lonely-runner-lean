#!/usr/bin/env python3
"""
(1,2) windowed pentagon kill: does the part-1 window satisfy the (43) cut in core2?
==================================================================================
Part-1 exc_1_2_pentkill: line Y={2X}, window X in [Xv - 1/q, Xv],
Xv = 1/6 + (q-p)*M/2, M = (s-q)/(3qs), requires s >= q+3 (wide branch).
(43) cut: Y = 2X <= 5/12 - p/(3q)  <=>  X <= Xcut2 := 5/24 - p/(6q).

Rigidity (1,2): 2r = 2q + p  (p even).  core2: 6p < q, q >= 18.
Questions:
 (A) Is Xv <= Xcut2 (whole part-1 window already in P')?
 (B) If not, does [Xv-1/q, min(Xv,Xcut2)] still have width >= 1/q (grid pt survives)?
 (C) actual grid point on the line in the cut window?
Also handle the special branch s = q+2 (part-1 has a separate `special`).
"""
import math
def frac(x): return x - math.floor(x)

def run(qmax=90):
    tot=0; A=0; B=0; Cok=0; cfail=[]
    for q in range(7,qmax+1):
        for p in range(1,q):
            if p%2!=0: continue            # (1,2) needs p even
            if math.gcd(p,q)!=1: continue
            if 6*p>=q: continue            # core2
            if (2*q+p)%2!=0: continue
            r=(2*q+p)//2
            if not (q<r and 2*r<3*q): continue
            if math.gcd(r,q)!=1: continue
            for s in range(q+3,3*q+1):      # wide branch s>=q+3
                if s<=r: continue
                tot+=1
                M=(s-q)/(3*q*s)
                Xv=1/6+(q-p)*M/2
                Xcut2=5/24 - p/(6*q)
                if Xv<=Xcut2+1e-12: A+=1
                top=min(Xv,Xcut2)
                lo=Xv-1/q
                if top-lo>=1/q-1e-12: B+=1
                # actual grid point: X=frac(r*m/(2q)), m odd, on line Y={2X}, in [lo,top]
                found=False
                for m in range(1,2*q,2):
                    X=frac(r*m/(2*q))
                    if lo-1e-9<=X<=top+1e-9 and X<1/2:
                        # verify Y={2X}=2X (no wrap) i.e. X<1/2
                        found=True; break
                if found: Cok+=1
                else: cfail.append((q,p,r,s,round(lo,4),round(top,4)))
    print(f"(1,2) wide branch (s>=q+3): completions={tot}")
    print(f"  (A) Xv<=Xcut2 (whole window in P'): {A}")
    print(f"  (B) cut window width>=1/q:          {B}")
    print(f"  (C) actual grid pt in cut window:   {Cok}  (fail {len(cfail)})")
    if cfail: print("   fails:", cfail[:10])

run()
