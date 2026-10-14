#!/usr/bin/env python3
"""Enumerate bad covers for (k,p), to characterise WHY some p fail."""
from itertools import combinations
from math import gcd
from functools import reduce

def setup(k, p):
    N=(k+1)*p; H=N//2
    V=[v for v in range(1,H+1) if v%p!=0]
    J=list(range(1,H+1)); idx={j:i for i,j in enumerate(J)}
    cov={}
    for v in V:
        m=0
        for j in J:
            r=(j*v)%N
            if r<p or r>N-p: m|=1<<idx[j]
        cov[v]=m
    return N,H,V,J,cov,(1<<len(J))-1

def all_bad_covers(k, p, cap=50):
    N,H,V,J,cov,FULL = setup(k,p)
    def gcd_ok(t): return all(reduce(gcd,S+(N,))==1 for S in combinations(t,k-1))
    out=[]
    def rec(chosen, used, mask):
        if len(out)>=cap: return
        if mask==FULL:
            if gcd_ok(tuple(chosen)): out.append(tuple(chosen))
            return
        if len(chosen)==k: return
        low=(~mask)&FULL; lb=(low&-low).bit_length()-1
        for i,v in enumerate(V):
            if i in used: continue
            if (cov[v]>>lb)&1:
                rec(chosen+[v], used|{i}, mask|cov[v])
                if len(out)>=cap: return
    rec([],set(),0)
    return N,H,out

if __name__=="__main__":
    import sys
    k=int(sys.argv[1])
    for p in [int(x) for x in sys.argv[2:]]:
        N,H,covers = all_bad_covers(k,p,cap=12)
        print(f"k={k} p={p}  N={N} H={H}  bad covers found: {len(covers)}")
        for c in covers[:12]:
            print("   ", c, "   v/p ratios:", [round(v/p,3) for v in c])
