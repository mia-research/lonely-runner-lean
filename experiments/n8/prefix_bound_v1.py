#!/usr/bin/env python3
"""Minimum number of speeds needed to cover only the PREFIX j=1..J, at (k,p).
If that minimum ever exceeds k, no bad cover exists and Lemma 7 applies --
replacing the exhaustive search by a much smaller prefix computation."""
import sys
from functools import lru_cache

def prefix_min_cover(k, p, J, cap=None):
    n=k+1; N=n*p; H=N//2
    if cap is None: cap=k+1          # we only care whether it exceeds k
    V=[v for v in range(1,H+1) if v%p!=0]
    targets=list(range(1,J+1))
    idx={j:i for i,j in enumerate(targets)}
    FULL=(1<<len(targets))-1
    cov={}
    for v in V:
        m=0
        for j in targets:
            r=(j*v)%N
            if r<p or r>N-p: m|=1<<idx[j]
        if m: cov[v]=m
    # dedupe identical coverage masks
    masks=sorted(set(cov.values()), key=lambda m:-bin(m).count('1'))
    best=[cap+1]
    def rec(mask, used):
        if mask==FULL:
            best[0]=min(best[0],used); return
        if used+1>=best[0]: return
        low=(~mask)&FULL; lb=(low&-low).bit_length()-1
        for m in masks:
            if (m>>lb)&1:
                rec(mask|m, used+1)
    rec(0,0)
    return best[0]

if __name__=="__main__":
    k=int(sys.argv[1]); p=int(sys.argv[2])
    for J in [int(x) for x in sys.argv[3:]]:
        r=prefix_min_cover(k,p,J)
        verdict = "EXCEEDS k=%d -> NO bad cover"%k if r>k else "<= k"
        print("  J=%4d : min speeds to cover 1..J = %s   %s"%(J, r if r<=k+1 else ">%d"%k, verdict), flush=True)
