"""
Exhaustive hunt for a TIGHT n=8 instance containing a multiple of 8.

Such a set is what "no tight instance contains a multiple of 8" forbids, and by the
ladder it is the ONLY thing standing between LRC(<=7) and an analytic LRC(8):
  * 8 divides no speed  ->  t = 1/8 gives M(T) >= 1/8.               [one line]
  * 8 divides some speed -> this search says none is tight up to V.

Method.  Two stages, so that no decision rests on floating point:
  stage 1 (float, with margin) -- sweep the closed bad intervals and keep only sets
          whose largest uncovered gap is < 1e-9.  A tight set has gap exactly 0 and
          float error here is ~1e-15, so this filter cannot discard a tight set.
  stage 2 (exact Fraction) -- re-decide every survivor by exact interval coverage.

Search space: 7-subsets of [1,V] with gcd 1 holding a multiple of 5, of 6, of 7 and
of 8 (the ladder's maximal levels; anything missing one is settled by t = 1/q).
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
import sys

def maxgap_float(T):
    iv=[]
    for v in T:
        w=1.0/(8*v)
        for k in range(0,v+1):
            lo,hi=k/v-w, k/v+w
            if hi<=0 or lo>=1: continue
            iv.append((lo if lo>0 else 0.0, hi if hi<1 else 1.0))
    iv.sort(); g=0.0; cur=0.0
    for lo,hi in iv:
        if lo>cur and lo-cur>g: g=lo-cur
        if hi>cur: cur=hi
    if 1.0-cur>g: g=1.0-cur
    return g

def covered_exact(T):
    iv=[]
    for v in T:
        w=F(1,8*v)
        for k in range(0,v+1):
            lo,hi=F(k,v)-w,F(k,v)+w
            if hi<=0 or lo>=1: continue
            iv.append((max(lo,F(0)),min(hi,F(1))))
    iv.sort(); cur=F(0)
    for lo,hi in iv:
        if lo>cur: return False
        if hi>cur: cur=hi
    return cur>=1

def main(V):
    n_lad=0; surv=[]; tight=[]
    for T in combinations(range(1,V+1),7):
        if not all(any(v%q==0 for v in T) for q in (5,6,7,8)): continue
        g=0
        for v in T: g=gcd(g,v)
        if g!=1: continue
        n_lad+=1
        if maxgap_float(T) < 1e-9:
            surv.append(T)
            if covered_exact(T): tight.append(T)
    print(f"V={V}: {n_lad} sets hold multiples of 5,6,7,8 with gcd 1")
    print(f"  stage-1 survivors (float max gap < 1e-9): {len(surv)}")
    print(f"  stage-2 EXACT tight instances containing a multiple of 8: {len(tight)}")
    for T in tight: print("     TIGHT WITH COARSE SPEED:", T)
    if not tight:
        print("  -> none. Claim holds over this range.")

if __name__=="__main__":
    main(int(sys.argv[1]) if len(sys.argv)>1 else 40)
