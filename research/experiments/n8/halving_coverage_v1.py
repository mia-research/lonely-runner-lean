"""
How much of the residual case does Theorem P actually settle?  An honest measurement,
not an advertisement.

Theorem P' (refined).  T = 7 distinct positive integers.  Pick any m >= 2, put
D = {v in T : m | v}, X = T \\ D, x = |X|, and g = gcd(D)  (so g is a multiple of m
and Ubar_D is invariant under t -> t + 1/g).  If x >= 1 and

    SUM_{u in X}  gcd(u,g) * ( floor( g / (4*gcd(u,g)) ) + 1 )  <  g          (*)

then M(T) >= 1/(8-x) > 1/8, proved from LRC(8-x) alone -- never from LRC(8).

Derivation of (*): for u in X the shifts j/g, j in Z/g, move ||u t|| through
g/gcd(u,g) distinct values spaced gcd(u,g)/g, each attained gcd(u,g) times; a closed
arc of length 1/4 holds at most floor(g/(4 gcd(u,g))) + 1 of those values.  If the
total over X is < g, some shift j is missed by every u in X, the intersection
INT_j (Ubar_X + j/g) is empty, and Ubar_D alone must cover -- contradicting LRC(8-x)
applied to D/g.

Measured below: the fraction of the residual case (multiples of 5,6,7,8, gcd 1) that
(*) settles, at several speed bounds.  A small fraction is a small fraction; it is
reported as such.
"""
from itertools import combinations
from math import gcd
import sys

def settles(T, mmax=64):
    best=None
    for m in range(2, mmax+1):
        D=[v for v in T if v%m==0]
        if not D: continue
        X=[v for v in T if v%m]
        x=len(X)
        if x<1: continue
        g=0
        for v in D: g=gcd(g,v)
        tot=0
        for u in X:
            h=gcd(u,g)
            tot += h*(g//(4*h)+1)
            if tot>=g: break
        if tot<g:
            if best is None or x<best[1]: best=(m,x,g)
    return best

def main(V):
    n=0; hit=0; byx={}
    for T in combinations(range(1,V+1),7):
        if not all(any(v%q==0 for v in T) for q in (5,6,7,8)): continue
        d=0
        for v in T: d=gcd(d,v)
        if d!=1: continue
        n+=1
        s=settles(T)
        if s: hit+=1; byx[s[1]]=byx.get(s[1],0)+1
    print(f"V={V}: residual sets {n}; settled by Theorem P' {hit} ({100*hit/n:.3f}%)"
          f"; by x: {dict(sorted(byx.items()))}")

if __name__=="__main__":
    for V in (20,24,28,32): main(V)
