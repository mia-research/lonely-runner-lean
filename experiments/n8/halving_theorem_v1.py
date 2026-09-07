"""
Theorem P (p-halving) at n = 8 -- verification, both directions.

STATEMENT.  T = 7 distinct positive integers.  M(T) = max_t min_{v in T} ||v t||.
Fix an integer p >= 2.  Let  X = {v in T : p does not divide v},  x = |X|,  D = T \ X.
    If  1 <= x <= 6  and  x*(floor(p/4) + 1) < p,   then   M(T) >= 1/(8-x)  >  1/8.

PROOF (5 lines).  Suppose M(T) <= 1/8, i.e. the closed bad sets
Ubar_v = {t : ||v t|| <= 1/8} cover the circle.  Ubar_D is invariant under t -> t + 1/p
because p | v for every v in D.  Hence for every j,  S^1 = Ubar_D u (Ubar_X + j/p),
and intersecting over j = 0..p-1,
    S^1 = Ubar_D  u  INT_j (Ubar_X + j/p).
For fixed t and u in X, {j : ||u(t - j/p)|| <= 1/8} has size at most floor(p/4)+1,
because p does not divide u, so j -> ju mod p is a bijection and the p points
u t - k/p are equally spaced by 1/p inside an arc of length 1/4.  So the p residues
j are covered by at most x*(floor(p/4)+1) < p of them: some j is missed, the
intersection is empty, and Ubar_D = S^1.  Writing D = p*D' and substituting t = s/p
gives M(D') <= 1/8 with |D'| = 7-x speeds -- contradicting LRC(8-x), which this
project has formally verified in Lean for 8-x = 4,5,6,7.  []

The theorem is only as strong as LRC(8-x); it does NOT assume LRC(8).

Checks run here:
 (1) FORWARD -- every T satisfying the hypothesis has M(T) >= 1/(8-x).  Exact.
 (2) SHARPNESS/CONTROL -- the three known tight instances must FAIL the hypothesis
     for every p (a tight instance has M = 1/8, so if any passed, the theorem is false).
     This control must fire: it is the one that would expose a wrong lemma.
 (3) CONSEQUENCE -- the divisibility profile a tight instance is forced into.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
import sys

def fn(x):
    r=x-(x.numerator//x.denominator); return r if r<=F(1,2) else 1-r

def gaps_of(T,n=8):
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

def M(T,n=8):
    gs=gaps_of(T,n)
    if not gs: return F(1,n)
    dens=set(2*v for v in T)
    for a,b in combinations(T,2): dens.add(a+b); dens.add(abs(a-b))
    dens.discard(0); best=F(1,n)
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

def hypothesis(T, pmax=64):
    """Best (p, x) satisfying the hypothesis, or None."""
    best=None
    for p in range(2,pmax+1):
        x=sum(1 for v in T if v%p)
        if 1<=x<=6 and x*(p//4+1)<p:
            if best is None or x<best[1]: best=(p,x)
    return best

TIGHT=[(1,2,3,4,5,6,7),(1,2,3,4,5,7,12),(1,4,5,6,7,11,13)]

print("(1) FORWARD: every T meeting the hypothesis must have M(T) >= 1/(8-x)")
bad=0; tested=0
for V in (14,18,22):
    for T in combinations(range(1,V+1),7):
        g=0
        for v in T: g=gcd(g,v)
        if g!=1: continue
        h=hypothesis(T)
        if h is None: continue
        p,x=h; tested+=1
        m=M(T)
        if m < F(1,8-x):
            bad+=1
            if bad<=5: print(f"    *** VIOLATION T={T} p={p} x={x} M={m} < 1/{8-x}")
    print(f"    V<={V}: {tested} sets met the hypothesis, {bad} violations")
print(f"  -> {'PASS' if bad==0 else 'FAIL'}\n")

print("(2) CONTROL: the three tight instances must FAIL the hypothesis for every p")
ok=True
for T in TIGHT:
    h=hypothesis(T,256)
    print(f"    {T}: hypothesis {'NOT met (correct)' if h is None else '*** MET '+str(h)+' -- LEMMA IS WRONG'}")
    ok &= (h is None)
print(f"  -> {'CONTROL FIRES as required' if ok else '*** CONTROL FAILED'}\n")

print("(3) CONSEQUENCE: divisibility profile forced on any tight instance")
print("    tightness requires, for every p >= 2:  x_p * (floor(p/4)+1) >= p")
for p in (2,3,4,5,6,7,8,9,11,13):
    need=min(x for x in range(1,8) if x*(p//4+1)>=p)
    print(f"      p={p:>2}: at least {need} speeds NOT divisible by {p}"
          f"  (i.e. at most {7-need} divisible)")
print("\n    the three tight instances, x_p = #{v : p does not divide v}:")
for T in TIGHT:
    print(f"      {str(T):>26}  " + "  ".join(f"x_{p}={sum(1 for v in T if v%p)}" for p in (2,3,5,7)))
