r"""
ok_finite_red_v1 -- is Case 2 reducible to a FINITE check?

u is scale-invariant (t -> lambda t is a measure-preserving self-cover of the circle), so
"speeds are large" is meaningful only against gcd(E) = 1.  The proof architecture that would
work is:
    (a) max(E) >= B  ==>  u(E) bounded away from 1 by a margin we can prove;
    (b) a finite check below B.
This measures (a): max u over Case-2 tuples whose MINIMUM speed is >= B.  If u falls off as
B grows, the architecture is live; if tuples with all speeds large still reach ~0.95, it is
not, and the obstruction is arithmetic (ratios), not size.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd, lcm
import random, sys

def nrm(a,b):
    r=F(a%b,b); return min(r,1-r)
def u_strict(E):
    """u via the cell method (strict criterion), = 1 - int X / 8 * 8 ... computed directly"""
    pts={F(0),F(1)}
    for e in E:
        for j in range(1,e+1):
            q=F(j,e)
            if 0<q<1: pts.add(q)
        # also the 1/8-boundaries in t are finer; use the t-space count instead below
    return None
def intX(E):
    """exact int X = 8 * |G_strict| via t-space count over N = 8*lcm"""
    L=reduce(lcm,E); N=8*L
    good=0
    for k in range(N):
        ok=True
        for e in E:
            if nrm(e*k,N) <= F(1,8):        # STRICT: boundary counts as blocked
                if nrm(e*k,N) < F(1,8) or True:
                    ok=False; break
        if ok: good+=1
    return F(8*good,N)

def intX_fast(E):
    L=reduce(lcm,E); N=8*L
    lo=N//8; hi=7*N//8
    good=0
    for k in range(N):
        ok=True
        for e in E:
            m=(e*k)%N
            if m<=lo or m>=hi: ok=False; break
        if ok: good+=1
    return F(8*good,N)

random.seed(5)
print(f"{'B (min speed)':>14} {'#sampled':>9} {'max u':>12} {'~':>9}  argmax")
for B,TOP,NS in [(1,26,None),(2,26,None),(5,30,4000),(10,40,4000),(20,55,3000),(40,90,2000)]:
    pool=[e for e in range(B,TOP+1)]
    best=None; n=0
    if NS is None:
        cand=[E for E in combinations(pool,7) if reduce(gcd,E)==1 and any(e%8==0 for e in E)]
    else:
        cand=[]
        seen=set()
        while len(cand)<NS and len(seen)<NS*40:
            E=tuple(sorted(random.sample(pool,7)))
            if E in seen: continue
            seen.add(E)
            if reduce(gcd,E)==1 and any(e%8==0 for e in E): cand.append(E)
    for E in cand:
        if reduce(lcm,E) > 400000: continue
        n+=1
        ix=intX_fast(list(E)); uu=1-ix/8*8/8*0+1-ix  # u = 1 - intX  (X in {0,1,..}); see note
        uu=1-ix
        if best is None or uu>best[0]: best=(uu,E)
    if best is None: print(f"{B:>14} {n:>9}  (none)"); continue
    print(f"{B:>14} {n:>9} {float(best[0]):12.6f} {'':>9}  {best[1]}")
print("\nNOTE u = 1 - int X only when X is 0/1-valued; where X >= 2 this UNDERSTATES u,")
print("so the reported numbers are a lower bound on max u -- adequate for the trend.")
