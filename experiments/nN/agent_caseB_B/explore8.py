import random, math, sys
from fractions import Fraction as F
from core import *
from conditions import *
from collections import Counter
random.seed(9)
D=2520
def sample(mode):
    top=random.randint(9*D+1,24*D)
    if mode=='u': xs=random.sample(range(D+1,top),5)
    else:
        xs=set()
        while len(xs)<5:
            v=int(round(D*math.exp(random.uniform(0,math.log(top/D)))))
            if D<v<top: xs.add(v)
        xs=list(xs)
    return [F(1)]+sorted(F(x,D) for x in xs)+[F(top,D)]

def stair_general(rd, max_groups, skip):
    n=len(rd)
    def rec(start,u,lo,hi,g):
        if start>0: yield (lo,hi,start-1)
        if g>=max_groups or start>=n: return
        laps=[u] if (not skip or start==0) else range(u,u+skip+1)
        for lap in laps:
            for end in range(start,n):
                nlo=max(lo,F(8*lap+1)/rd[start]); nhi=min(hi,F(8*lap+7)/rd[end])
                if nlo>nhi: break
                yield from rec(end+1,lap+1,nlo,nhi,g+1)
    yield from rec(0,0,F(0),F(10**9),0)
def cond(rd,mg,skip):
    for lo,hi,p in stair_general(rd,mg,skip):
        rest=rd[p+1:]
        if not rest: return lo
        if lacunary_worst(rest,lo,hi): return nested_longest(rest,lo,hi)[0]
    return None
N=int(sys.argv[1])
for mode in ('u','log'):
    c=Counter()
    sets=[sample(mode) for _ in range(N)]
    for rd in sets:
        base=any(fn(rd) is not None for n,fn in DERIVED)
        c['D']+=base
        for mg in (3,4,5,7):
            for skip in (0,1,2):
                R=cond(rd,mg,skip)
                if R is not None:
                    assert lonely_at(rd,R)
                    c[(mg,skip)]+=1
                    if base or C1_escape(rd) is not None: pass
                if R is not None or C1_escape(rd) is not None: c[('+C1',mg,skip)]+=1
    print(mode,N,sorted(c.items(),key=str))
