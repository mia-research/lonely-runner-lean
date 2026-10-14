"""
Is the OPTIMAL WITNESS DENOMINATOR bounded on the residual case?

D(T) := min { q >= 2 : exists a with gcd(a,q)=1 and ||v*a/q|| >= 1/8 for all v in T }.

Why this is the question.  ||v * a/q|| >= 1/8 depends ONLY on v mod q.  So if
D(T) <= Q0 for every T in the residual case R, then LRC(8) on R is equivalent to a
statement about residue vectors modulo lcm(2..Q0) -- finitely many cases, checkable.
That would be a proof, not a search over speeds.

Why it is NOT forced (unlike the earlier 2-adic run).  Density of the rationals gives
only D(T) <~ 1/(width of the good set) ~ c * max(T), i.e. GROWTH.  So "bounded" is the
surprising outcome and "grows with max(T)" is the default.  The informative result here
is a bound; a growth curve refutes the route and costs one run.

Pre-committed reading, written before the numbers below were seen:
  * max D constant across the V ladder  -> route alive; record Q0 and go finite.
  * max D grows with V                  -> route dead as stated; report the growth.
  * some T with no q <= qmax            -> record it; it bounds nothing by itself.

Exact integer arithmetic; ||v a/q|| >= 1/8  <=>  8*min(r, q-r) >= q  with r = va mod q.
"""
from itertools import combinations
from math import gcd
import random, sys

def D(T, qmax):
    for q in range(2, qmax+1):
        for a in range(1, q):
            if gcd(a,q)!=1: continue
            ok=True
            for v in T:
                r=(v*a)%q
                if 8*min(r,q-r) < q: ok=False; break
            if ok: return q
    return None

def in_R(T):
    if not all(any(v%m==0 for v in T) for m in (5,6,7,8)): return False
    g=0
    for v in T: g=gcd(g,v)
    return g==1

def draw(V,rng):
    while True:
        T=tuple(sorted(rng.sample(range(1,V+1),7)))
        if in_R(T): return T

if __name__=="__main__":
    QMAX=400; N=600
    rng=random.Random(4242)
    print(f"residual case; N={N} sampled sets per V; qmax={QMAX}")
    print(f"{'V':>5} {'max D':>6} {'mean D':>7} {'unresolved':>11}   worst set")
    for V in (20,40,80,160,320,640):
        mx=0; tot=0; bad=0; worst=None
        for _ in range(N):
            T=draw(V,rng); d=D(T,QMAX)
            if d is None: bad+=1; continue
            tot+=d
            if d>mx: mx,worst=d,T
        print(f"{V:>5} {mx:>6} {tot/(N-bad):>7.1f} {bad:>11}   {worst}", flush=True)
