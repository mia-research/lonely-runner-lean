"""Do the reduced triples beat 1/4?

For the self-similar family (5m1,5m2,5m3,e) the reduced problem is three runners m_i at
threshold 1/5.  The gap-criterion route needs a window of width 2*(S - 1/5)/m3 > 1/e where
S = sup_t min_i ||m_i t||.  With S = 1/4 (the LRC n=4 floor) that gives e > 10*m3.
A larger S shrinks the requirement:  e > m3 / (S - 1/5) ... precisely  e > m3/(S - 1/5) * 1/2 * 2,
i.e.  window = 2(S - 1/5)/m3 > 1/e   <=>   e > m3 / (2(S - 1/5)).

S is computed EXACTLY: min_i ||m_i t|| is piecewise linear with breakpoints at k/(2 m_i) and at
crossings k/(2(m_i +- m_j)), so a common denominator D = 2*lcm of all those places every vertex
on the grid t = k/D.
"""
import math
from itertools import combinations
from fractions import Fraction as F
from collections import Counter

def norm(x):
    fr = x - math.floor(x); return min(fr, 1 - fr)

def sup_min(ms):
    """Exact sup over t of min_i ||m_i t||, via the vertex grid."""
    dens = set()
    for m in ms: dens.add(2*m)
    for a, b in combinations(ms, 2):
        if a + b: dens.add(2*(a+b))
        if a != b: dens.add(2*abs(a-b))
    D = 1
    for d in dens: D = D * d // math.gcd(D, d)
    best = F(0)
    for k in range(D + 1):
        t = F(k, D)
        v = min(norm(F(m) * t) for m in ms)
        if v > best: best = v
    return best

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

hi = 60
ss = [c for c in combinations(range(1, hi+1), 4)
      if prim(c) and all(d % 5 == 0 for d in c[:-1]) and c[-1] > 4*c[0] and c[-1] > 15]
triples = sorted({tuple(d//5 for d in c[:-1]) for c in ss})
print(f"self-similar sets to [1,{hi}]: {len(ss)}   distinct reduced triples: {len(triples)}\n")
dist = Counter(); worst = []
for ms in triples:
    S = sup_min(ms)
    dist[S] += 1
    worst.append((S, ms))
worst.sort()
print(f"{'sup min ||m t||':>16} {'as float':>10} {'# triples':>10}")
for S in sorted(dist)[:10]:
    print(f"{str(S):>16} {float(S):>10.4f} {dist[S]:>10}")
print(f"   ... {len(dist)} distinct values in all")
print()
print(f"triples at the LRC floor S = 1/4 : {dist.get(F(1,4), 0)}")
print(f"triples with S > 3/10 = 0.3      : {sum(v for S, v in dist.items() if S > F(3,10))}"
      f"  ({100*sum(v for S,v in dist.items() if S > F(3,10))/len(triples):.1f}%)")
print()
print("the tightest triples:")
for S, ms in worst[:12]:
    need = F(ms[-1], 1) / (2*(S - F(1,5))) if S > F(1,5) else None
    print(f"   m = {str(ms):>14}  S = {str(S):>8} = {float(S):.4f}   route needs e > {float(need):.2f}"
          f"   (vs the free bound e > {5*ms[-1]})")
