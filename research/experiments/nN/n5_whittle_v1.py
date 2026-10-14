"""Whittling: the route closes from the FREE bound exactly when S > 3/10.

window = 2(S - 1/5)/m3 > 1/e   <=>   e > m3 / (2(S - 1/5)).
The difference set gives e > 5*m3 for free.  So the route needs nothing extra iff
      m3 / (2(S - 1/5)) <= 5*m3   <=>   S >= 1/5 + 1/10 = 3/10.
So S > 3/10 closes automatically; S <= 3/10 is the residue of the residue.
"""
import math
from itertools import combinations
from fractions import Fraction as F
from collections import Counter

def norm(x):
    fr = x - math.floor(x); return min(fr, 1 - fr)

def sup_min(ms, _cache={}):
    if ms in _cache: return _cache[ms]
    dens = {2*m for m in ms}
    for a, b in combinations(ms, 2):
        dens.add(2*(a+b))
        if a != b: dens.add(2*abs(a-b))
    D = 1
    for d in dens: D = D * d // math.gcd(D, d)
    best = F(0)
    for k in range(D + 1):
        v = min(norm(F(m*k, D)) for m in ms)
        if v > best: best = v
    _cache[ms] = best
    return best

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

for hi in (50, 60, 70):
    ss = [c for c in combinations(range(1, hi+1), 4)
          if prim(c) and all(d % 5 == 0 for d in c[:-1]) and c[-1] > 4*c[0] and c[-1] > 15]
    covered = 0; hard = Counter()
    for c in ss:
        ms = tuple(d//5 for d in c[:-1])
        S = sup_min(ms)
        if S >= F(3,10): covered += 1
        else: hard[ms] += 1
    print(f"[1,{hi}]  self-similar sets {len(ss):>5}   S >= 3/10 (route closes) {covered:>5}"
          f"  ({100*covered/len(ss):5.1f}%)   remaining {len(ss)-covered:>4}")
    print(f"          hard triples (S < 3/10): {dict(sorted(hard.items(), key=lambda p:-p[1]))}")
print()
print("=== the hard triples, and what each actually needs ===")
hardset = set()
for c in [c for c in combinations(range(1,71), 4)
          if prim(c) and all(d%5==0 for d in c[:-1]) and c[-1] > 4*c[0] and c[-1] > 15]:
    ms = tuple(d//5 for d in c[:-1])
    if sup_min(ms) < F(3,10): hardset.add(ms)
print(f"{'triple':>14} {'S':>8} {'route needs e >':>16} {'free bound e >':>15} {'shortfall':>10}")
for ms in sorted(hardset):
    S = sup_min(ms)
    need = F(ms[-1]) / (2*(S - F(1,5)))
    print(f"{str(ms):>14} {str(S):>8} {float(need):>16.2f} {5*ms[-1]:>15} {float(need)-5*ms[-1]:>10.2f}")
