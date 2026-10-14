"""The window criterion applied to the WHOLE residue, not just the self-similar core.

Frame: the flank openings are t = (5j+1)/(5e), spacing 1/e.  The flank itself sits at exactly
1/5 there, so the window must keep only the NON-FLANK disparities lonely.  With
      S = sup_t min over non-flank d of ||d t||,
the window has width 2(S - 1/5)/d_max and beats the spacing when  e > d_max / (2(S - 1/5)).
Since d_max < e is free, the criterion is automatic when 2(S - 1/5) >= 1, i.e. S >= 7/10.

The self-similar case escaped with S >= 3/10 because its reduction to modulus e replaced d_max
by m_3 = d_max/5 -- a factor-five gain.  Question: how far does the raw criterion reach on the
mixed classes, and can a partial reduction recover the factor?
"""
import math
from itertools import combinations
from fractions import Fraction as F

def norm(x):
    fr = x - math.floor(x); return min(fr, 1 - fr)

def sup_min(ms, _c={}):
    key = tuple(ms)
    if key in _c: return _c[key]
    dens = {2*m for m in ms}
    for a, b in combinations(ms, 2):
        dens.add(a+b)
        if a != b: dens.add(abs(a-b))
    best = F(0)
    for q in dens:
        for k in range(0, q//2 + 2):
            t = F(k, q)
            if t > F(1,2): continue
            v = min(norm(F(m) * t) for m in ms)
            if v > best: best = v
    _c[key] = best
    return best

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

def in_residue(c):
    e = c[-1]
    return any(d % 5 == 0 for d in c[:-1]) and e > 4*c[0] and e > 15

hi = 45
sets = [c for c in combinations(range(1, hi+1), 4) if prim(c) and in_residue(c)]
print(f"residue sets in [1,{hi}]: {len(sets)}\n")
from collections import Counter
res = Counter(); cov = Counter()
for c in sets:
    e = c[-1]; nf = c[:-1]
    k5 = sum(1 for d in nf if d % 5 == 0)
    S = sup_min(nf)
    res[k5] += 1
    if S > F(1,5) and F(max(nf)) / (2*(S - F(1,5))) < e: cov[k5] += 1
print(f"{'# inner 5-mults':>16} {'sets':>8} {'raw window closes':>19} {'share':>8}")
for k in sorted(res):
    print(f"{k:>16} {res[k]:>8} {cov[k]:>19} {100*cov[k]/res[k]:>7.1f}%")
tot = sum(res.values()); tc = sum(cov.values())
print(f"{'TOTAL':>16} {tot:>8} {tc:>19} {100*tc/tot:>7.1f}%")
print()
print("=== what S would be needed, vs what S is ===")
need = []
for c in sets[:0]: pass
Ss = Counter()
for c in sets:
    nf = c[:-1]; e = c[-1]
    S = sup_min(nf)
    # required S for the raw criterion: S > 1/5 + d_max/(2e)
    req = F(1,5) + F(max(nf), 2*e)
    Ss[(S >= req)] += 1
print(f"   sets with S >= 1/5 + d_max/(2e): {Ss[True]} of {tot}  ({100*Ss[True]/tot:.1f}%)")
print(f"   mean S over the residue        : {float(sum(sup_min(c[:-1]) for c in sets)/tot):.4f}")
