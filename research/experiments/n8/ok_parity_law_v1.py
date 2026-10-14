"""Is  (1-o_odd) + (1-o_even) = (1-u)  with the two EQUAL, a law or a coincidence?
Disjointness would say: wherever a residue is free, exactly ONE parity side is free."""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
from functools import reduce
import sys

def nrm(x):
    f = x - int(x)
    if f < 0: f += 1
    return min(f, 1 - f)

def blocked(e, t):
    return {j for j in range(8) if nrm(F(e) * (t + F(j, 8))) < F(1, 8)}

box = int(sys.argv[1]) if len(sys.argv) > 1 else 14
tuples = [T for T in combinations(range(1, box + 1), 7)
          if reduce(gcd, T) == 1 and any(e % 8 == 0 for e in T)]
disj = eq = both = 0
ex_eq = []
for T in tuples:
    cuts = sorted({F(m, 8 * e) for e in T for m in range(0, 8 * e + 1)} | {F(0), F(1)})
    ro = re = ru = F(0)
    for i in range(len(cuts) - 1):
        lo, hi = cuts[i], cuts[i + 1]; t = (lo + hi) / 2; w = hi - lo
        hit = set()
        for e in T: hit |= blocked(e, t)
        o_free = not {1, 3, 5, 7} <= hit
        e_free = not {0, 2, 4, 6} <= hit
        if o_free: ro += w
        if e_free: re += w
        if o_free or e_free: ru += w
    if ro + re == ru: disj += 1
    if ro == re: eq += 1
    if ro + re == ru and ro == re: both += 1
    elif ro == re: ex_eq.append(T)
n = len(tuples)
print(f"Case-2 tuples in [1..{box}] (exhaustive, exact): {n}")
print(f"  DISJOINT  (1-o_odd)+(1-o_even) = (1-u) : {disj} / {n}  ({100*disj//n}%)")
print(f"  EQUAL     (1-o_odd) = (1-o_even)       : {eq} / {n}  ({100*eq//n}%)")
print(f"  both                                    : {both} / {n}")
