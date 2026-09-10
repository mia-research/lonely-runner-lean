"""Is the ODD-SIDE target 1-o a viable strengthening of 1-u?  1-o <= 1-u always
(O* contains O* cap E*), so the odd side is a STRONGER statement on a SIMPLER object
(4 residues, quarter states only).  The question is how much room it leaves."""
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

def measures(T):
    """exact (1-o, 1-e, 1-u) by cell decomposition; every breakpoint is m/(8e)."""
    cuts = sorted({F(m, 8 * e) for e in T for m in range(0, 8 * e + 1)} | {F(0), F(1)})
    ro = re = ru = F(0)
    for i in range(len(cuts) - 1):
        lo, hi = cuts[i], cuts[i + 1]
        t = (lo + hi) / 2
        hit = set()
        for e in T: hit |= blocked(e, t)
        w = hi - lo
        if not {1, 3, 5, 7} <= hit: ro += w
        if not {0, 2, 4, 6} <= hit: re += w
        if len(hit) < 8: ru += w
    return ro, re, ru

box = int(sys.argv[1]) if len(sys.argv) > 1 else 14
tuples = [T for T in combinations(range(1, box + 1), 7)
          if reduce(gcd, T) == 1 and any(e % 8 == 0 for e in T)]
print(f"Case-2 tuples in [1..{box}]: {len(tuples)}   (exhaustive, exact)")
worstO = worstU = None
zeroO = 0
for T in tuples:
    ro, re, ru = measures(T)
    best_side = max(ro, re)
    if worstO is None or best_side < worstO[0]: worstO = (best_side, T, ro, re)
    if worstU is None or ru < worstU[0]: worstU = (ru, T)
    if ro == 0 or re == 0: zeroO += 1
print(f"  min over tuples of (1-u)                 : {worstU[0]} = {float(worstU[0]):.6f}"
      f"   at {worstU[1]}")
print(f"  min over tuples of max(1-o_odd, 1-o_even): {worstO[0]} = {float(worstO[0]):.6f}"
      f"   at {worstO[1]}")
print(f"     its two sides: 1-o_odd = {float(worstO[2]):.6f}, 1-o_even = {float(worstO[3]):.6f}")
print(f"  tuples where one whole side is ALWAYS blocked (1-o = 0): {zeroO} / {len(tuples)}")
