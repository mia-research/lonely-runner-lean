"""Two sound, non-circular, non-search certificates, on complementary domains:
   a <= 3 : block criterion  a < 2 max(u_O,u_E)   (structural)
   a >= 4 : union bound      |C| > sum |B*_e|     (measure inequality)"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
from functools import reduce
import sys, importlib.util
spec = importlib.util.spec_from_file_location("u", "experiments/n8/ok_collapse_union_v1.py")
u = importlib.util.module_from_spec(spec); spec.loader.exec_module(u)
F_, blocked, ODD, v2 = F, u.blocked, u.ODD, u.v2
BL = {0:(0,4), 1:(1,5), 2:(2,6), 3:(3,7)}
LVL = F(1,8)
def nrm(x):
    f = x-int(x)
    if f < 0: f += 1
    return min(f, 1-f)

def block_crit(T):
    a = sum(1 for e in T if e % 2)
    if a >= 4: return False
    for lo, hi in u.cells(T):
        t = (lo+hi)/2
        hit = set()
        for e in T:
            if e % 2 == 0: hit |= blocked(e, t)
        full = {r for r in range(4) if set(BL[r]) <= hit}
        uO = sum(1 for r in (1,3) if r not in full); uE = sum(1 for r in (0,2) if r not in full)
        if a < 2*max(uO, uE): return True
    return False

box = int(sys.argv[1]) if len(sys.argv) > 1 else 16
tuples = [T for T in combinations(range(1, box+1), 7)
          if reduce(gcd, T) == 1 and any(e % 8 == 0 for e in T)]
tuples = tuples[::max(1, len(tuples)//350)]
from collections import Counter
tot, hit = Counter(), Counter()
resid = []
for T in tuples:
    a = sum(1 for e in T if e % 2); tot[a] += 1
    mC, mB, _ = u.analyse(list(T))
    if (a <= 3 and block_crit(list(T))) or mC > mB: hit[a] += 1
    else: resid.append((a, T))
n = len(tuples)
print(f"PAIR of certificates over {n} Case-2 tuples from [1..{box}]\n")
print("   a   tuples   settled")
for a in sorted(tot):
    print(f"  {a:>2}   {tot[a]:>6}   {hit[a]:>7}")
print(f"\n  total settled : {sum(hit.values())} / {n}  ({100*sum(hit.values())//n}%)")
print(f"  residue       : {len(resid)}   {[T for _, T in resid[:6]]}")
print(f"  residue by a  : {dict(Counter(a for a, _ in resid))}")
