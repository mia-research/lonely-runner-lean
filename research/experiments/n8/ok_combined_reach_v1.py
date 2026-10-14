"""Union of the two structural criteria over Case 2: block criterion (a<=3) + odd-runner
collapse (a>=4).  Both produce an explicit witness; neither uses any measure estimate."""
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

BL = {0: (0, 4), 1: (1, 5), 2: (2, 6), 3: (3, 7)}

def block_crit(T):
    a = sum(1 for e in T if e % 2)
    if a >= 4: return False
    cuts = sorted({F(m, 8 * e) for e in T for m in range(0, 8 * e + 1)})
    for i in range(len(cuts) - 1):
        t = (cuts[i] + cuts[i + 1]) / 2
        hit = set()
        for e in T:
            if e % 2 == 0: hit |= blocked(e, t)
        full = {r for r in range(4) if set(BL[r]) <= hit}
        uO = sum(1 for r in (1, 3) if r not in full)
        uE = sum(1 for r in (0, 2) if r not in full)
        if a < 2 * max(uO, uE): return True
    return False

def collapse(T):
    odd = sorted([e for e in T if e % 2], reverse=True)
    if not odd: return False
    e1 = odd[0]
    cuts = sorted({F(1, 4 * e) for e in odd if F(1, 4 * e) < F(1, 2 * e1)}
                  | {F(0), F(1, 2 * e1)})
    for i in range(len(cuts) - 1):
        lo, hi = cuts[i], cuts[i + 1]
        if lo >= hi: continue
        t = (lo + hi) / 2
        hit = set()
        for e in T: hit |= blocked(e, t)
        if len(hit) < 8: return True
    return False

box = int(sys.argv[1]) if len(sys.argv) > 1 else 18
tuples = [T for T in combinations(range(1, box + 1), 7)
          if reduce(gcd, T) == 1 and any(e % 8 == 0 for e in T)]
step = max(1, len(tuples) // 900)
tuples = tuples[::step]
nb = nc = nu = 0
res = []
for T in tuples:
    b = block_crit(T); c = collapse(T)
    nb += b; nc += c; nu += (b or c)
    if not (b or c): res.append(T)
n = len(tuples)
print(f"Case-2 sample from [1..{box}] (every {step}th): {n} tuples")
print(f"  block criterion (a<=3)            : {nb:>4}  ({100*nb//n}%)")
print(f"  odd-runner collapse (near-0 window): {nc:>4}  ({100*nc//n}%)")
print(f"  UNION -- explicit witness, no estimate anywhere : {nu:>4}  ({100*nu//n}%)")
print(f"  residue                            : {n-nu:>4}  ({100*(n-nu)//n}%)")
print(f"  first few residual tuples: {res[:6]}")
