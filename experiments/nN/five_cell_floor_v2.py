"""five_cell_floor_v1 with its floating-point grid check replaced by the Boundary Set Method.

v1 cross-checked the minimiser on a 2,000,000-point float grid.  The framework distrusts floats:
BSM evaluates the boundary points (8k +- 1)/(8d) and the open cells separately, over a common
integer denominator, and so reads the isolation points themselves.  Here the BSM point set and test
of experiments/n8/bsm_fast.py (integer arithmetic, M = 16*lcm, 8*min(r, M-r) >= M inclusive) is
extended to report component lengths, and applied to EVERY 5-set that the exact interval merge of v1
places below 1/4, plus the progressions.  Agreement is required exactly, as fractions.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
from functools import reduce

def merge_longest(S, n=8):                       # v1's exact interval merge
    r = F(1, n); bad = []
    for d in S:
        for j in range(d + 1): bad.append((F(j, d) - r / d, F(j, d) + r / d))
    bad.sort(); out = []; cur = F(0)
    for a, b in bad:
        if a > cur: out.append((cur, a))
        elif a == cur and a > 0 and (not out or out[-1][1] != cur): out.append((cur, cur))
        cur = max(cur, b)
        if cur >= 1: break
    return max((b - a for a, b in out if 0 < a and b < 1), default=F(0))

def bsm_longest(S):                              # bsm_fast.py's point set and ok(), with lengths
    L = reduce(lambda a, b: a * b // gcd(a, b), S); M = 16 * L; B = {0, M}
    for d in S:
        step = M // d
        for k in range(d + 1):
            for s in (-1, 1):
                t = k * step + s * (step // 8)
                if 0 <= t <= M: B.add(t)
    B = sorted(B)
    def ok(x): return all(8 * min((d * x) % M, M - (d * x) % M) >= M for d in S)
    best = 0; start = None
    for i, b in enumerate(B):
        if ok(b):
            if start is None: start = b
            nxt = B[i + 1] if i + 1 < len(B) else None
            if nxt is not None and ok((b + nxt) // 2) and ok(nxt): continue
            best = max(best, b - start); start = None
        else: start = None
    return F(best, M)

low = sorted((merge_longest(S) * max(S), S) for S in combinations(range(1, 31), 5)
             if reduce(gcd, S) == 1 and merge_longest(S) * max(S) < F(1, 4))
checks = low + [(merge_longest(S) * max(S), S) for S in [(1, 2, 3, 4, 5), (2, 4, 6, 8, 10)]]
dis = [(S, v, bsm_longest(S) * max(S)) for v, S in checks if bsm_longest(S) * max(S) != v]
print(f"primitive 5-subsets of [1,30] below 1/4 (exact merge): {len(low)}")
print(f"BSM vs exact merge on those {len(low)} and the two progressions: {len(dis)} disagreements {dis}")
for v, S in low[:6]: print(f"  {S}: longest*max = {v} (BSM {bsm_longest(S) * max(S)})")
