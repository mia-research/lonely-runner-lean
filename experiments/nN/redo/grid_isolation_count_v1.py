# How many lonely instants does a grid have per period?  Integer readings S (7 distinct positive), lonely set L(S) in [0,1]
# (period 1; t and 1-t symmetric).  Exact: reading a is clear on [(8k+1)/(8a), (8k+7)/(8a)], k = 0..a-1.
import itertools, sys
from fractions import Fraction as F
def clear_intervals(a):
    return [(F(8*k+1, 8*a), F(8*k+7, 8*a)) for k in range(a)]
def intersect(A, B):
    out = []; i = j = 0
    while i < len(A) and j < len(B):
        lo = max(A[i][0], B[j][0]); hi = min(A[i][1], B[j][1])
        if lo <= hi: out.append((lo, hi))
        if A[i][1] < B[j][1]: i += 1
        else: j += 1
    return out
def merge(L):
    out = []
    for lo, hi in sorted(L):
        if out and lo <= out[-1][1]: out[-1] = (out[-1][0], max(out[-1][1], hi))
        else: out.append((lo, hi))
    return out
def lonely_set(S):
    L = clear_intervals(S[0])
    for a in S[1:]:
        L = intersect(L, clear_intervals(a))
        if not L: return []
    return merge(L)
def describe(S):
    L = lonely_set(S); pts = [x for x, y in L if x == y]; ivs = [(x, y) for x, y in L if x < y]
    return L, pts, ivs, sum((y - x for x, y in ivs), F(0))
if __name__ == "__main__":
    L, pts, ivs, m = describe([1, 2, 3, 4, 5, 6, 7])
    print("AP 1..7: components", len(L), "isolated points", [str(p) for p in pts], "intervals", len(ivs), "measure", m)
    for c in (3, 5, 7):
        L, pts, ivs, m = describe([c * x for x in range(1, 8)])
        print("%d*AP: components %d, points %d, intervals %d, measure %s; first points %s" % (c, len(L), len(pts), len(ivs), m, [str(p) for p in pts[:6]]))
    # complete grids: residues mod 8 are exactly {1..7}, laps q in 0..Q-1
    Q = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    from collections import Counter
    cnt = Counter(); worst = []; n = 0; with_interval = 0
    for qs in itertools.product(range(Q), repeat=7):
        S = sorted(r + 8 * q for r, q in zip(range(1, 8), qs))
        if len(set(S)) < 7: continue
        n += 1
        L, pts, ivs, m = describe(S)
        odd = [F(a, 8) for a in (1, 3, 5, 7)]
        assert all(any(x <= o <= y for x, y in L) for o in odd), S    # the four class instants are always lonely
        cnt[(len(pts), len(ivs))] += 1
        if ivs: with_interval += 1
        if len(L) > 4 and len(worst) < 6: worst.append((S, len(L), len(pts), len(ivs)))
    print("complete grids (residues 1..7, laps < %d): %d sets; the four a/8 (a odd) lonely in all." % (Q, n))
    print(" (isolated points, intervals) -> number of sets:", sorted(cnt.items())[:20])
    print(" sets with some lonely interval (positive length):", with_interval)
    print(" examples with more than 4 components:", worst)
