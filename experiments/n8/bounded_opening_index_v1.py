"""Does every difference set have a free flank opening at a SMALL opening index?

If there is an explicit K with: every seven-difference set has a flank e and an opening k <= K at
which all others are clear, then Existence at order 8 is a COMPACT problem. Normalise d_max = 1;
the conditions for fixed (e, k) are finitely many exact inequalities in the six ratios, so coverage
becomes a finite semialgebraic question rather than an unbounded search.

Measured here: max over sets of the MINIMAL opening index that works.
"""
import sys
from itertools import combinations
def blocked(d, e, k):
    r = (d * (8 * k + 1)) % (8 * e)
    return min(r, 8 * e - r) < e
def min_opening(D):
    best = None
    for e in D:
        others = [d for d in D if d != e]
        for k in range(e):
            if all(not blocked(d, e, k) for d in others):
                if best is None or k < best[0]: best = (k, e)
                break
    return best
if __name__ == '__main__':
    DMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    worst = None; hist = {}; none_ = 0
    tot = 0
    for sub in combinations(range(1, DMAX + 1), 7):
        tot += 1
        r = min_opening(list(sub))
        if r is None: none_ += 1; continue
        k = r[0]
        hist[k] = hist.get(k, 0) + 1
        if worst is None or k > worst[0]: worst = (k, list(sub), r[1])
    print(f"exhaustive 7-subsets of 1..{DMAX}: {tot} sets, {none_} with no free flank")
    print(f"  distribution of the minimal opening index: {dict(sorted(hist.items()))}")
    print(f"  WORST CASE: k = {worst[0]} for {worst[1]} at flank {worst[2]}")
