#!/usr/bin/env python3
"""Residue-walk transitions (observation). State = (size rank of the flank x, opening index k); the walk
starts at (1, 0). A transition is (x, k) -> (x', k'), where x' is the next setter and k' its opening.
Per BHK case and overall: the distinct transition types and their counts, the distinct full paths
(as state sequences), and whether new types keep appearing as the range grows (types seen in [1,30]
versus [1,40]). Re-runs the walk from the sets in six_cascade_observe_v1.tsv. Exact."""
from fractions import Fraction as F
from collections import Counter, defaultdict
rows = []
for l in list(open("six_cascade_observe_v1.tsv"))[1:]:
    s, c = l.split("\t")[:2]
    rows.append((eval(s), c))
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def walk(S):
    t = F(1, 6 * S[0]); state = (1, 0); path = [state]
    while True:
        blk = [d for d in S if cd(d * t) < F(1, 6)]
        if not blk: return path, t
        best = None
        for d in blk:
            N = round(d * t); o = F(6 * N + 1, 6 * d)
            if best is None or o > best[0]: best = (o, d, N)
        t = best[0]; state = (S.index(best[1]) + 1, best[2]); path.append(state)
trans = defaultdict(Counter); paths = defaultdict(Counter); small = set(); big = set()
for S, c in rows:
    path, T = walk(S)
    paths[c][tuple(path)] += 1
    for a, b in zip(path, path[1:]):
        trans[c][(a, b)] += 1
        (small if S[-1] <= 30 else big).add((a, b))
for c in ("S8", "S5", "S6", "S7"):
    print(f"== {c}: distinct transition types {len(trans[c])}; distinct paths {len(paths[c])}")
    print("   top transitions:", trans[c].most_common(8))
    print("   top paths:", paths[c].most_common(6))
alltypes = set().union(*[set(t) for t in trans.values()])
print(f"overall distinct transition types: {len(alltypes)}; seen only in sets with max > 30: {len(big - small)}")
print("   max opening index k in any state:", max(max(k for (_, k) in ab) for ab in alltypes))
