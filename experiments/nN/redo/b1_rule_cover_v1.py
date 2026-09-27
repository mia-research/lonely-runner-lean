"""E119: which scale-free block rules (flank = the reading of rank r, lap K) are needed across the band B1
(7 d1 < d7 < 9 d1)?  For each set, all (r, K) with K <= 4 whose block condition holds; then a greedy smallest
family of (r, K) covering every set.  Exact integer arithmetic.  This finds the rules; the covering is then to be
derived, not enumerated."""
import itertools
from collections import Counter
N = 40
def ok(T, e, K):   # every reading's position (8K+1) d / e in some block [8k+1, 8k+7]
    for d in T:
        p8 = (8 * K + 1) * d          # position * e
        k = p8 // (8 * e)             # lap
        if not ((8 * k + 1) * e <= p8 <= (8 * k + 7) * e): return False
    return True
sets = []
for T in itertools.combinations(range(1, N + 1), 7):
    if not (7 * T[0] < T[-1] < 9 * T[0]): continue
    sets.append(frozenset((r, K) for K in range(0, 5) for r, e in enumerate(T) if ok(T, e, K)))
print("B1 sets to", N, ":", len(sets), "  with no rule K<=4:", sum(1 for s in sets if not s))
left = list(sets); chosen = []
while left:
    c = Counter(p for s in left for p in s)
    best, n = c.most_common(1)[0]
    chosen.append((best, n)); left = [s for s in left if best not in s]
    if len(chosen) > 12: break
print("greedy cover (rank r = 0 slowest .. 6 fastest, lap K): newly covered")
for (r, K), n in chosen: print("   r=%d K=%d  %d" % (r, K, n))
print("uncovered after these:", len(left))
