"""E121: is every band shape compatible with the lap assignment of one of the AP's global instants?
AP class c (odd): reading of rank i (AP index j = i + 1) on lap floor(j c / 8).  Compatibility is exact and pairwise
(TwoBlockN.lonely_eight_of_pairwise_laps): (8 k_i + 1) s_j <= (8 k_j + 7) s_i for all i, j.  Exhaustive to N, plus the
fine extremal shapes.  Integer arithmetic."""
import itertools, sys
from collections import Counter
N = int(sys.argv[1]) if len(sys.argv) > 1 else 40
CLASSES = list(range(1, 32, 2))
LAPS = {c: [(j * c) // 8 for j in range(1, 8)] for c in CLASSES}
def compat(T, k):
    return all((8 * k[i] + 1) * T[j] <= (8 * k[j] + 7) * T[i] for i in range(7) for j in range(7))
cnt = Counter(); miss = []
def classify(T):
    return next((c for c in CLASSES if compat(T, LAPS[c])), None)
for T in itertools.combinations(range(1, N + 1), 7):
    if not (7 * T[0] < T[-1] < 9 * T[0]): continue
    c = classify(T); cnt[c] += 1
    if c is None and len(miss) < 10: miss.append(T)
print("band sets to", N, ": least AP class compatible:", sorted(cnt.items(), key=lambda kv: (kv[0] is None, kv[0] or 0)))
print("   none of classes 1..31:", cnt[None], miss)
D1 = 27720
for shape in [(1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378), (1, 2.3091, 3.1726, 4.1869, 5.2226, 5.7861, 7.4385),
              (1, 2.5302, 3.2218, 4.1563, 4.531, 5.6544, 7.0302), (1, 3.15, 4.2099, 4.7242, 5.225, 5.7897, 7.4429)]:
    T = tuple(int(round(x * D1)) for x in shape)
    print("   extremal", shape, "-> least AP class", classify(T))
