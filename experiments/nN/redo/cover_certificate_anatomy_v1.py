"""E125: what the band cover's certificates say.  For each empty leaf of band_cover_tree_v3, rebuild its piece and read
its Farkas certificate: how many rows carry weight, and what those rows are (band ordering rows s_i <= s_{i+1}, the
s7 range, or walls of which cones and which runner pairs).  Also the containment certificates' support sizes."""
import json
from fractions import Fraction as F
from collections import Counter
N = 6
def root():
    rows = []
    for i in range(N - 1):
        a = [0] * N; a[i] = 1; a[i + 1] = -1; rows.append((a, F(0), False, ('order', i + 1, i + 2)))
    a = [0] * N; a[5] = 1; rows.append((a, F(8), False, ('s7<=9',)))
    a = [0] * N; a[5] = -1; rows.append((a, F(-6), False, ('s7>=7',)))
    return rows
def wall(k, i, j):
    a = [0] * N
    if j: a[j - 1] += 8 * k[i] + 1
    if i: a[i - 1] -= 8 * k[j] + 7
    return a, F(8 * k[j] + 7 - (8 * k[i] + 1))
tree = json.load(open('band_cover_tree_v3.json'))
stack = [((), root())]; supp = Counter(); kinds = Counter(); pairs = Counter(); csupp = Counter()
while stack:
    path, P = stack.pop(); rec = tree[','.join(map(str, path))]
    if rec['kind'] == 'empty':
        d = rec['cert'][1]; idx = [int(t) for t in d if int(t) < len(P)]
        supp[len(idx)] += 1
        kinds[tuple(sorted(P[t][3][0] if P[t][3][0] in ('order', 's7<=9', 's7>=7') else 'wall' for t in idx))] += 1
        for t in idx:
            if P[t][3][0] == 'wall': pairs[tuple(sorted(P[t][3][2:4]))] += 1
        continue
    for key, d in rec['certs'].items(): csupp[len(d)] += 1
    if rec['kind'] == 'in': continue
    k = rec['k']; acc = []
    for m, (i, j) in enumerate(rec['cut']):
        a, rhs = wall(k, i, j)
        stack.append((path + (m,), P + acc + [([-v for v in a], -rhs, True, ('wall', tuple(k), i, j))]))
        acc = acc + [(a, rhs, False, ('wall', tuple(k), i, j))]
print("empty leaves: rows in the Farkas combination:", sorted(supp.items()))
print("  row types combined:"); [print("    %5d  %s" % (v, k)) for k, v in kinds.most_common(12)]
print("  runner pairs of the walls used (i, j):"); [print("    %5d  %s" % (v, k)) for k, v in pairs.most_common(12)]
print("containment certificates: rows combined:", sorted(csupp.items()))
