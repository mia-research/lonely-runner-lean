"""Independent checker for band_cover_tree_v3.json.  Imports nothing from the generator or any LP code.
Claim: every (s1..s6) with 1 <= s1 <= ... <= s6, 7 <= s6 <= 9 (s0 = 1) lies in some cone
  C(k) = { (8k_i+1) s_j <= (8k_j+7) s_i for all i != j },  k0 in {0, 1},
so (TwoBlockN.lonely_eight_of_pairwise_laps) the subject is lonely at some R in [8k0+1, 8k0+7] within [1,7] u [9,15].
Variables x_i = s_{i+1} - 1 >= 0.  Pieces are rebuilt from the root: at a node using cone k with cut walls w_1..w_m, the
children are P & {w_1..w_{l-1} hold} & {w_l violated strictly}; every uncut wall of k carries a Farkas certificate that it
holds on (the closure of) P; 'empty' leaves carry a certificate that P is empty; 'in' leaves have no cut walls."""
import json, sys
from fractions import Fraction as F
N = 6
def root():
    rows = []
    for i in range(N - 1):
        a = [0] * N; a[i] = 1; a[i + 1] = -1; rows.append((a, F(0), False))      # s_{i+1} <= s_{i+2}
    a = [0] * N; a[5] = 1; rows.append((a, F(8), False))                          # s6 <= 9
    a = [0] * N; a[5] = -1; rows.append((a, F(-6), False))                        # s6 >= 7
    return rows
def wall(k, i, j):
    """(8k_i+1) s_j - (8k_j+7) s_i <= 0 in x = s - 1 (s0 = 1)."""
    a = [0] * N
    if j: a[j - 1] += 8 * k[i] + 1
    if i: a[i - 1] -= 8 * k[j] + 7
    return a, F(8 * k[j] + 7 - (8 * k[i] + 1))
def unsp(d, m):
    y = [F(0)] * m
    for t, v in d.items(): y[int(t)] = F(v)
    return y
def contained(P, a, rhs, cert):
    y = unsp(cert, len(P))
    if any(v < 0 for v in y): return False
    for c in range(N):
        if sum(y[t] * P[t][0][c] for t in range(len(P))) < a[c]: return False
    return sum(y[t] * P[t][1] for t in range(len(P))) <= rhs
def empty(P, cert):
    kind, d = cert
    rows = [(a + [1 if st else 0], b) for a, b, st in P] + [([0] * N + [1], F(1))]
    y = unsp(d, len(rows))
    if any(v < 0 for v in y): return False
    for c in range(N):
        if sum(y[t] * rows[t][0][c] for t in range(len(rows))) < 0: return False
    yb = sum(y[t] * rows[t][1] for t in range(len(rows)))
    if kind == 'farkas': return yb < 0
    tau = sum(y[t] * rows[t][0][N] for t in range(len(rows)))
    return tau >= 1 and yb <= 0 and any(st for a, b, st in P)
tree = json.load(open(sys.argv[1] if len(sys.argv) > 1 else 'band_cover_tree_v3.json'))
PAIRS = [(i, j) for i in range(7) for j in range(7) if i != j]
stack = [((), root())]; seen = 0; leaves = {'in': 0, 'empty': 0}; cones = set(); bad = []
while stack:
    path, P = stack.pop(); key = ','.join(map(str, path)); seen += 1
    rec = tree.get(key)
    if rec is None: bad.append(('missing node', key)); continue
    if rec['kind'] == 'empty':
        if not empty(P, rec['cert']): bad.append(('empty cert fails', key))
        leaves['empty'] += 1; continue
    k = rec['k']; cut = [tuple(c) for c in rec['cut']]
    if k[0] not in (0, 1): bad.append(('slowest lap not 0 or 1', key))
    cones.add(tuple(k))
    for (i, j) in PAIRS:
        if (i, j) in cut: continue
        a, rhs = wall(k, i, j)
        if all(v == 0 for v in a):
            if rhs < 0: bad.append(('constant wall false', key))
            continue
        c = rec['certs'].get('%d,%d' % (i, j))
        if c is None or not contained(P, a, rhs, c): bad.append(('containment fails', key, (i, j)))
    if rec['kind'] == 'in':
        if cut: bad.append(('in-leaf with cuts', key))
        leaves['in'] += 1; continue
    acc = []
    for m, (i, j) in enumerate(cut):
        a, rhs = wall(k, i, j)
        stack.append((path + (m,), P + acc + [([-v for v in a], -rhs, True)])); acc = acc + [(a, rhs, False)]
print("nodes visited", seen, "of", len(tree), " leaves", leaves, " cones used", len(cones))
print("CHECK PASSED" if not bad and seen == len(tree) else "CHECK FAILED %s" % bad[:5])
