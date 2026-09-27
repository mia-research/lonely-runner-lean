"""E125: are the band cover's refutations cycles of ratio bounds?  For each empty leaf, the walls in its Farkas combination
are edges between runners (node 0 = the slowest runner, fixed at 1; order rows s_i <= s_{i+1} are edges too; the s7 range
rows touch node 6 and the constant).  Classify the edge multigraph: a single cycle (every node degree 2), a path between
two constant-anchored nodes (through node 0 / the s7 range), or other."""
import json
from fractions import Fraction as F
from collections import Counter, defaultdict
exec(open('cover_certificate_anatomy_v1.py').read().split("tree = json.load")[0])
tree = json.load(open('band_cover_tree_v3.json'))
stack = [((), root())]; shape = Counter(); lens = Counter()
while stack:
    path, P = stack.pop(); rec = tree[','.join(map(str, path))]
    if rec['kind'] == 'empty':
        d = rec['cert'][1]; idx = [int(t) for t in d if int(t) < len(P)]
        deg = defaultdict(int); anchors = 0; E = 0
        for t in idx:
            tag = P[t][3]
            if tag[0] == 'order': u, v = tag[1], tag[2]
            elif tag[0] == 'wall': u, v = tag[2], tag[3]
            else: u, v = 6, 'C'
            deg[u] += 1; deg[v] += 1; E += 1
        nodes = [n for n in deg]
        odd = [n for n in nodes if deg[n] % 2]
        if all(deg[n] == 2 for n in nodes) and not any(n in (0, 'C') for n in nodes): kind = 'cycle among runners 1..6'
        elif all(deg[n] == 2 for n in nodes if n not in (0, 'C')): kind = 'cycle/path through the fixed runner or s7 range'
        else: kind = 'branching (some runner in 3+ walls)'
        shape[kind] += 1; lens[E] += 1
        continue
    if rec['kind'] == 'in': continue
    k = rec['k']; acc = []
    for m, (i, j) in enumerate(rec['cut']):
        a, rhs = wall(k, i, j)
        stack.append((path + (m,), P + acc + [([-v for v in a], -rhs, True, ('wall', tuple(k), i, j))]))
        acc = acc + [(a, rhs, False, ('wall', tuple(k), i, j))]
print("empty leaves by the shape of their refutation:"); [print("   %5d  %s" % (v, k)) for k, v in shape.most_common()]
print("edges per refutation:", sorted(lens.items()))
