"""E124: generate the band's wall-cut cover WITH certificates.  Nodes are identified by their path from the root; each
record: kind ('in' | 'split' | 'empty'), cone laps k, cut walls (i, j) in order, containment certificates for the walls
not cut (sparse Farkas multipliers over the piece's rows), and emptiness certificates.  Pieces are NOT stored: the
checker rebuilds them from the root."""
import sys, json, time
from fractions import Fraction as F
from multiprocessing import Pool
from exact_lp import lp_max_dual
from band_cone_cover_exact_v2 import BASE, load_cones, inside, cats
NV = 6
def wall(k, i, j):
    a = [0] * NV; rhs = F((8 * k[j] + 7) - (8 * k[i] + 1))
    if j >= 1: a[j - 1] += 8 * k[i] + 1
    if i >= 1: a[i - 1] -= 8 * k[j] + 7
    return a, rhs
PAIRS = [(i, j) for i in range(7) for j in range(7) if i != j]
def sp(y): return {str(t): str(v) for t, v in enumerate(y) if v != 0}
def process(args):
    P, cones = args
    A1 = [a + ([1] if st else [0]) for a, b, st in P] + [[0] * NV + [1]]
    b1 = [b for a, b, st in P] + [F(1)]
    r = lp_max_dual(A1, b1, [0] * NV + [1])
    strict = any(st for a, b, st in P)
    if r[0] == 'infeasible': return {'kind': 'empty', 'cert': ['farkas', sp(r[1])]}, [], []
    if strict and r[1] <= 0: return {'kind': 'empty', 'cert': ['tau', sp(r[3])]}, [], []
    x = r[2][:NV]; s = [F(1)] + [F(1) + v for v in x]
    k = next((c for c in cones if inside(s, c)), None); new = []
    if k is None:
        new = [c for c in cats(s) if inside(s, c)]
        assert new, ("HOLE", s)
        k = new[0]
    A = [a for a, b, st in P]; b = [bb for a, bb, st in P]
    cut, certs = [], {}
    for (i, j) in PAIRS:
        a, rhs = wall(k, i, j)
        if all(v == 0 for v in a):
            assert rhs >= 0; continue
        rr = lp_max_dual(A, b, a)
        if rr[1] > rhs: cut.append((i, j))
        else: certs['%d,%d' % (i, j)] = sp(rr[3])
    rec = {'kind': 'in' if not cut else 'split', 'k': list(k), 'cut': cut, 'certs': certs}
    children = []; acc = []
    for (i, j) in cut:
        a, rhs = wall(k, i, j)
        children.append(P + acc + [([-v for v in a], -rhs, True)]); acc = acc + [(a, rhs, False)]
    return rec, children, new
if __name__ == '__main__':
    cones = load_cones(); frontier = [((), BASE)]; tree = {}; t0 = time.time()
    with Pool(10) as pool:
        while frontier:
            res = pool.map(process, [(P, cones) for _, P in frontier], chunksize=4)
            nxt = []
            for (path, P), (rec, ch, new) in zip(frontier, res):
                tree[','.join(map(str, path))] = rec
                for c in new:
                    if c not in cones: cones.append(c)
                nxt += [(path + (m,), C) for m, C in enumerate(ch)]
            frontier = nxt
            print("nodes %d  frontier %d  %.0fs" % (len(tree), len(frontier), time.time() - t0)); sys.stdout.flush()
    json.dump(tree, open('band_cover_tree_v3.json', 'w'))
    from collections import Counter
    print("DONE", Counter(r['kind'] for r in tree.values()), "cones used", len({tuple(r['k']) for r in tree.values() if 'k' in r}))
