# E832: for sample uncertified leaves at D=64 (frontier_box_dfs_v1_leaves64_*.txt), the zone chain of the box centre, the LP over that chain type (floats steer only), its binding links and the exact nullspace of the binding link rows (an exact combination equal to zero = a cycle of product 1).
import glob, random, re, collections
from fractions import Fraction as F
import numpy as np, sympy as sp
exec(open('frontier_chain_types_v1.py').read().split("groups = {")[0])
random.seed(3)
rows = []
for f in sorted(glob.glob('frontier_box_dfs_v1_leaves64_*.txt')):
    for l in open(f):
        v = [int(x) for x in l.split()]; rows.append((v[0], v[1:]))
def cluster(D, n):
    c = [(x + 0.5) / D for x in n]; r = c[5] / c[3]
    return min([5.25, 7.0, 6.3, 6.25], key=lambda a: abs(a - r))
by = collections.defaultdict(list)
for D, nb in rows: by[cluster(D, nb)].append((D, nb))
for key in (5.25, 7.0, 6.3, 6.25):
    sample = random.sample(by[key], min(4, len(by[key])))
    print('cluster rho7/rho5 near', key, ':', len(by[key]), 'leaves')
    seen = set()
    for D, nb in sample:
        x = sorted((v + 0.5) / D for v in nb)
        ch = chain_of(x)
        if ch is None or ch in seen: continue
        seen.add(ch)
        res, names = lp(ch, 'margin')
        bind = [(names[i], float(d)) for i, d in enumerate(res.ineqlin.marginals) if abs(d) > 1e-9 and names[i].startswith('link')]
        rws = []
        for nm, d in bind:
            m = re.match(r'link: r(\d+) lap (\d+) -> r(\d+) lap (\d+)', nm)
            p, jp, q, jq = [int(g) for g in m.groups()]
            row = [0] * 6; row[q - 2] += -(8 * jp + 1); row[p - 2] += (8 * jq - 1); rws.append(row)
        ns = sp.Matrix(rws).T.nullspace() if rws else []
        print('   LP margin (float) %.2e | binding links %s | exact nullspace of the binding rows: %s' % (-res.fun, [b[0] for b in bind], [list(v) for v in ns]))
