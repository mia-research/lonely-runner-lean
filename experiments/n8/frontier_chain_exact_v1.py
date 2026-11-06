# E830: exact (Fractions / sympy) analysis of the LP results of frontier_chain_types_v1.py: (a) the tight system of the chain type with the largest r7 (laps 2 and 3 carves) solved exactly; the same for the largest type among the lap-2 carves; (b) for each chain type of the near-carves above 25, the exact positive combination of its binding links that is identically zero.
import glob, pickle, re, collections
from fractions import Fraction as F
import numpy as np
import sympy as sp
exec(open('frontier_chain_types_v1.py').read().split("groups = {")[0])
def exact_top(ch):
    res, names = lp(ch, 'rho7')
    tight = [i for i, d in enumerate(res.ineqlin.marginals) if abs(d) > 1e-9]
    syms = sp.symbols('r2:8')
    eqs = []
    for i in tight:
        nm = names[i]
        m = re.match(r'link: r(\d+) lap (\d+) -> r(\d+) lap (\d+)', nm)
        if m:
            p, jp, q, jq = int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4))
            eqs.append((8 * jp + 1) * syms[q - 2] - (8 * jq - 1) * syms[p - 2])
        m = re.match(r'end 7 r(\d+) < (\d+)', nm)
        if m: eqs.append(7 * syms[int(m.group(1)) - 2] - int(m.group(2)))
        m = re.match(r'start (lower|upper) r(\d+) [<>] (\d+)', nm)
        if m: eqs.append(syms[int(m.group(2)) - 2] - int(m.group(3)))
        m = re.match(r'order r(\d+) <= r(\d+)', nm)
        if m: eqs.append(syms[int(m.group(1)) - 2] - syms[int(m.group(2)) - 2])
    sol = sp.solve(eqs, syms, dict=True)
    return res, names, tight, sol
groups = {2: [], 3: []}
for k in (2, 3):
    for f in sorted(glob.glob('frontier_band_carve_v1_k%d_s*.pkl' % k)): groups[k] += pickle.load(open(f, 'rb'))
groups[3] += [v for f in sorted(glob.glob('frontier_box_carve_v1_23_25_s*.pkl')) for v in pickle.load(open(f, 'rb'))]
for k in (2, 3):
    types = collections.Counter(chain_of(sorted(v)) for v in groups[k] if chain_of(sorted(v)))
    best = (0, None)
    for ch in types:
        res, names = lp(ch, 'rho7')
        if res.status == 0 and -res.fun > best[0]: best = (-res.fun, ch)
    res, names, tight, sol = exact_top(best[1])
    print('lap', k, 'strip:', len(groups[k]), 'carves,', len(types), 'chain types; LP top r7 (float):', round(best[0], 6))
    print('   binding constraints:', [names[i] for i in tight])
    if sol: print('   exact solution of the tight system:', {str(a): sp.nsimplify(b) for a, b in sol[0].items()}, '| r7 float', float(sol[0].get(sp.Symbol('r7'), 0)))
# (b) near-carves above 25
vecs = []
for f in sorted(glob.glob('frontier_box_carve_v1_hi2_s*.out')):
    m = re.search(r'readings \(float\): \[(.*)\]', open(f).readline()); vecs.append([float(v) for v in m.group(1).split(',')])
vecs.append(pickle.load(open('frontier_polish_v1_first.pkl', 'rb')))
types = collections.Counter(chain_of(sorted(v)) for v in vecs if chain_of(sorted(v)))
print('near-carves above 25:', len(vecs), 'vectors,', len(types), 'chain types')
for ch in types:
    res, names = lp(ch, 'margin')
    bind = [(names[i], float(d)) for i, d in enumerate(res.ineqlin.marginals) if abs(d) > 1e-9 and names[i].startswith('link')]
    rows = []
    for nm, d in bind:
        m = re.match(r'link: r(\d+) lap (\d+) -> r(\d+) lap (\d+)', nm)
        p, jp, q, jq = [int(g) for g in m.groups()]
        row = [0] * 6; row[q - 2] += -(8 * jp + 1); row[p - 2] += (8 * jq - 1); rows.append(row)
    M = sp.Matrix(rows).T
    ns = M.nullspace()
    print('  type', 'chain length', len(ch), '| float margin', round(-res.fun, 12), '| binding links:', [b[0] for b in bind], '| exact nullspace of the binding rows (a combination equal to 0):', [list(v) for v in ns])
