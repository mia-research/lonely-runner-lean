# E830: chain types of the carves found (laps 2 and 3 of the top reading) and of the best near-carves for laps 4 to 6 and above 25: for each distinct zone-chain type, an LP over the readings (floats steer only, HiGHS): the largest r7 with every link (8j+1) r_q - (8k-1) r_p >= 0 (closed type), ends covered, readings in [1, 80]; and for the near-carves the largest margin t.  The binding links (nonzero dual) of the type with the largest r7 are listed.
import glob, pickle, collections, re
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
def chain_of(x):
    rs = [F(v) for v in x]; zones = []
    for idx, r in enumerate(rs):
        j = 1
        while (8 * j - 1) / r < 7:
            zones.append(((8 * j - 1) / r, (8 * j + 1) / r, idx, j)); j += 1
    zones.sort()
    cand = [z for z in zones if z[0] < 1 < z[1]]
    if not cand: return None
    chain = [max(cand, key=lambda z: z[1])]; cur = chain[0][1]
    while cur <= 7:
        opts = [z for z in zones if z[0] <= cur and z[1] > cur]
        if opts: z = max(opts, key=lambda z: z[1])
        else:
            nxt = [z for z in zones if z[0] > cur]
            if not nxt: return None
            z = min(nxt, key=lambda z: z[0])
        chain.append(z); cur = z[1]
    return tuple((z[2], z[3]) for z in chain)
n = 6
def lp(chain, objective):
    A = []; b = []; names = []
    for k in range(len(chain) - 1):
        (p, jp), (q, jq) = chain[k], chain[k + 1]
        if p == q: continue
        row = np.zeros(n + 1); row[q] += -(8 * jp + 1); row[p] += (8 * jq - 1); row[n] = 1.0
        A.append(row); b.append(0.0); names.append('link: r%d lap %d -> r%d lap %d' % (p + 2, jp, q + 2, jq))
    p, j = chain[0]
    row = np.zeros(n + 1); row[p] = -1; row[n] = 1; A.append(row); b.append(-(8 * j - 1)); names.append('start lower r%d > %d' % (p + 2, 8 * j - 1))
    row = np.zeros(n + 1); row[p] = 1; row[n] = 1; A.append(row); b.append(8 * j + 1); names.append('start upper r%d < %d' % (p + 2, 8 * j + 1))
    p, j = chain[-1]
    row = np.zeros(n + 1); row[p] = 7; row[n] = 1; A.append(row); b.append(8 * j + 1); names.append('end 7 r%d < %d' % (p + 2, 8 * j + 1))
    for i in range(n - 1):
        row = np.zeros(n + 1); row[i] = 1; row[i + 1] = -1; A.append(row); b.append(0.0); names.append('order r%d <= r%d' % (i + 2, i + 3))
    c = np.zeros(n + 1)
    bounds = [(1, 80)] * n + [(0, 10)]
    if objective == 'rho7': c[n - 1] = -1
    else: c[n] = -1; bounds[n] = (None, 10)
    res = linprog(c, A_ub=np.array(A), b_ub=np.array(b), bounds=bounds, method='highs')
    return res, names
groups = {'laps 2,3 carves': [], 'near-carves above 25': []}
for f in sorted(glob.glob('frontier_band_carve_v1_k[23]_s*.pkl')) + sorted(glob.glob('frontier_box_carve_v1_23_25_s*.pkl')): groups['laps 2,3 carves'] += pickle.load(open(f, 'rb'))
for f in sorted(glob.glob('frontier_box_carve_v1_hi2_s*.out')):
    m = re.search(r'readings \(float\): \[(.*)\]', open(f).readline()); groups['near-carves above 25'].append([float(v) for v in m.group(1).split(',')])
groups['near-carves above 25'].append(pickle.load(open('frontier_polish_v1_first.pkl', 'rb')))
best = None
for g, vecs in groups.items():
    types = collections.Counter()
    for v in vecs:
        ch = chain_of(sorted(v))
        if ch: types[ch] += 1
    print(g, ':', len(vecs), 'vectors,', len(types), 'distinct chain types')
    if g.startswith('laps'):
        bestr = (0, None, None)
        for ch in types:
            res, names = lp(ch, 'rho7')
            if res.status == 0 and -res.fun > bestr[0]: bestr = (-res.fun, ch, (res, names))
        res, names = bestr[2]
        print('  largest r7 over the closed chain types (LP, floats steer):', round(bestr[0], 6), '| readings at the optimum:', [round(float(v), 6) for v in res.x[:n]])
        print('  binding links of that type:', [(nm, round(float(d), 5)) for nm, d in zip(names, res.ineqlin.marginals) if abs(d) > 1e-9])
        pickle.dump(bestr[1], open('frontier_chain_types_best_lap3.pkl', 'wb'))
    else:
        tmax = []
        for ch in types:
            res, names = lp(ch, 'margin')
            tmax.append((-res.fun if res.status == 0 else None, ch))
        vals = sorted(t for t, ch in tmax if t is not None)
        print('  largest margin t of each chain type (LP, floats steer): max', vals[-1] if vals else None, '| number of types with t > 1e-9:', sum(1 for t in vals if t > 1e-9))
