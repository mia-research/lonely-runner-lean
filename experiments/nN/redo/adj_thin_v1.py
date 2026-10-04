# adj_thin_v1 -- distribution of the float margin t of every row's facet LP over a sample of expanded full-dimensional cells (steering diagnostic for cells/facets thinner than the perturbation scale)
import pickle, random, math
from collections import Counter
exec(open('adj_lib_v1.py').read())
S = pickle.load(open('adj_state_unb_v1.pkl', 'rb'))
ex = [(sg, r) for sg, r in S['seen'].items() if r is not None and r['status'] == 'ok' and r['codim'] == 0]
random.Random(7).shuffle(ex); ex = ex[:120]
H = Counter(); tcs = []
for sg, r in ex:
    x = r['entry']; rows, tags, steps, R = cell_of(x); D = groups_of(rows); keys = list(D)
    An, bn, nn = lp_prep(keys); tcs.append(r['tc'])
    for i in range(len(keys)):
        z, t = facet_lp(An, bn, i, None)
        if z is None: H['lp-infeasible'] += 1; continue
        if t <= -1e-6: H['t <= -1e-6 (no facet)'] += 1
        elif t <= 0: H['-1e-6 < t <= 0'] += 1
        elif t <= 1e-12: H['0 < t <= 1e-12'] += 1
        elif t <= 1e-9: H['1e-12 < t <= 1e-9'] += 1
        elif t <= 1e-7: H['1e-9 < t <= 1e-7'] += 1
        elif t <= 1e-5: H['1e-7 < t <= 1e-5'] += 1
        elif t <= 1e-3: H['1e-5 < t <= 1e-3'] += 1
        else: H['t > 1e-3'] += 1
print('cells sampled', len(ex), 'rows tested', sum(H.values()))
for k, v in sorted(H.items()): print('  ', k, v)
tcs.sort(); print('Chebyshev margin of the cells: min %.3e  median %.3e  max %.3e' % (tcs[0], tcs[len(tcs)//2], tcs[-1]))
