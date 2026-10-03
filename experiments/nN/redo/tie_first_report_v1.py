# tie_first_report_v1.py -- type table of zero-width landings from tie_first_*.pkl (exact)
import pickle
from fractions import Fraction as F
from collections import Counter, defaultdict
rows = {}
for ds, fs in (('J1', ['tie_first_J1_0_v1.pkl']), ('J2', ['tie_first_J2_0_v1.pkl', 'tie_first_J2_3000_v1.pkl'])):
    rows[ds] = sum((pickle.load(open(f, 'rb')) for f in fs), [])
for ds, rs in rows.items():
    print('DATASET', ds, 'zero-width landings', len(rs))
    print(' by (moves>=2?, R*==1, #exits at p=1, #entries at p=7):', sorted(Counter((min(x['nm'], 2), x['R'] == 1, len(x['exits']), len(x['entries'])) for x in rs).items()))
    c = Counter(); small = {}
    for x in rs:
        for e in x['exits']:
            for n in x['entries']:
                key = (x['nm'] if x['nm'] < 2 else 2, e, n)
                # exit lap 0 convention for the start
                c[key] += 1
                sk = (x['rh'][-1], x['rh'])
                if key not in small or sk < small[key][0]: small[key] = (sk, x['R'], x['idx'])
    print(' by (moves class, exit (rank,lap), entry (rank,lap)): count, smallest rho_7 example')
    for k in sorted(c, key=lambda k: -c[k]):
        sk, R, idx = small[k]
        print('  ', k, c[k], 'rho7=%s R*=%s idx=%s' % (sk[0], R, idx))
    print(' closer rank (entries) distribution:', sorted(Counter(n[0] for x in rs for n in x['entries']).items()))
    print(' opener rank distribution (setter at last move):', sorted(Counter(x['opener'][0] if x['opener'] else None for x in rs).items(), key=str))
    print(' R* integer?', Counter(x['R'].denominator == 1 for x in rs))
