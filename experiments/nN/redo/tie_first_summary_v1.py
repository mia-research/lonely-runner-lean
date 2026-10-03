# tie_first_summary_v1.py -- classes of zero-width landings among the stored tree members (J1: 18,452 points; J2: 271,361 points), exact.
import pickle
from fractions import Fraction as F
from collections import Counter, defaultdict
rows = {'J1': pickle.load(open('tie_first_J1_0_v1.pkl', 'rb')),
        'J2': pickle.load(open('tie_first_J2_0_v1.pkl', 'rb')) + pickle.load(open('tie_first_J2_3000_v1.pkl', 'rb'))}
def cls(x):
    nm = x['nm']; ent = x['entries']
    mv = 'K0z' if nm == 0 else ('K1z' if nm == 1 else 'K2z')
    return mv
for ds, rs in rows.items():
    print('DATASET', ds, 'zero-width landings among stored points:', len(rs))
    C = Counter(cls(x) for x in rs); print('  by move class:', dict(C), '| moves exactly:', sorted(Counter(x['nm'] for x in rs).items())[:12])
    # touching reading identity
    T = Counter(); small = {}
    for x in rs:
        for e in x['exits']:
            for n in x['entries']:
                kind = ('start (exit = reading 1 at lap 0)' if x['R'] == 1 else ('entry is reading 1' if n[0] == 1 else ('exit is reading 1' if e[0] == 1 else 'neither reading 1')))
                k = (cls(x), kind); T[k] += 1
                sk = (x['rh'][-1], x['rh'])
                if k not in small or sk < small[k][0]: small[k] = (sk, x['R'], e, n, x['idx'])
    for k in sorted(T): 
        sk, R, e, n, idx = small[k]
        print('  %-4s %-36s pairs %5d | smallest rho_7 = %s (%.6f), R* = %s, exit (rank,lap) %s, entry (rank,lap) %s, member idx %s' % (k[0], k[1], T[k], sk[0], float(sk[0]), R, e, n, idx))
        print('        readings', [str(r) for r in sk[1]])
    # ties
    ties = [x for x in rs if len(x['exits']) > 1 or len(x['entries']) > 1]
    print('  tied (>=2 readings at p=1 or at p=7 at the landing):', len(ties), '; exits>=2:', sum(len(x['exits']) > 1 for x in rs), '; entries>=2:', sum(len(x['entries']) > 1 for x in rs), '; both:', sum(len(x['exits']) > 1 and len(x['entries']) > 1 for x in rs))
    # ratios of tied pairs
    rc = Counter()
    for x in ties:
        rh = x['rh']
        for lst, sign in ((x['exits'], 1), (x['entries'], -1)):
            if len(lst) > 1:
                (a, ja), (b, jb) = lst[0], lst[1]
                rc[('exits' if sign == 1 else 'entries', (a, ja), (b, jb))] += 1
    print('  most common tied pairs (type, first (rank,lap), second (rank,lap)):', rc.most_common(8))
    # reading 1 involvement among ties
    print('  closer rank (any entry) counts:', sorted(Counter(n[0] for x in rs for n in x['entries']).items()))
    print('  R* values most common:', Counter(str(x['R']) for x in rs).most_common(6))
