# carve_analyse_v1: aggregate carve_rec_*_v1.pkl.  Exact fractions printed as p/q and decimal only as a label for reading.
import pickle, glob, random
from collections import Counter, defaultdict
from fractions import Fraction as F
def ld(name):
    out = []
    for f in sorted(glob.glob('carve_rec_%s_*_v1.pkl' % name), key=lambda s: int(s.split('_')[-2])): out += pickle.load(open(f, 'rb'))
    return out
DS = {'J1': ld('J1'), 'J2s': ld('J2s'), 'taxo': ld('taxo'), 'lat1_24': ld('lat1_24')}
import os
for nm in ('lat2_24', 'lat3_24'):
    if glob.glob('carve_rec_%s_*_v1.pkl' % nm): DS[nm] = ld(nm)
DS['lat1_16'] = [r for r in DS['lat1_24'] if r['rho7'] <= 16]; DS['lat1_20'] = [r for r in DS['lat1_24'] if r['rho7'] <= 20]
for n in (16, 20, 24): pass
def key(r): return r['ns'][1:]
print('## (1) exact checks per dataset')
for k, R in DS.items():
    c = Counter()
    for r in R:
        for f in ('order_ok', 'cc_ok', 'landing_ok', 'k6_ok'): c[f] += r[f]
        c['gate_cond==crosser'] += (r['gate_cond'] == r['crosser']); c['crosser'] += r['crosser']; c['W'] += r['W']
        c['W&crosser'] += (r['W'] and r['crosser'])
    print(k, 'members', len(R), dict(c))
print('\n## (2) profile counts (n_2..n_7)')
P = {k: Counter(key(r) for r in R) for k, R in DS.items()}
P1 = {k: Counter((key(r), r['onept']) for r in R) for k, R in DS.items()}
for k in DS: print(k, 'members', len(DS[k]), 'distinct profiles', len(P[k]), 'distinct (profile, #one-point windows)', len(P1[k]))
def cmp(a, b):
    A, B = set(P[a]), set(P[b]); print('  %s vs %s: |A|=%d |B|=%d  A&B=%d  A-B=%d  B-A=%d' % (a, b, len(A), len(B), len(A & B), len(A - B), len(B - A)))
print('inclusions'); 
for a, b in (('lat1_16', 'lat1_20'), ('lat1_20', 'lat1_24'), ('J1', 'J2s'), ('J1', 'lat1_24'), ('J2s', 'lat1_24'), ('taxo', 'J2s'), ('taxo', 'lat1_24'), ('taxo', 'J1')): cmp(a, b)
print('\nJ2s cumulative distinct profiles by prefix size (members sorted by region index order of sample)')
R = DS['J2s']; s = set()
for n, r in enumerate(R, 1):
    s.add(key(r))
    if n in (1000, 2500, 5000, 10000, 15000, 20000): print('  first', n, 'members:', len(s))
print('J2s by rho_7 bin: distinct profiles'); 
bins = [(0, 9), (9, 13), (13, 17), (17, 100)]
for lo, hi in bins:
    S = [r for r in R if lo < r['rho7'] <= hi]; print('  rho_7 in (%d,%d]: members %d, profiles %d' % (lo, hi, len(S), len(set(key(r) for r in S))))
print('lattice s=1 by a_7: distinct profiles with a_7 = N exactly, and new relative to a_7 < N')
seen = set()
for N in range(7, 25):
    S = [r for r in DS['lat1_24'] if r['rho7'] == N]; k = set(key(r) for r in S)
    print('  a_7=%2d: sets %5d, profiles %3d, new vs smaller a_7: %3d, cumulative %3d' % (N, len(S), len(k), len(k - seen), len(k | seen))); seen |= k
print('J1 by rho_7 bin')
for lo, hi in ((0, 7), (7, 8), (8, 9)):
    S = [r for r in DS['J1'] if lo < r['rho7'] <= hi]; print('  (%d,%d]: members %d profiles %d' % (lo, hi, len(S), len(set(key(r) for r in S))))
print('\nprofile table (profile -> J1, J2s, taxo, lat16, lat20, lat24 counts), all profiles occurring in J1/J2s/lat24 (top 60 by total), full table in carve_table_v1.out')
allk = set()
for k in ('J1', 'J2s', 'taxo', 'lat1_24'): allk |= set(P[k])
rows = sorted(allk, key=lambda p: -sum(P[k][p] for k in ('J1', 'J2s', 'taxo', 'lat1_24')))
with open('carve_table_v1.out', 'w') as f:
    f.write('profile(n_2..n_7)\tJ1\tJ2s\ttaxo\tlat16\tlat20\tlat24\n')
    for p in rows: f.write('%s\t%d\t%d\t%d\t%d\t%d\t%d\n' % (p, P['J1'][p], P['J2s'][p], P['taxo'][p], P['lat1_16'][p], P['lat1_20'][p], P['lat1_24'][p]))
for p in rows[:60]: print(p, [P[k][p] for k in ('J1', 'J2s', 'taxo', 'lat1_16', 'lat1_20', 'lat1_24')])
print('total distinct over all families:', len(rows))
print('\n## (3) gate crossers (K_7 empty)')
for k in [x for x in DS if x not in ('lat1_16','lat1_20')]:
    C = [r for r in DS[k] if r['crosser']]; N = [r for r in DS[k] if not r['crosser']]
    print(k, 'crossers', len(C), 'non-crossers', len(N))
    if not C: continue
    pc = Counter(key(r) for r in C); pn = Counter(key(r) for r in N)
    print('  crosser profiles', len(pc), ' shared with non-crossers', len(set(pc) & set(pn)), ' crosser-only', len(set(pc) - set(pn)))
    print('  n_6 among crossers', sorted(Counter(r['n6'] for r in C).items())); print('  n_6 among non-crossers', sorted(Counter(r['n6'] for r in N).items()))
    pre_c = set(key(r)[:-1] for r in C); pre_n = set(key(r)[:-1] for r in N); print('  prefix (n_2..n_6) crosser distinct', len(pre_c), 'in common with non-crossers', len(pre_c & pre_n))
    print('  (W) longest K6 window < 2/rho_7: crossers', sum(r['W'] for r in C), '/', len(C), '; non-crossers', sum(r['W'] for r in N), '/', len(N))
    print('  gate condition (all K6 components inside one open zone of reading 7): crossers', sum(r['gate_cond'] for r in C), '/', len(C), '; non-crossers', sum(r['gate_cond'] for r in N), '/', len(N))
    print('  crossers: one-point windows in K6? ; n_6 min/max', min(r['n6'] for r in C), max(r['n6'] for r in C))
print('\n## (4) monotonicity of n_k')
for k in [x for x in DS if x not in ('lat1_16','lat1_20')]:
    R = DS[k]; inc = Counter(); anyinc = 0; mx = [0] * 7
    for r in R:
        n = r['ns']; a = False
        for i in range(1, 7):
            if n[i] > n[i - 1]: inc[i + 1] += 1; a = True
            mx[i] = max(mx[i], n[i])
        anyinc += a
    print(k, 'members', len(R), 'with some increase n_{k}>n_{k-1}:', anyinc, ' by k:', dict(sorted(inc.items())), ' max n_k (k=2..7):', mx[1:])
    dec = Counter(); 
    print('   members with n_7 < n_6:', sum(1 for r in R if r['ns'][6] < r['ns'][5]))

print('\n## (4b) increases: smallest exact examples (readings) per step k')
import pickle, itertools, random
from math import gcd
from functools import reduce
def readings(name, idx):
    if name in ('J1',): return dict(pickle.load(open('cell_members7_J1.pkl','rb')))[idx]
    if name == 'J2s': return dict(pickle.load(open('cell_members7_J2.pkl','rb')))[idx]
    if name == 'taxo': return pickle.load(open('taxo_sample_v1.pkl','rb'))[idx][1]
    s = int(name[3]); return [F(x, s) for x in idx]
_cache = {}
def rd(name, idx):
    nm = 'J1' if name == 'J1' else name
    if nm in ('J1','J2s','taxo'):
        if nm not in _cache:
            _cache[nm] = (dict(pickle.load(open('cell_members7_J1.pkl','rb'))) if nm=='J1' else dict(pickle.load(open('cell_members7_J2.pkl','rb'))) if nm=='J2s' else {i:t[1] for i,t in enumerate(pickle.load(open('taxo_sample_v1.pkl','rb')))})
        return _cache[nm][idx]
    return [F(x, int(nm[3])) for x in idx]
def fs(rh): return '[' + ', '.join(str(x) for x in rh) + ']'
for k in [x for x in DS if x not in ('lat1_16','lat1_20')]:
    R = DS[k]
    for step in (3, 6, 7):
        c = [r for r in R if r['ns'][step-1] > r['ns'][step-2]]
        if c:
            r = min(c, key=lambda r: (r['rho7'], str(r['idx'])))
            print(k, 'n_%d > n_%d: %d members; example ns=%s readings %s' % (step, step-1, len(c), r['ns'], fs(rd(k, r['idx']))))
    mxr = max(R, key=lambda r: (max(r['ns']), str(r['idx'])))
    print(k, 'largest n_k =', max(r['ns'] for r in [mxr]), 'at', fs(rd(k, mxr['idx'])))
print('\n## (5) profiles by family')
fam = {k: set(P[k]) for k in DS if k in P}
nonlat = set(P['J1']) | set(P['J2s']) | set(P['taxo']); lat = set()
for k in DS:
    if k.startswith('lat1_24') or k in ('lat2_24','lat3_24'): lat |= set(P[k])
print('non-lattice (J1,J2s,taxo) profiles', len(nonlat), ' lattice profiles', len(lat), ' common', len(nonlat & lat))
only_lat = sorted(lat - nonlat); only_non = sorted(nonlat - lat)
print('profiles only in lattices:', len(only_lat), ' only in non-lattice:', len(only_non))
def ex(p, names):
    for k in names:
        for r in DS[k]:
            if key(r) == p: return k, fs(rd(k, r['idx'])), r['onept']
for p in only_lat[:15]: print('  lattice-only', p, ex(p, [k for k in DS if k.startswith('lat')]))
print('  (taxo and J2s profiles absent from lattices: counts)', len(set(P['taxo']) - lat), len(set(P['J2s']) - lat))
for p in only_non[:5]: print('  non-lattice-only', p, ex(p, ['J1','J2s','taxo']))
print('per dataset: profiles absent from every other dataset:')
for k in P:
    if k in ('lat1_16','lat1_20'): continue
    others = set().union(*[set(P[j]) for j in P if j not in (k,'lat1_16','lat1_20')]); a = sorted(set(P[k]) - others)
    print(' ', k, len(a), ' e.g.', [ (p, ex(p,[k])) for p in a[:2]])
# full table with one example each
with open('carve_table_v1.out','w') as f:
    f.write('profile(n_2..n_7)\tJ1\tJ2s\ttaxo\tlat1_16\tlat1_20\tlat1_24\tlat2_24\tlat3_24\tonepts\texample(dataset: readings)\n')
    first = {}
    for k in ['J1','J2s','taxo','lat1_24','lat2_24','lat3_24']:
        if k in DS:
            for r in DS[k]:
                first.setdefault(key(r), (k, r['idx'], r['onept']))
    for p in sorted(set().union(*[set(P[k]) for k in P]), key=lambda p: -sum(P[k][p] for k in ('J1','J2s','taxo','lat1_24'))):
        k, i, o = first[p]
        f.write('%s\t%s\t%s\n' % (p, '\t'.join(str(P[j][p]) if j in P else '-' for j in ('J1','J2s','taxo','lat1_16','lat1_20','lat1_24','lat2_24','lat3_24')), '%d\t%s: %s' % (o, k, fs(rd(k, i)))))
