# carve_extra_v1: stabilisation / separation counts from carve_rec_*.  (counts only)
import pickle, glob
from collections import Counter
def ld(name):
    out = []
    for f in sorted(glob.glob('carve_rec_%s_*_v1.pkl' % name), key=lambda s: int(s.split('_')[-2])): out += pickle.load(open(f, 'rb'))
    return out
D = {n: ld(n) for n in ('J1', 'J2s', 'taxo', 'lat1_24', 'lat2_24', 'lat3_24')}
key = lambda r: r['ns'][1:]
S = {n: set(key(r) for r in R) for n, R in D.items()}
J2lo = set(key(r) for r in D['J2s'] if r['rho7'] <= 9)
print('J2s members with rho_7<=9: profiles', len(J2lo), ' of which in J1 profile set:', len(J2lo & S['J1']), ' not in J1:', len(J2lo - S['J1']))
for n in ('lat1_24', 'lat2_24', 'lat3_24'):
    lo = set(key(r) for r in D[n] if r['rho7'] <= 9)
    print(n, 'rho_7<=9: profiles', len(lo), 'in J1 set', len(lo & S['J1']), 'in J2s set', len(lo & S['J2s']), 'in taxo set', len(lo & S['taxo']))
    lo = set(key(r) for r in D[n] if r['rho7'] <= 17); print(n, 'rho_7<=17: profiles', len(lo), 'in J2s set', len(lo & S['J2s']))
print('singleton profiles (occurring for exactly one member):')
for n, R in D.items():
    c = Counter(key(r) for r in R); print(' ', n, 'members', len(R), 'profiles', len(c), 'singletons', sum(1 for v in c.values() if v == 1), 'max multiplicity', max(c.values()))
print('lattice s=1: cumulative distinct profiles by a_7<=N, and singletons among a_7<=N')
for N in (12, 16, 20, 24):
    R = [r for r in D['lat1_24'] if r['rho7'] <= N]; c = Counter(key(r) for r in R)
    print('  N=%d sets %d profiles %d singletons %d' % (N, len(R), len(c), sum(1 for v in c.values() if v == 1)))
print('crossers: J2s crosser prefix profiles (n_2..n_6) vs J1 crosser prefix profiles')
pj1 = set(key(r)[:-1] for r in D['J1'] if r['crosser']); pj2 = set(key(r)[:-1] for r in D['J2s'] if r['crosser'])
print('  J1', len(pj1), 'J2s', len(pj2), 'J2s in J1', len(pj1 & pj2), 'J2s not in J1', len(pj2 - pj1))
for n in ('J1', 'J2s'):
    C = [r for r in D[n] if r['crosser']]; N = [r for r in D[n] if not r['crosser']]
    print(n, 'crossers n_6<=6:', sum(r['n6'] <= 6 for r in C), '/', len(C), '; non-crossers n_6<=6:', sum(r['n6'] <= 6 for r in N), '/', len(N), '; non-crossers n_6<=6 and W:', sum(r['n6'] <= 6 and r['W'] for r in N))
    print('  crossers n_6 in (2,3,4,5,6) ; non-crossers n_6<=3: ', sum(r['n6'] <= 3 for r in N), 'crossers n_6<=3:', sum(r['n6'] <= 3 for r in C))
    ps = Counter(key(r)[:-1] for r in C); pn = Counter(key(r)[:-1] for r in N)
    print('  prefix profiles occurring only for crossers', sum(1 for p in ps if p not in pn), '(members', sum(v for p, v in ps.items() if p not in pn), ') ; only for non-crossers', sum(1 for p in pn if p not in ps))
    print('  longest K6 window times rho_7 / 2 : crossers max', float(max(r['lmax6'] * r['rho7'] / 2 for r in C)), ' exact < 1 for all:', all(r['lmax6'] * r['rho7'] / 2 < 1 for r in C))
