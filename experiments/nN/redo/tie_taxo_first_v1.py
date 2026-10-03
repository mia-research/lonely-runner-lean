# tie_taxo_first_v1.py -- zero-width landings in the 52,000 sampler arrangements and the 5,005 integer sets (lat1), by number of cascade moves; exact.
import pickle, glob
from fractions import Fraction as F
from collections import Counter
exec(open('win_lib_v1.py').read())
rows = pickle.load(open('taxo_sample_v1.pkl', 'rb'))
C = Counter(); small = {}
for r in rows:
    name, rho, lab, lab2, ok, nm, op, cl, width, R = r
    if width != 0: continue
    k = (min(nm, 3), 'integer readings' if all(x.denominator == 1 for x in rho) else 'some non-integer')
    C[k] += 1
    sk = (rho[-1], rho)
    if k not in small or sk < small[k][0]: small[k] = (sk, nm, op, cl, R, name)
print('SAMPLER (52,000): zero-width landings by (moves 0,1,2,3+; integer readings?):')
for k in sorted(C):
    sk, nm, op, cl, R, name = small[k]
    print('  moves', k[0], k[1], 'count', C[k], '| smallest rho_7', sk[0], '| moves', nm, 'opener', op, 'closer', cl, 'R*', R, '| family', name)
    print('       readings', [str(x) for x in sk[1]])
# lat1: first window pinch
recs = []
for f in glob.glob('win_rec_lat1_*_v1.pkl'): recs += pickle.load(open(f, 'rb'))
Cl = Counter(); smalll = {}
for lab, rh, ws, *_ in recs:
    rh = norm(rh); a, b = ws[0]
    if a != b: continue
    steps, R = path(rh)
    k = ('start R*=1' if R == 1 else 'pinch R*>1', len(steps))
    Cl[k] += 1
    sk = (rh[-1], rh)
    if k not in smalll or sk < smalll[k][0]: smalll[k] = (sk, R)
print('LAT1 (5,005 integer sets): first window a single point, by (kind, moves):', sorted(Cl.items()))
for k in sorted(smalll): print('  ', k, 'smallest rho_7', smalll[k][0][0], 'R*', smalll[k][1], [str(x) for x in smalll[k][0][1]])
# explicit constructed examples (derivation in tie_structure_v1.md)
print('CONSTRUCTED:')
for name, rh in (('K0z [1..7]', [F(x) for x in range(1, 8)]),
                 ('K1z rho_7 = 15/2, rho_6 = 35/6', [F(1), F(2), F(3), F(4), F(5), F(35, 6), F(15, 2)]),
                 ('K1z rho_7 = 8, rho_6 = 56/9', [F(1), F(2), F(3), F(4), F(5), F(56, 9), F(8)])):
    o = outcome(rh); ws = windows(rh, 23)
    print('  ', name, 'R*', o['R'], 'moves', o['nmoves'], 'opener', o['opener'], 'closer', o['closer'], 'width', o['width'], 'first window', ws[0], 'verify', verify(rh, ws, 23))
