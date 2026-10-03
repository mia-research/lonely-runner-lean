# tie_region_v1.py -- where the sampler example 'grid+laps' 20982 lies in the J=1 tree (exact), which pickle holds its window set; K1z family; near-AP bound.
import pickle, glob
from fractions import Fraction as F
exec(open('win_lib_v1.py').read())
t = pickle.load(open('taxo_sample_v1.pkl', 'rb')); name, rho = t[20982][0], t[20982][1]
rh = norm(rho); o = outcome(rh)
print('example', name, [str(x) for x in rh], '| rho_7 =', rh[-1], '=%.4f' % float(rh[-1]))
print('path word', o['path'], '| R* =', o['R'], '| closer', o['closer'], '| width', o['width'])
T = pickle.load(open('terminals7_J1.pkl', 'rb')); Md = dict(pickle.load(open('cell_members7_J1.pkl', 'rb')))
inbox = []
for i, x in enumerate(T):
    rng = x[3]
    if all(F(lo).limit_denominator(10**9) <= r <= F(hi).limit_denominator(10**9) for (lo, hi), r in zip(rng, rh)) and tuple(x[0]) == o['path']: inbox.append(i)
print('regions with the same path word AND whose stored reading box (LP ranges, 1e-9 rational rounding of the float bounds; guidance for the box, the path equality is exact) contains the example:', inbox,
      [(T[i][5], T[i][3]) for i in inbox][:1])
print('regions with path word ():', [i for i, x in enumerate(T) if tuple(x[0]) == ()], '(index 0: box rho_2..rho_7 in [1,7]; index 1: rho_7 = 9 exactly, rho_2..rho_6 in [1,7])')
for i in inbox:
    r = Md[i]; ws = windows(norm(r), 23)
    print('stored member of region', i, ':', [str(x) for x in r]); print('   its windows in [1,23]:', [(str(a), str(b)) for a, b in ws][:5], '... total', len(ws))
    print('   rule x for stored member:', [x for x in (1, 5, 9, 13, 17, 21)], 'readings in I(x) per x:', {x: sum(1 for q in norm(r) if (lambda m: m >= 0 and (x + 2) * q <= 8 * m + 7)((x * q - 1) // 8)) for x in (1, 5, 9, 13, 17, 21)})
ws = windows(rh, 23)
print('example windows in [1,23]:', [(str(a), str(b)) for a, b in ws])
found = []
for f in sorted(glob.glob('win_rec_taxo_*_v1.pkl')):
    for lab, r, w, *_ in pickle.load(open(f, 'rb')):
        if lab == ('taxo', 'grid+laps', 20982): found.append((f, [(str(a), str(b)) for a, b in w] == [(str(a), str(b)) for a, b in ws]))
print('window set of the example is stored (label (taxo, grid+laps, 20982)) in:', found)
print('J1 pickle win_rec_J1_0_v1.pkl holds label (J1, 0) = the stored member of region 0, not the example.')
print('--- K1z family: rho_7 = 7+d, rho_6 = 7*rho_7/9, readings 1,2,3,4,5 (landing R* = 9/rho_7)')
for d in (F(1, 10), F(1, 100), F(1, 1000), F(1, 10**6)):
    r7 = 7 + d; r6 = 7 * r7 / 9; rr = [F(1), F(2), F(3), F(4), F(5), r6, r7]
    o2 = outcome(rr); w2 = windows(rr, 23)
    print('  d =', d, 'moves', o2['nmoves'], 'R*', o2['R'], '=9/rho_7?', o2['R'] == 9 / r7, 'width', o2['width'], 'first window single point', w2[0][0] == w2[0][1] == o2['R'], 'verify', verify(rr, w2, 23))
print('--- near-AP bound (Lean ProgressionPairN hypothesis |d_j - j c| <= c/20): rho_7 = d_7/d_1 >= (7-1/20)/(1+1/20) =', F(139, 20) / F(21, 20), '> 3')
