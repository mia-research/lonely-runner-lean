# tmpl_supj_v1 -- within a template, the top upper end of R2 is (8j+1)/b for the right end b of a window; split by (window, j)  (exact)
import pickle, glob, signal
from collections import defaultdict, Counter
exec(open('tmpl_lib_v1.py').read()); signal.alarm(500)
def dec(x, k=5):
    x = F(x); n = x.numerator * 10**k // x.denominator; return '%d.%0*d' % (n // 10**k, k, n % 10**k)
cr = {}
for f in sorted(glob.glob('tmpl_rec_*_v1.pkl')):
    d = pickle.load(open(f, 'rb'))
    for n, rh, tid in d['cross']: cr.setdefault(rh, d['tlist'][tid])
X24 = (F(1),F(2752864293769,970238379379),F(3691147638604,961559468885),F(4851775667488,988103849833),F(5240560485773,830842598345),F(2806730537001,400961505286),F(474233610200591258564537783,19451412054102649094869700))
cr[X24] = template(list(X24))[0]
r2 = {}
for f in sorted(glob.glob('tmpl_r2_*_v1.pkl')):
    for rh, iv, unb, own in pickle.load(open(f, 'rb'))['out']: r2[rh] = iv
# exact identity sup = rho_y' (8j+1)/(8j'-1) for X24
sup = r2[X24][-1][1]; print('X24: sup R2 == 129*rho_2/15 :', sup == F(129) * X24[1] / 15, '; == (8*16+1)/b with b = 15/rho_2 (entry e2.2)')
T = cr[X24]; print('X24 template windows (exact):', [(str(a), str(b)) for a, b in windows(list(X24))][:3], '...')
by = defaultdict(list)
for rh, T in cr.items():
    iv = r2[rh]; hi = iv[-1][1]; W = windows(list(rh))
    for k, (a, b) in enumerate(W):
        x = hi * b - 1
        if x.denominator == 1 and x.numerator % 8 == 0 and x.numerator > 0:
            by[T].append((lab(T[k][1]), x.numerator // 8, hi, rh[6])); break
T0 = cr[X24]
print('template', tstr(T0), 'n', len(by[T0]))
g = defaultdict(list)
for l, j, hi, r7 in by[T0]: g[(l, j)].append(hi)
for k, v in sorted(g.items()): print('   top bound attained as (8j+1)/b at right end', k[0], 'with j =', k[1], ': tuples', len(v), 'sup range [%s, %s]' % (dec(min(v)), dec(max(v))))
print('templates with more than one attaining (label, j) pair:', sum(1 for T, v in by.items() if len({(l, j) for l, j, h, r in v}) > 1), 'of', len(by))
print('pairs (label, j) attaining, over all templates, with j >= 7:', sorted(Counter((l, j) for v in by.values() for l, j, h, r in v if j >= 7).items()))
print('largest j (lap of reading 7 whose zone contains the top component):', max(j for v in by.values() for l, j, h, r in v))
