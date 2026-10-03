# tie_instants_v1.py -- where single-point windows sit (R0), which readings touch, integer-reading law check. Exact Fractions.
import pickle, glob, itertools
from fractions import Fraction as F
from collections import Counter, defaultdict
exec(open('win_lib_v1.py').read())
def posr(R, r): return (R * r) % 8
def parts(R0, rh):
    ps = [posr(R0, r) for r in rh]
    ex = [(i + 1, int((R0 * r - 1) / 8)) for i, (r, p) in enumerate(zip(rh, ps)) if p == 1]
    en = [(i + 1, int((R0 * r + 1) / 8)) for i, (r, p) in enumerate(zip(rh, ps)) if p == 7]
    return ex, en
sets = {}
for f in sorted(glob.glob('win_rec_*_v1.pkl')):
    sets.setdefault(f.split('win_rec_')[1].split('_')[0], []).extend(pickle.load(open(f, 'rb')))
print('== A. R0 of every single-point window, by involvement of reading 1 (rank 1) and integrality of R0')
for name, recs in sets.items():
    C = Counter(); ex1 = {}
    for rec in recs:
        rh = norm(rec[1])
        for w in rec[2]:
            if w[0] != w[1]: continue
            R0 = w[0]; ex, en = parts(R0, rh)
            a1 = any(e[0] == 1 for e in ex); b1 = any(e[0] == 1 for e in en)
            # exit by reading 1 at lap 0 is the start (R0 = 1)
            key = ('R0=1' if R0 == 1 else ('R0 int' if R0.denominator == 1 else 'R0 non-int'),
                   'reading1 exits' if a1 else ('reading1 enters' if b1 else 'neither'))
            C[key] += 1
            if R0.denominator == 1: C[('R0 value', int(R0))] += 1
    print(name, sorted((k, v) for k, v in C.items() if k[0] != 'R0 value'))
    print('   integer R0 values:', sorted((k[1], v) for k, v in C.items() if k[0] == 'R0 value'))
print('== B. integer readings (lat1, exhaustive 5005): odd-integer-instant law')
bad = 0; nchk = 0; evenpt = 0; nonint_pt = 0
for lab, rh0, ws, *_ in sets['lat1']:
    rh = norm(rh0); ints = [int(r) for r in rh]
    has0 = any(c % 8 == 0 for c in ints)
    pts = {w[0] for w in ws if w[0] == w[1]}
    for r in range(1, 24):
        pred = (r % 2 == 1) and (not has0) and any(c % 8 == r % 8 for c in ints) and any(c % 8 == (-r) % 8 for c in ints) and r > 1
        pred_start = (r == 1) and (not has0) and any(c % 8 == 7 for c in ints)
        # r==1: start window is a point iff some reading = 7 mod 8 (p=7 at R=1); reading 1 supplies the p=1 side
        got = F(r) in pts
        nchk += 1
        if got != (pred or pred_start): bad += 1
    for p in pts:
        if p.denominator != 1: nonint_pt += 1
        elif int(p) % 2 == 0: evenpt += 1
print('instants checked', nchk, 'violations', bad, '; point windows at non-integer R0:', nonint_pt, '; at even integer R0:', evenpt)
