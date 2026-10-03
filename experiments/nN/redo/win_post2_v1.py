import pickle, glob
from fractions import Fraction as F
fl = lambda x: '%.9f' % float(x)
J1 = []
for fn in sorted(glob.glob('win_rec_J1_*_v1.pkl')): J1 += pickle.load(open(fn, 'rb'))
def arr(rh): return str(rh)
ni = [r for r in J1 if all(x.denominator != 1 for x in r[1][1:])]
for nm, rec in (('all J1', J1), ('J1 no integer reading', ni)):
    best = None; bf = None
    for lab, rh, ws in rec:
        for a, b in ws:
            if b > a and (best is None or b - a < best[0]): best = (b - a, lab, rh, ws, (a, b))
        a, b = ws[0]
        if b > a and (bf is None or b - a < bf[0]): bf = (b - a, lab, rh, ws, (a, b))
    print(nm, 'narrowest positive window', best[0], '(~%s)' % fl(best[0]), best[1], 'window', best[4], 'arrangement', arr(best[2]))
    print(nm, 'narrowest positive FIRST window', bf[0], '(~%s)' % fl(bf[0]), bf[1], 'window', bf[4], 'arrangement', arr(bf[2]))
    lat = max(rec, key=lambda r: r[2][0][0]); print(nm, 'latest first window', lat[2][0], lat[0], 'arrangement', arr(lat[1]))
    fw = min(rec, key=lambda r: len(r[2])); print(nm, 'fewest windows', len(fw[2]), fw[0])
