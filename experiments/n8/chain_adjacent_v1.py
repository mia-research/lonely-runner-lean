# E823: (1) consecutive chain pieces never come from the same (window, shift); (2) pieces of the least-lo window at shift 0 (A) per period 1/lo_min; every piece shorter than 1/lo_min.
import pickle
from fractions import Fraction as F
res = pickle.load(open('chain_pieces_v1.pkl', 'rb'))
in53 = {tuple(map(int, l.split(','))) for l in open('core_cover_cores.txt') if l.strip()}
same_adj = 0; pairs = 0; longer = 0; npieces = 0
def med(q): q = sorted(q); return q[len(q) // 2]
for tag, f in [('53', True), ('others, chain >= 5', False)]:
    sel = [r for r in res if (r[0] in in53) == f and (f or len(r[3]) >= 5)]
    per = []
    for core, T, y0, ch in sel:
        lo_min = min(p[2] for p in ch)
        nA = sum(1 for p in ch if p[2] == lo_min and p[4] == 0)
        Np = (y0 - F(3, 8)) * lo_min
        per.append((F(len(ch)) / Np if Np else None, F(nA) / Np if Np else None, nA, Np, len(ch)))
    per2 = [x for x in per if x[0] is not None]
    print(tag, len(sel), 'chain pieces per period of the first window: min', min(x[0] for x in per2), 'median', med([x[0] for x in per2]), 'max', max(x[0] for x in per2), '; A pieces per period: min', min(x[1] for x in per2), 'median', med([x[1] for x in per2]), 'max', max(x[1] for x in per2))
for core, T, y0, ch in res:
    lo_all = None
    for (a, b, lo, hi, d, k), (a2, b2, lo2, hi2, d2, k2) in zip(ch, ch[1:]):
        pairs += 1
        if (lo, hi, d) == (lo2, hi2, d2): same_adj += 1
    for a, b, lo, hi, d, k in ch:
        npieces += 1
        if b - a >= 1 / lo: longer += 1
print('consecutive chain pairs', pairs, 'from the same (window, shift):', same_adj, '; pieces of length >= 1/lo of their own window:', longer, 'of', npieces)
