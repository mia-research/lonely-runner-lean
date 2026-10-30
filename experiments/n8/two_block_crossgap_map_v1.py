"""E648. Map of the records of two_block_strip_cascade_v1 where the subject's nearest reading is NOT its own block's
step (cross-gap end runners, interleaved blocks). For each: the own block's exact clear set (components of the
complement of the open zones ((m-1/8)/d, (m+1/8)/d) of the own-block readings), the index of the component holding the
landing, R_own = 8 u t, and whether the landing is also in a window of the OTHER block's own clear set (from the
subject's view, the other block's readings). Exact Fractions."""
import pickle, math
from fractions import Fraction as F
from collections import Counter
E = F(1, 8)
recs = pickle.load(open('two_block_strip_cascade_v1.pkl', 'rb'))
def sp(p, A, b): return [F(i) for i in range(p)] + [A + j * b for j in range(8 - p)]
def clear_components(ds, T):
    zones = sorted(((m - E) / d, (m + E) / d) for d in ds for m in range(0, int(d * T) + 2))
    comps = []; cur = F(0)
    for a, b in zones:
        if a > cur: comps.append((cur, a))
        cur = max(cur, b)
    return comps  # closed components [cur, a]; first one starts at 0 only if no zone at 0 (zone m=0 covers (-1/8d,1/8d))
def comp_index(comps, t):
    for i, (a, b) in enumerate(comps):
        if a <= t <= b: return i + 1
    return None
tab = Counter(); n = 0
for (p, b, G, k, t, op, M, mv, R, r) in recs:
    A = G + (p - 1); v = sp(p, A, b)
    own = list(range(p)) if k < p else list(range(p, 8)); oth = [i for i in range(8) if i not in own]
    u = F(1) if k < p else b
    dsall = [abs(v[i] - v[k]) for i in range(8) if i != k]
    if min(dsall) >= u: continue
    n += 1
    dso = [abs(v[i] - v[k]) for i in own if i != k]; dsx = [abs(v[i] - v[k]) for i in oth]
    io = comp_index(clear_components(dso, t + 1), t)
    ix = comp_index(clear_components(dsx, t + 1), t)
    nearest = min(dsx)
    Rx = 8 * nearest * t  # in units of the cross neighbour
    reg = 'interleaved' if G <= 0 else 'gap'
    who = op[0] if op[0] == 'start' else ('own' if op[1] in own else 'other')
    tab[(reg, who, 'own win %s' % io, 'R_own<8' if 8 * u * t < 8 else 'R_own>=8',
         'other-block win %s' % ix, 'R_cross<=7' if Rx <= 7 else 'R_cross>7')] += 1
print("records with nearest reading across the gap / interleaved:", n)
for kk, vv in sorted(tab.items(), key=lambda x: -x[1])[:40]: print(vv, kk)
