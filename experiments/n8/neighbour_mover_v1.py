"""The landing bound with each reading as the one mover, held between its neighbours (2026-11-25).  Exact Fractions.

Owner (2026-11-25): runners are bound by their neighbours' speed; moving a reading past a neighbour is a restatement
of another arrangement.  So for readings r_1 = 1 < r_2 < ... < r_7, reading k (k = 2..7) moves in (r_{k-1}, r_{k+1})
(k = 7: (r_6, oo)) with the other six frozen (rule 3).  For each k, the walk of one_mover_bound_v1 (windows of the
frozen six from t0 = 1/8; v passes a window iff the window lies inside one zone of v [PROVISIONAL: covering; the claim
supported: B_k bounds R* for every position of reading k between its neighbours]) gives B_k = 8b at the first window
no position of the mover passes.  Then R* <= min_k B_k for the arrangement.  Population: E340's 110,081 members.
Reported: R* <= min_k B_k (check), min_k B_k in arc 0 / arc 1 / later, which k attains the minimum, the largest
min_k B_k, and how many B_k were skipped (pass set over 2*10^5 laps; only k = 7 has an unbounded range).
"""
import pickle, sys
from fractions import Fraction as Fr
from collections import Counter
exec(open('one_mover_bound_v1.py').read().split("if __name__")[0])

def bmove(six, lo, hi, limit=2 * 10 ** 5):
    ws = windows(six, E, T1); L = Fr(-1); J = None; A = None
    for n, (a, b, o) in enumerate(ws):
        if b - a > L:
            L = b - a; J = n
            vmax = Fr(1, 4) / L if L > 0 else Fr(10) ** 4
            if hi is not None: vmax = min(vmax, hi)
            P = passes(ws[J][0], ws[J][1], lo, vmax, limit=limit)
            if P is None: return 'skipped', n
            A = [(l, h) for l, h, k in P]
            for j in range(n + 1):
                if j != J and A: A = passes_in(ws[j][0], ws[j][1], A)
        else:
            A = passes_in(a, b, A)
        if not A: return 8 * b, n
    return None, None

rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
step = int(sys.argv[1]) if len(sys.argv) > 1 else 1; off = int(sys.argv[2]) if len(sys.argv) > 2 else 0
c = Counter(); best = None; worst_ratio = None
for r in rec[off::step]:
    rs = sorted(Fr(x) for x in r[1]); T, _ = cascade(rs, E); R = 8 * T
    Bs = {}
    for k in range(1, 7):
        six = rs[:k] + rs[k + 1:]
        lo, hi = rs[k - 1], (rs[k + 1] if k < 6 else None)
        Bk, n = bmove(six, lo, hi)
        if Bk == 'skipped': c['B_k skipped, k = %d' % (k + 1)] += 1; continue
        if Bk is None: c['B_k none below 39, k = %d' % (k + 1)] += 1; continue
        Bs[k + 1] = Bk
        if R > Bk: c['FAIL: R* > B_k'] += 1
    if not Bs: c['no B_k'] += 1; continue
    m = min(Bs.values()); km = [k for k in Bs if Bs[k] == m]
    side = 'R*<=7' if R <= 7 else 'R*>=9'
    c[(side, 'min B in arc 0' if m <= 7 else ('min B in arc 1' if m <= 15 else 'min B later'))] += 1
    c[(side, 'min attained by k = ' + ','.join(map(str, km)))] += 1
    c[(side, 'min B = R* exactly' if m == R else 'min B > R*')] += 1
    if best is None or m > best[0]: best = (m, R, km, rs)
for k, v in sorted(c.items(), key=str): print(v, k)
m, R, km, rs = best
print('largest min_k B_k =', m, '~', round(float(m), 6), '(floats steer only) | its R* =', R, '~', round(float(R), 6), '| k =', km)
print('   readings', [str(x) for x in rs])
