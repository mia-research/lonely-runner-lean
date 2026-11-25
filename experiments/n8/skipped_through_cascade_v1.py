"""E940 item 6, first exception, through the cascade (2026-11-25).  Exact Fractions.
The members of E340 whose walk for the fastest reading was skipped by neighbour_mover_v1 (B_7 'skipped').
For each: (a) the window lengths met before the skip: the longest of them, and whether it is below 10^-9 (a
near-point window, a pinned face of the member's LP cell, E341); (b) the cascade: R*, the six-window holding T, and
the landing kind (t0 / opening of a six-window / an exit of the fastest reading v inside one); how many six-windows
before T the reading v nests; (c) the walk with deferral: windows whose pass set exceeds the lap limit are kept
aside until a longer window caps v, then applied; the intersection is order-free, so the first empty intersection
still gives a bound 8b >= R* [PROVISIONAL: covering; the claim supported: B_7 bounds R* for every fastest reading].
The same (b) is tallied for the members that were not skipped, for comparison.
"""
import pickle, sys
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter
exec(open('neighbour_mover_v1.py').read().split("rec = pickle.load")[0])

def bdefer(six, lo, limit=2 * 10 ** 5):
    ws = windows(six, E, T1); L = Fr(-1); A = None; built = False
    for n, (a, b, o) in enumerate(ws):
        newlong = b - a > L
        if newlong: L = b - a
        if not built or newlong:
            vmax = Fr(1, 4) / L if L > 0 else Fr(10) ** 4
            J = max(range(n + 1), key=lambda i: ws[i][1] - ws[i][0])
            P = passes(ws[J][0], ws[J][1], lo, vmax, limit=limit)
            if P is None: continue
            A = [(l, h) for l, h, k in P]
            for j in range(n + 1):
                if j != J and A: A = passes_in(ws[j][0], ws[j][1], A)
            built = True
        else:
            A = passes_in(a, b, A)
        if not A: return 8 * b, n
    return None, None

def landing_kind(rs, T):
    six, v = rs[:6], rs[6]
    ws = windows(six, E, T + Fr(1, 8))
    hold = [i for i, (a, b, o) in enumerate(ws) if a <= T <= b]
    if not hold: return 'T in no six-window (FAIL)', None, 0
    i = hold[0]; a, b, o = ws[i]
    nested = sum(1 for (x, y, oo) in ws[:i] if any((8 * k - 1) / (8 * x) < v < (8 * k + 1) / (8 * y) for k in [floor(v * x + E)]))
    if T == E: kind = 't0'
    elif T == a: kind = 'opening of a six-window'
    elif (8 * v * T - 1) % 8 == 0: kind = 'exit of the fastest reading inside a six-window'
    else: kind = 'other (FAIL)'
    return kind, i + 1, nested

rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
step = int(sys.argv[1]) if len(sys.argv) > 1 else 1; off = int(sys.argv[2]) if len(sys.argv) > 2 else 0
c = Counter(); longest_skip = Fr(0)
for r in rec[off::step]:
    rs = sorted(Fr(x) for x in r[1]); six = rs[:6]
    T, path = cascade(rs, E); R = 8 * T
    Bk, n = bmove(six, rs[5], None)
    grp = 'skipped' if Bk == 'skipped' else 'not skipped'
    c[(grp, 'members')] += 1
    kind, i, nested = landing_kind(rs, T)
    c[(grp, 'landing: ' + kind)] += 1
    c[(grp, 'R*<=7' if R <= 7 else 'R*>=9')] += 1
    c[(grp, 'v nests every six-window before T' if i is not None and nested == i - 1 else 'v leaves some earlier six-window (FAIL)')] += 1
    if grp == 'skipped':
        ws = windows(six, E, T1)
        Lsk = max(b - a for a, b, o in ws[:n + 1])
        if Lsk > longest_skip: longest_skip = Lsk
        c[(grp, 'longest window met before the skip below 10^-9' if Lsk < Fr(1, 10 ** 9) else 'longest window met before the skip at least 10^-9')] += 1
        Bd, nd = bdefer(six, rs[5])
        c[(grp, 'deferred walk: no bound' if Bd is None else ('deferred walk: R* <= B_7' if R <= Bd else 'deferred walk: R* > B_7 (FAIL)'))] += 1
        if Bd is not None: c[(grp, 'deferred B_7 ' + ('<= 7' if Bd <= 7 else ('in [9, 15]' if Bd <= 15 else '> 15')))] += 1
for k, v in sorted(c.items(), key=str): print(v, k)
print('longest window met before a skip:', longest_skip, '~', float(longest_skip), '(float steers only)')
