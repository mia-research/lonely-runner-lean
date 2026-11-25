"""E943 rule-22 item (2026-11-25): the one skipped member whose shortest window's left end is not a state of the
cascade's path (short_window_v1).  Find it and print its path, its six-windows up to the skip and the window's ends.
"""
import pickle, sys
from fractions import Fraction as Fr
from math import floor
exec(open('short_window_v1.py').read().split("rec = pickle.load(open('/Users")[0])
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
off = int(sys.argv[1])
for idx in range(off, len(rec), 8):
    rs = sorted(Fr(x) for x in rec[idx][1]); six = rs[:6]
    Bk, n = bmove(six, rs[5], None)
    if Bk != 'skipped': continue
    ws = windows(six, E, T1); i = min(range(n + 1), key=lambda q: ws[q][1] - ws[q][0]); a, b, o = ws[i]
    st = states(rs)
    if a in st: continue
    print('index', idx, '| readings (floats, steer only)', [round(float(x), 6) for x in rs])
    T, path = cascade(rs, E); print('   R* =', 8 * T, '~', round(float(8 * T), 6), '| moves', len(path))
    print('   path states R (floats):', [round(float(8 * s), 6) for s in st])
    print('   six-windows up to the skip (R, floats):', [(round(float(8 * x), 6), round(float(8 * y), 6)) for x, y, oo in ws[:n + 1]])
    print('   shortest: window', i + 1, '| ends exit/entry:', edges(six, a, b), '| T inside it or before it:', T <= b, '| in the way at a:', [q + 1 for q in range(7) if blocked(rs[q], a)])
