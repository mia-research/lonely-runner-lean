"""Wall-window split on E340's members, test v9 (2026-11-25).  Exact Fractions; the cascade is the oracle.

Population: the 110,081 J=2 members of E340 (`LonelyRunner/experiments/nN/redo/disc_records_v1.pkl`; record r: r[1] the
seven readings with d_min = 1, r[2] the landing R* in units R = 8 d_min t, r[5] the states, r[6] the moves).  E340's
4,939 gate crossers (R* >= 9) break E929's cap T <= 7/(8 d_min); E929 marks why their chain covers d_min's first
window as not understood.  The split of E929 to E931 is run on every member, crossers and the rest reported apart:
  (0) T = R*/8 (this script's cascade against the stored record);
  (1) E929 item 1: T is F's cascade from the opening of the S window holding it (asserted);
  (2) the windows of S inside d_min's first window [1/8, 7/8]: how many, and how F passes each (E930: one move, with
      the predicate checked; E931: two or more moves, with the link condition and the interval-merge cover checked);
  (3) the window holding T: its index, its opener (reading rank in S, lap), whether T is the opening.
Readings are positive speeds' differences; no runner at speed 0 is constructed (rule 5).
"""
import pickle, sys
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter
exec(open('wall_window_chain_v7.py').read().split("def readings(v, k):")[0])
def onemove_pred(Fs, a, b):          # as wall_window_index_v6.py (E930 item 1)
    hits = []
    for f in Fs:
        for k in range(max(1, floor(8 * a * f / 8) - 1), floor(f * b) + 2):
            if Fr(8 * k - 1, 8) / a < f < Fr(8 * k + 1, 8) / b: hits.append((Fs.index(f) + 1, k))
    return hits

PKL = sys.argv[1] if len(sys.argv) > 1 else \
    '/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl'
rec = pickle.load(open(PKL, 'rb'))
c = Counter(); ex = {}
def note(key, item=None):
    c[key] += 1
    if item is not None and key not in ex: ex[key] = item

for r in rec:
    rs = sorted(r[1]); d = rs[0]; t0 = E / d
    grp = 'crosser' if r[2] >= 9 else 'rest'
    S = [x for x in rs if x <= 7 * d]; Fs = [x for x in rs if x > 7 * d]
    T, _ = cascade(rs, t0)
    note((grp, '(0) T == R*/8', T == r[2] / 8), None if T == r[2] / 8 else (r[0], str(T), str(r[2])))
    if not Fs:
        note((grp, 'F empty')); continue
    ws = windows(S, t0, T + 1)
    i = next(k for k, (a, b, o) in enumerate(ws) if a <= T <= b)
    a, b, o = ws[i]
    TF, _ = cascade(Fs, a)
    note((grp, '(1) T == F cascade from the opening', TF == T))
    inside = [w for w in ws if w[1] <= Fr(7, 8) / d]
    note((grp, '(2) S windows inside [1/8, 7/8]', len(inside)))
    note((grp, '(2) T beyond 7/8' if T > Fr(7, 8) / d else '(2) T inside [1/8, 7/8]'))
    for j in range(i + 1):
        aj, bj, oj = ws[j]
        ch, passed, st = f_chain(Fs, aj, bj)
        assert passed == (j < i)
        hits = onemove_pred(Fs, aj, bj)
        one = passed and len(ch) == 1
        note((grp, '(2) E930 predicate agrees', bool(hits) == one))
        note((grp, '(2) E931 pass == cover', passed == covered(Fs, aj, bj)))
        for n in range(1, len(ch)):
            s0, k0 = ch[n - 1][0], ch[n - 1][1]; s1, k1 = ch[n][0], ch[n][1]
            note((grp, '(2) E931 link condition', Fr(8 * k1 - 1, 8 * k0 + 1) < s1 / s0 < Fr(8 * k1 + 1, 8 * k0 + 1)))
        if passed:
            where = 'inside [1/8,7/8]' if bj <= Fr(7, 8) / d else 'beyond 7/8'
            note((grp, '(2) passed window', where, 'one move' if one else 'two or more moves'))
    op = 't0' if o is None else ('d lap %d' % o[1] if o[0] == d else 'S rank %d of %d lap %d' % (S.index(o[0]) + 1, len(S), o[1]))
    note((grp, '(3) window holding T: index %s' % (i + 1 if i < 5 else '>=6'), 'opener ' + op if i else 'opener t0'))
    note((grp, '(3) T is the opening' if T == a else '(3) T is an F exit'))

for k, v in sorted(c.items(), key=lambda x: str(x[0])):
    print(v, k)
    if k in ex: print('      e.g.', ex[k])
