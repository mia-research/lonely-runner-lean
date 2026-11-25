"""Wall-window index, test v5 (2026-11-25).  Exact Fractions; the cascade is the oracle.

Setting (E929): d = r_1, S = readings <= 7d, F = the rest; S's clear set from t0 = 1/(8d) is windows W_1, W_2, ...
with W_1 = [t0, 7/(8 max S)].  T lies in W_i, and i is the first window holding an F-clear instant (E929 item 1).
Question: what, in the readings, makes F pass a window?  For each window W_j = [a, b] with j < i (F passes it) and for
W_i, record F's cascade from a:
  moves  = number of F moves before the state leaves [a, b] (passes) or fixes (lands);
  single = F passes W_j in ONE move: one F reading's zone covers all of [a, b];
  span   = which F readings set the passing moves (rank in F, lap = floor(r t) at the move);
  len    = the window's length in laps of F's slowest reading, (b - a) * min F, as a Fraction, binned by quarters.
Positions start at 1 (rule 5).  Populations as E929: Z16, Q (seed 1), W40 (seed 6).
"""
import itertools, random, sys
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter

E = Fr(1, 8)
def blocked(r, t):
    x = r * t; f = x - floor(x)
    return f < E or f > 1 - E
def nxt(r, t):
    return (ceil(r * t - E) + E) / r
def cascade(rs, t, cap=100000):
    st = []
    for _ in range(cap):
        b = [r for r in rs if blocked(r, t)]
        if not b: return t, st
        m = max(nxt(r, t) for r in b)
        st.append(min(r for r in b if nxt(r, t) == m)); t = m
    raise RuntimeError('cap')

def windows(S, t0, T1):
    zones = []
    for r in S:
        for m in range(max(0, floor(r * t0) - 1), floor(r * T1) + 2):
            if m == 0: continue
            zones.append(((m - E) / r, (m + E) / r, r, m))
    zones.sort()
    out = []; cur = t0; opener = None
    for a, b, r, m in zones:
        if b <= cur: continue
        if a > T1: break
        if a >= cur: out.append((cur, a, opener))
        if b > cur: cur = b; opener = (r, m)
        if cur > T1: break
    if cur <= T1: out.append((cur, T1, opener))
    return out

def f_run(Fs, a, b):
    """F's cascade from a, stopped once the state leaves [a, b]; returns (moves, passed, setters, state)."""
    t = a; moves = 0; setters = []
    while True:
        bl = [r for r in Fs if blocked(r, t)]
        if not bl: return moves, False, setters, t
        m = max(nxt(r, t) for r in bl)
        s = min(r for r in bl if nxt(r, t) == m)
        setters.append((Fs.index(s) + 1, floor(s * t + E)))
        moves += 1; t = m
        if t > b: return moves, True, setters, t

tab = Counter(); ex = {}
def note(key, item=None):
    tab[key] += 1
    if item is not None:
        ex.setdefault(key, [])
        if len(ex[key]) < 2: ex[key].append(item)

def qbin(x):
    q = floor(4 * x)
    return '>=2' if q >= 8 else '[%s,%s)' % (Fr(q, 4), Fr(q + 1, 4))

def case(pop, rs, label):
    rs = sorted(rs); d = rs[0]; t0 = E / d
    S = [r for r in rs if r <= 7 * d]; Fs = [r for r in rs if r > 7 * d]
    if not Fs: return
    T, _ = cascade(rs, t0)
    ws = windows(S, t0, T + 1)
    i = next(k for k, (a, b, o) in enumerate(ws) if a <= T <= b)
    fmin = Fs[0]
    for j in range(i + 1):
        a, b, o = ws[j]
        moves, passed, setters, st = f_run(Fs, a, b)
        assert passed == (j < i), (pop, label, j, i)          # forced by E929 item 1; checked
        L = (b - a) * fmin
        tag = 'passes' if passed else 'lands'
        note((pop, 'W%d' % min(j + 1, 3), tag, 'moves %s' % (moves if moves < 4 else '>=4')))
        note((pop, 'W%d' % min(j + 1, 3), tag, 'len in min-F laps %s' % qbin(L)))
        if passed:
            note((pop, 'W%d' % min(j + 1, 3), 'passes', 'single' if moves == 1 else 'chain',
                  'first setter F rank %d of %d' % (setters[0][0], len(Fs))),
                 (label, [str(x) for x in rs], str(a), str(b), setters))

def readings(v, k):
    return [abs(v[i] - v[k]) for i in range(len(v)) if i != k]

pops = sys.argv[1:] or ['Z16', 'Q', 'W40']
if 'Z16' in pops:
    for v in itertools.combinations(range(1, 17), 8):
        for k in range(8):
            case('Z16', [Fr(x) for x in readings(v, k)], (v, k))
if 'Q' in pops:
    rng = random.Random(1)
    for _ in range(3000):
        gaps = [Fr(rng.randint(6, 24), 12) for _ in range(7)]
        v = [Fr(1)]
        for g in gaps: v.append(v[-1] + g)
        for k in range(8):
            case('Q', readings(v, k), ([str(g) for g in gaps], k))
if 'W40' in pops:
    rng = random.Random(6); seen = 0
    while seen < 2900:
        others = sorted(set(Fr(rng.randint(13, 480), 12) for _ in range(6)))
        if len(others) < 6: continue
        seen += 1
        case('W40', [Fr(1)] + others, seen)

for kk, vv in sorted(tab.items(), key=lambda x: str(x[0])):
    print(vv, kk)
    for e in ex.get(kk, [])[:1]: print('      e.g.', e)
