"""Wall-window law, test v4 (2026-11-25).  Exact Fractions; the cascade is the oracle.

Split named from the readings before the landing: d = r_1, S = readings <= 7d, F = the rest (as v1).
S's clear set from t0 = 1/(8d) is a union of windows [a_i, b_i]; each end is a zone edge (8m +- 1)/(8r) of an S reading.
Forced (E757 ChainCarried, chain_next_piece / chain_landing [L]): T lies in some window of S, and inside it T is F's
cascade started at that window's left end.  Recorded per case (not forced): the index i of the window holding T; the
reading r of S and lap m whose exit (8m+1)/(8r) opens that window; whether F's cascade from a_i fixes inside it; for
i = 1 the window [t0, 7/(8 max S)] of v1.  Also the largest lap m of any S edge met before T (S's laps in play).
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
    """Windows of S's common clear set in [t0, T1], with the opener (reading, lap) of each (None for t0)."""
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

tab = Counter(); ex = {}
def note(key, item):
    tab[key] += 1
    ex.setdefault(key, [])
    if len(ex[key]) < 3: ex[key].append(item)

def case(pop, rs, label):
    rs = sorted(rs); d = rs[0]; t0 = E / d
    S = [r for r in rs if r <= 7 * d]; Fs = [r for r in rs if r > 7 * d]
    T, st = cascade(rs, t0)
    if not Fs:
        note((pop, 'F empty'), label); return
    ws = windows(S, t0, T + 1)
    i = next(k for k, (a, b, o) in enumerate(ws) if a <= T <= b)
    a, b, o = ws[i]
    TF, _ = cascade(Fs, a)
    assert TF == T, (pop, label)      # forced (E757); checked
    maxlap = max([w[2][1] for w in ws[:i + 1] if w[2]] or [0])
    if i == 0:
        note((pop, 'window 1'), label)
    else:
        r, m = o
        rank = S.index(r) + 1
        note((pop, 'window %d' % min(i + 1, 4), 'opener: S rank %s of %d' % ('max' if r == max(S) else rank, len(S)), 'lap %d' % m), (label, [str(x) for x in rs], str(T)))
    tab[(pop, 'S laps in play up to T: max %d' % maxlap)] += 1

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
    if kk in ex and 'laps in play' not in str(kk):
        for e in ex[kk][:2]: print('      e.g.', e)
