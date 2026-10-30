"""E647. Exact cascade across the small-gap strip of the two-block template (E646 item 4).
Speeds (any c > 0, positive): c, c+1, ..., c+(p-1) | c+A, c+A+b, ..., c+A+(7-p)b, gap G = A-(p-1).
Strip: p = 2..6, b != 1 on a rational grid, 0 < G < Gcov(p,b) (E646), and interleaved G <= 0 down to -(p-1) with no
equal speeds. For every subject k the readings are |v_i - v_k|. The cascade is copied unchanged from
catalogue_by_outcome_v1.py (start 1/(8 d_min), largest next opening). Oracle check C1: the landing equals the first
instant >= 1/(8 d_min) at which every reading is clear, computed without the cascade by scanning the openings
(M + 1/8)/d in increasing order. Recorded: the opener (block of the opener relative to the subject, its position),
lap M, moves, R = 8 d_min t. Exact Fractions; no floats."""
import math, sys, pickle
from fractions import Fraction as F
from collections import Counter, defaultdict
sys.path.insert(0, '.')
from two_block_remainder_v1 import gcov
E = F(1, 8)
def dist(x):
    f = x - math.floor(x); return min(f, 1 - f)
def cascade(r):
    t = F(1, 8 * r[0]); last = None; moves = 0
    while True:
        way = [(i, d) for i, d in enumerate(r) if dist(d * t) < E]
        if not way: return t, last, moves
        best = None
        for i, d in way:
            M = round(d * t)
            nt = (F(M) + E) / d
            if best is None or nt > best[0]: best = (nt, i, M)
        t, i, M = best; last = (i, M); moves += 1
def first_lonely(r, upto):
    cands = sorted({(F(M) + E) / d for d in r for M in range(0, int(d * upto) + 1)} | {F(1, 8 * r[0])})
    for t in cands:
        if t < F(1, 8 * r[0]) or t > upto: continue
        if all(dist(d * t) >= E for d in r): return t
    return None
def speeds(p, A, b):
    return [F(i) for i in range(p)] + [A + j * b for j in range(8 - p)]
bs = sorted({F(n, 12) for n in range(1, 97)} - {F(1)})
recs = []; c1_bad = 0; n = 0
for p in range(2, 7):
    for b in bs:
        gc, _ = gcov(p, b)
        m = max(F(1), b)
        step = m / 8
        Gs = []
        j = -8 * (p - 1)  # interleaved down to G = -(p-1) in steps of 1/8 (first-block units)
        while F(j, 8) <= 0:
            Gs.append(F(j, 8)); j += 1
        G = step
        while G < gc:
            Gs.append(G); G += step
        for G in Gs:
            A = G + (p - 1)
            v = speeds(p, A, b)
            if len(set(v)) < 8: continue
            for k in range(8):
                rd = sorted((abs(x - v[k]), i) for i, x in enumerate(v) if i != k)
                r = [d for d, _ in rd]; who = [i for _, i in rd]
                t, last, mv = cascade(r); n += 1
                if first_lonely(r, t) != t: c1_bad += 1
                if last is None: op = ('start', who[0]); M = 0
                else: op = ('set', who[last[0]]); M = last[1]
                recs.append((p, b, G, k, t, op, M, mv, 8 * r[0] * t, r))
print("cascades:", n, " C1 violations:", c1_bad)
pickle.dump(recs, open('two_block_strip_cascade_v1.pkl', 'wb'))
