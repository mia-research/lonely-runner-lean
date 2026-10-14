"""E426 (2026-10-07), quarter_left_eighth_v1: the sets that quarter_coincidence_v1 leaves (no lonely quarter instant at
any pair's grid), searched exactly at the eighth-level reduction points tau = m/w (w an odd reading, m = 1..w-1) and,
failing that, at the eighth-level coincidence points tau = j/h (8h = |a -+ b| for two non-multiples of 8), at the
eight shifts (tau + k)/8.  Populations: (3,4) (o,o,o,o) in [1, 40]; (2,5) (f,o,o,o,o) in [1, 40]; (1,6) (f,f,o,o,o,o)
in [1, 36]; gcd 1.  Exact.
"""
import sys, itertools, collections
from math import gcd
from functools import reduce
from fractions import Fraction as F
sys.path.insert(0, '.')
from quarter_coincidence_v1 import quarter_pair, lonely
def eighth_reduction(S):
    W = [d for d in S if d % 2]
    for w in W:
        for m in range(1, w):
            for k in range(8):
                if lonely(S, (F(m, w) + k) / 8): return ('reduction', w)
    return None
def eighth_coinc(S):
    NM = [d for d in S if d % 8]
    for a, b in itertools.combinations(NM, 2):
        for s in (a - b, a + b):
            if s and s % 8 == 0:
                h = abs(s) // 8
                for j in range(1, h):
                    for k in range(8):
                        if lonely(S, (F(j, h) + k) / 8): return ('coincidence8', a, b)
    return None
OUT = open('quarter_left_eighth_v1.out', 'w'); OUT.write(__doc__ + '\n')
for (m, f, N) in ((3, 0, 40), (2, 1, 40), (1, 2, 36)):
    c = collections.Counter(); ex = []
    mults = list(range(8, N + 1, 8)); fours = list(range(4, N + 1, 8)); odds = list(range(1, N + 1, 2))
    for M in itertools.combinations(mults, m):
        for Fo in itertools.combinations(fours, f):
            for W in itertools.combinations(odds, 4):
                S = M + Fo + W
                if reduce(gcd, S) > 1: continue
                r = quarter_pair(S)
                if r not in (None, False) and not isinstance(r[0], str): continue
                c['left by quarter'] += 1
                if eighth_reduction(S): c['eighth reduction'] += 1; continue
                if eighth_coinc(S): c['eighth coincidence'] += 1; continue
                c['left'] += 1
                if len(ex) < 12: ex.append(S)
    line = '%s %s %s' % ((m, f, N), dict(c), ex); print(line); OUT.write(line + '\n')
