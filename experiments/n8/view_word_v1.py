"""View words, test v1 (2026-11-25).  Exact Fractions; the cascade is the oracle.

Owner (2026-11-25): existence comes from the AP and phi(n); the question is arrangement finiteness (goal G2).
E932: the cascade's words, written in laps, grow with the readings' scale.  E747/E748/E754 [L]: every cascade state is a
class-1 instant (8M+1)/(8p) of its setter p, and at it a reading f sits at ((n mod 8) + (8M+1) eps)/8 mod 1, where
(n, eps) is f's view on the grid through p (n = floor(f/p + 1/2), eps = f/p - n in [-1/2, 1/2)).  The lap M enters
only through the rotation (8M+1) eps; the residue n mod 8 does not depend on M.
Recorded, per (arrangement, subject):
  - the landing's setter p*, its lap M*, and for every reading the view letter at the landing:
      (n mod 8, w) with w = (n mod 8) + (8M*+1) eps, and its window index j = the integer with
      8j+1 <= w <= 8j+7 (clear; E747);
  - the path: each move's letter for the new setter s at the old state (8M+1)/(8p):
      (n mod 8 of s through p, J) with (n mod 8) + (8M+1) eps in (8J - 1, 8J + 1) (blocked);
  - LANDING TYPE = (residue vector through p*, window-index vector) over the readings other than p*, sorted;
    PATH TYPE = tuple of path letters.
Counted per population: distinct landing types, distinct path types, the largest |j|, |J|, M*.
Populations: E929's Z16, Q (positions from 1, rule 5), W40; and W80, W160 (E932's W recipe, readings to 80 and 160) to
see growth with scale.
"""
import itertools, random, sys
from fractions import Fraction as Fr
from math import floor
from collections import Counter
E = Fr(1, 8)
def dist(x): x = x - floor(x); return min(x, 1 - x)
def blocked(r, t): return dist(r * t) < E
def ex(r, t): return (floor(r * t + E) + E) / r           # exit of r's current zone
def view(f, p):
    n = floor(f / p + Fr(1, 2)); return n, f / p - n
def cascade(rs):
    d = min(rs); t = E / d; p, M = d, 0; path = []
    while True:
        bl = [r for r in rs if blocked(r, t)]
        if not bl: return t, p, M, path
        m = max(ex(r, t) for r in bl); s = min(r for r in bl if ex(r, t) == m)
        n, e = view(s, p); w = (n % 8) + (8 * M + 1) * e
        J = floor((w + 1) / 8)                                # w in (8J-1, 8J+1)
        assert 8 * J - 1 < w < 8 * J + 1
        path.append((n % 8, J))
        p, M, t = s, floor(s * m), m
        assert t == Fr(8 * M + 1, 8) / s
        if len(path) > 400: raise RuntimeError('long')
def landing_type(rs, p, M):
    lets = []; used = False
    for f in rs:
        if f == p and not used: used = True; continue
        n, e = view(f, p); w = (n % 8) + (8 * M + 1) * e
        j = floor((w - 1) / 8)
        assert 8 * j + 1 <= w <= 8 * j + 7, (f, p, M, w)
        lets.append((n % 8, j))
    return tuple(sorted(lets))
st = {}
def case(pop, rs):
    rs = sorted(rs)
    T, p, M, path = cascade(rs)
    lt = landing_type(rs, p, M)
    s = st.setdefault(pop, dict(n=0, LT=Counter(), PT=Counter(), maxj=0, maxJ=0, maxM=0, moves=Counter(), M0=0))
    s['n'] += 1; s['LT'][lt] += 1; s['PT'][tuple(path)] += 1
    s['maxj'] = max([s['maxj']] + [abs(j) for _, j in lt]); s['maxJ'] = max([s['maxJ']] + [abs(J) for _, J in path])
    s['maxM'] = max(s['maxM'], M); s['moves'][len(path)] += 1; s['M0'] += (M == 0)
def readings(v, k): return [abs(v[i] - v[k]) for i in range(len(v)) if i != k]
pops = sys.argv[1:] or ['Z16', 'Q', 'W40', 'W80', 'W160']
if 'Z16' in pops:
    for v in itertools.combinations(range(1, 17), 8):
        for k in range(8): case('Z16', [Fr(x) for x in readings(v, k)])
if 'Q' in pops:
    rng = random.Random(1)
    for _ in range(3000):
        gaps = [Fr(rng.randint(6, 24), 12) for _ in range(7)]
        v = [Fr(1)]
        for g in gaps: v.append(v[-1] + g)
        for k in range(8): case('Q', readings(v, k))
for H, seed in ((40, 6), (80, 7), (160, 8)):
    if 'W%d' % H not in pops: continue
    rng = random.Random(seed); seen = 0
    while seen < 2900:
        others = sorted(set(Fr(rng.randint(13, 12 * H), 12) for _ in range(6)))
        if len(others) < 6: continue
        seen += 1; case('W%d' % H, [Fr(1)] + others)
allLT = Counter(); allPT = Counter()
for pop, s in st.items():
    print(pop, 'cases', s['n'], '| landing types', len(s['LT']), '| path types', len(s['PT']),
          '| max |j|', s['maxj'], '| max |J|', s['maxJ'], '| max M*', s['maxM'], '| M*=0', s['M0'],
          '| moves', dict(sorted(s['moves'].items())))
    for t in s['LT']: allLT[t] += 1
    for t in s['PT']: allPT[t] += 1
names = list(st)
for a, b in itertools.combinations(names, 2):
    A, B = set(st[a]['LT']), set(st[b]['LT'])
    print('landing types', a, b, 'shared', len(A & B), '| only', a, len(A - B), '| only', b, len(B - A))
    A, B = set(st[a]['PT']), set(st[b]['PT'])
    print('path types   ', a, b, 'shared', len(A & B), '| only', a, len(A - B), '| only', b, len(B - A))
for pop, s in st.items():
    print(pop, 'commonest landing types:')
    for t, c in s['LT'].most_common(5): print('   ', c, t)
    print(pop, 'commonest path types:')
    for t, c in s['PT'].most_common(8): print('   ', c, t)
