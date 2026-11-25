"""Wall-window word, test v8 (2026-11-25).  Exact Fractions; the cascade is the oracle.

E931: a multi-move pass of an S window is a word (f_1,k_1),...,(f_n,k_n); each link (f,k) -> (f',k') satisfies
(8k'-1)/(8k+1) < f'/f < (8k'+1)/(8k+1).  The cell is centred near k'/k, so a link says the two setters' readings are in
ratio close to the ratio of their laps.  Owner (2026-11-25): test whether a fixed set of ratio cells, named by lap
fractions, determines the word.
Recorded:
  (1) the link's lap pair (k, k') and its reduced lap ratio k'/k;
  (2) whether k'/k is the closest fraction to f'/f among all p/q with q <= k (a best approximation of f'/f);
  (3) the FRACTION WORD of a pass: the tuple of reduced lap ratios k_{i+1}/k_i, with the first lap k_1; distinct
      fraction words per population, and how many occur in more than one population (scale-free word types);
  (4) the first move: k_1 against the opening's position a*f_1 (k_1 = the nearest integer to a*f_1 by construction).
Positions start at 1 (rule 5).  Populations as E929.
"""
import itertools, random, sys
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter
exec(open('wall_window_chain_v7.py').read().split("def readings(v, k):")[0])

def best_approx(x, k):
    """closest p/q to x with 1 <= q <= k (ties to smallest q)."""
    best = None
    for q in range(1, k + 1):
        for p in (floor(x * q), ceil(x * q)):
            dist = abs(x - Fr(p, q))
            if best is None or dist < best[0]: best = (dist, Fr(p, q))
    return best[1]

c = Counter(); fw = {}; lw = {}
def case(pop, rs, label):
    rs = sorted(rs); d = rs[0]; t0 = E / d
    S = [r for r in rs if r <= 7 * d]; Fs = [r for r in rs if r > 7 * d]
    if not Fs: return
    T, _ = cascade(rs, t0)
    ws = windows(S, t0, T + 1)
    i = next(k for k, (a, b, o) in enumerate(ws) if a <= T <= b)
    for j in range(i):
        a, b, o = ws[j]
        ch, passed, st = f_chain(Fs, a, b)
        if len(ch) < 2: continue
        laps = [k for s, k, *_ in ch]; fs = [s for s, *_ in ch]
        word = (laps[0],) + tuple(Fr(laps[n], laps[n - 1]) for n in range(1, len(ch)))
        fw.setdefault(pop, Counter())[word] += 1
        for n in range(1, len(ch)):
            k0, k1 = laps[n - 1], laps[n]; x = fs[n] / fs[n - 1]
            c[(pop, 'link lap pair', (k0, k1))] += 1
            ba = best_approx(x, k0)
            c[(pop, 'link: k\'/k is best approximation of f\'/f with q <= k', ba == Fr(k1, k0))] += 1
def readings(v, k): return [abs(v[i] - v[k]) for i in range(len(v)) if i != k]
for v in itertools.combinations(range(1, 17), 8):
    for k in range(8): case('Z16', [Fr(x) for x in readings(v, k)], (v, k))
rng = random.Random(1)
for _ in range(3000):
    gaps = [Fr(rng.randint(6, 24), 12) for _ in range(7)]
    v = [Fr(1)]
    for g in gaps: v.append(v[-1] + g)
    for k in range(8): case('Q', readings(v, k), ([str(g) for g in gaps], k))
rng = random.Random(6); seen = 0
while seen < 2900:
    others = sorted(set(Fr(rng.randint(13, 480), 12) for _ in range(6)))
    if len(others) < 6: continue
    seen += 1; case('W40', [Fr(1)] + others, seen)

for k, v in sorted(c.items(), key=lambda x: str(x[0])): print(v, k)
def fmt(w): return '(' + ', '.join(str(x) for x in w) + ')'
allw = Counter()
for p, cw in fw.items():
    print(p, 'distinct fraction words:', len(cw))
    for w, n in cw.most_common(): print('   ', n, fmt(w))
    for w in cw: allw[w] += 1
print('fraction words in more than one population:', sum(1 for w in allw if allw[w] > 1), 'of', len(allw))
for w in allw:
    if allw[w] > 1: print('   shared', fmt(w), {p: fw[p][w] for p in fw if w in fw[p]})
