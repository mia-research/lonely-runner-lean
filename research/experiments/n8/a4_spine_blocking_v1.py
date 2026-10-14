"""A4. At one scale D, base at the subject: runner j reads s_j = a_j + e_j (slot a_j integer, deviation e_j in [0,1)).
At spine instant u = r/8 (r = 1, 3, 5, 7) it sits at r·a_j + r·e_j eighths, and is in the way iff that is within 1 of a
multiple of 8. With c = r·a mod 8 and r·e in [0, r): in the way iff c + r·e < 1 or 7 < c + r·e < 9 (strict; endpoints clear).
So the in-the-way pattern depends only on (a mod 8, e), at every scale.

(1) For each slot residue a mod 8: the exact partition of e in [0,1) into pieces, and the spines each piece is in the way at.
(2) The largest set of spines one runner can be in the way at, by residue.
(3) Check against direct evaluation from speeds: random arrangements, subject scale D = d_min, all four spine instants,
    table prediction versus circle distance computed from the speeds. Exact rationals."""
from fractions import Fraction as F
import math, random
SPINES = (1, 3, 5, 7)
def in_way(c, r, e):
    v = c + r * e
    return v < 1 or (7 < v < 9)
def pattern(a8, e): return frozenset(r for r in SPINES if in_way((r * a8) % 8, r, e))
def pieces(a8):
    bps = {F(0), F(1)}
    for r in SPINES:
        c = (r * a8) % 8
        for edge in (1, 7, 9):
            x = F(edge - c, r)
            if 0 < x < 1: bps.add(x)
    bps = sorted(bps); out = []
    for lo, hi in zip(bps, bps[1:]):
        out.append(((lo, hi), pattern(a8, (lo + hi) / 2)))
    pts = [(x, pattern(a8, x)) for x in bps[:-1]]   # the breakpoints themselves (e = 0 included)
    return out, pts
def show(ps): return '{' + ','.join(str(r) for r in sorted(ps)) + '}' if ps else '{}'
print('(1) in-the-way spines by slot residue and deviation (open pieces; breakpoints listed separately)')
maxset = {}
for a8 in range(8):
    out, pts = pieces(a8)
    segs = '  '.join(f'({lo},{hi}):{show(p)}' for (lo, hi), p in out)
    ptxt = '  '.join(f'e={x}:{show(p)}' for x, p in pts)
    print(f'  a≡{a8}: {segs}')
    print(f'        at breakpoints: {ptxt}')
    allp = [p for _, p in out] + [p for _, p in pts]
    maxset[a8] = max(allp, key=len)
print('(2) largest spine set one runner is in the way at:', {a8: show(p) for a8, p in maxset.items()})
# (3) validation from speeds
def cdist(x):
    f = x - math.floor(x); return min(f, 1 - f)
rng = random.Random(4); checks = mism = 0
for _ in range(3000):
    v = sorted({F(rng.randint(0, 4000), rng.choice([1, 2, 3, 7, 10, 29])) for _ in range(8)})
    if len(v) < 8: continue
    for i in range(8):
        ds = [abs(x - v[i]) for x in v if x != v[i]]
        D = min(ds)
        for r in SPINES:
            t = F(r, 8) / D
            direct = [cdist(d * t) < F(1, 8) for d in ds]
            pred = []
            for d in ds:
                s = d / D; a = math.floor(s); e = s - a
                pred.append(r in pattern(a % 8, e))
            checks += 1
            if direct != pred: mism += 1
print(f'(3) spine checks from speeds: {checks}; table disagreements: {mism}')
