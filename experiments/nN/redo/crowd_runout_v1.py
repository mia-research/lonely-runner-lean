"""E127: what happens when a crowd runs out, read through the cascade.  For two readings s < s' the union of their open
windows ((8k-1)/x, (8k+1)/x) over R covers some stretches solidly: a 'dead zone' of the pair is a maximal covered stretch
longer than either runner's own window.  At the cascade's landing R*: is R* the far end of a pair's dead zone (the pair's
joined windows end exactly at R*)?  Which pairs, at which laps.  Exact."""
import itertools, random
from fractions import Fraction as F
from math import floor
from collections import Counter
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def cascade(T):
    t = F(1, 8 * T[0])
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return 8 * T[0] * t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
def windows(x, hi):
    return [(F(8 * k - 1) / x, F(8 * k + 1) / x) for k in range(1, int(hi * x / 8) + 2)]
def dead_zone_ending_at(x, y, R):
    """the maximal stretch covered by the union of x's and y's windows that ends exactly at R (open windows: R itself is
    the right end of a window); returns its left end, or None."""
    W = sorted(windows(x, R + 1) + windows(y, R + 1))
    if not any(b == R for a, b in W): return None
    lo, hi = None, None; best = None
    for a, b in W:
        if hi is None or a >= hi: lo, hi = a, b
        else: hi = max(hi, b)
        if hi == R: best = lo
    return best
def study(s, R):
    """s: readings / d_min (s[0] = 1).  The pair (i, j) whose joint dead zone ends at R and is longest."""
    out = None
    for i, j in itertools.combinations(range(7), 2):
        lo = dead_zone_ending_at(s[i], s[j], R)
        if lo is None: continue
        L = R - lo
        single = max(F(2) / s[i], F(2) / s[j])
        if L > single and (out is None or L > out[0]): out = (L, i, j, lo)
    return out
def shapes_band_late():
    D1 = 27720; rnd = random.Random(21); out = []
    for sd in [(1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378), (1, 2.5302, 3.2218, 4.1563, 4.531, 5.6544, 7.0302)]:
        T = [int(round(x * D1)) for x in sd]
        for step in range(1200):
            L = list(T); i = rnd.randrange(1, 7); L[i] += rnd.randrange(-500, 501)
            U = sorted(set(L))
            if len(U) < 7 or U[0] != D1 or not (7 * D1 < U[-1] < 9 * D1): continue
            R = cascade(tuple(U))
            if R > 7:
                T = U
                if step % 12 == 0: out.append(([F(d, D1) for d in U], R))
    return out
res = Counter(); pairs = Counter()
for s, R in shapes_band_late():
    o = study(s, R)
    res['late band: landing ends a pair dead zone' if o else 'late band: no pair dead zone ends at R*'] += 1
    if o: pairs[('late', o[1], o[2])] += 1
for T in itertools.combinations(range(1, 25), 7):
    if not (7 * T[0] < T[-1] <= 24 * T[0]): continue
    s = [F(d, T[0]) for d in T]; R = cascade(T)
    if R <= 1: continue
    o = study(s, R)
    res['Case B to 24: landing ends a pair dead zone' if o else 'Case B to 24: no pair dead zone ends at R*'] += 1
for k, v in sorted(res.items()): print("  %7d  %s" % (v, k))
print("  late band: which pair (ranks) ends the dead zone:", pairs.most_common(8))
