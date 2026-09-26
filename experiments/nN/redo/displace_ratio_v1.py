"""(1) Which runners repeat in the relay and at which laps; (2) the owner's conjecture that some scale or ratio dictates
how far the isolation is pushed, as d_min sets the bound.  Exhaustive: every set of 7 distinct whole-number readings in
1..24 whose bound is not lonely (145,368 relays).  For each relay: R_final = 8 d_min t* (how far pushed), and candidate
ratios -- S = d_max/d_min, d_2/d_min, g_min/d_min (smallest neighbour gap), b/d_min and its lap k (b the collider whose
exit is the first move), d_min/g (g = gcd).  Envelope: the largest R_final for each value of a candidate (rounded).
For the relays with a repeated setter: the repeater's rank, its rho = d/d_min, and its lap at each setting.  Exact."""
import itertools
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
from collections import Counter, defaultdict
from multiprocessing import Pool
from arrangement_lib import nd

E8 = F(1, 8)

def relay(T):
    t = F(1, 8 * T[0]); setters = []; first_b = None
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return setters, t, first_b
        ex = {d: (F(floor(d * t - E8) + 1) + E8) / d for d in way}
        s = max(ex, key=lambda x: ex[x])
        if first_b is None: first_b = s
        setters.append((s, floor(s * ex[s]))); t = ex[s]

def chunk(first):
    env = defaultdict(lambda: defaultdict(F)); rep_rank = Counter(); rep_rho = Counter(); rep_laps = Counter()
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest; m = T[0]
        setters, t, b = relay(T)
        if not setters: continue
        R = 8 * m * t
        gaps = [T[j] - T[j - 1] for j in range(1, 7)]
        g = reduce(gcd, T)
        cand = {'S': round(T[-1] / m, 1), 'd2/dmin': round(T[1] / m, 1), 'gmin/dmin': round(min(gaps) / m, 2),
                'b/dmin': round(b / m, 1), 'k of b': floor(b / (8 * m) + F(1, 2)), 'dmin/g': m // g}
        for name, v in cand.items():
            if R > env[name][v]: env[name][v] = R
        seen = Counter(s for s, _ in setters)
        for s, cnt in seen.items():
            if cnt > 1:
                rep_rank[T.index(s)] += 1; rep_rho[round(s / m)] += 1
                rep_laps[tuple(M for x, M in setters if x == s)[:4]] += 1
    return {k: dict(v) for k, v in env.items()}, rep_rank, rep_rho, rep_laps

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 19))
    env = defaultdict(dict); rr = Counter(); rho = Counter(); laps = Counter()
    for e, a, b, c in parts:
        for k, d in e.items():
            for v, R in d.items(): env[k][v] = max(env[k].get(v, F(0)), R)
        rr.update(a); rho.update(b); laps.update(c)
    for name in ['S', 'd2/dmin', 'gmin/dmin', 'b/dmin', 'k of b', 'dmin/g']:
        items = sorted(env[name].items())
        print(f"{name}: largest R by value (first 24 values): {[(v, round(float(R), 3)) for v, R in items[:24]]}")
    print(f"repeaters by rank (0 = nearest): {sorted(rr.items())}")
    print(f"repeaters by rho = d/d_min (rounded): {sorted(rho.items())[:20]}")
    print(f"laps at which a repeater sets (first 4), most common: {laps.most_common(15)}")
