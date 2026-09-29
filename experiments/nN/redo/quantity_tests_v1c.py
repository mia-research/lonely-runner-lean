"""E170 follow-up (c): same-pair returns within a chain -- elapsed time vs the exact-replay period 1/gcd(a,b), and the
lap advances (r, s) with drift 8(s - r b/a) (HandoffDriftN).  Exact; same cascade as quantity_tests_v1."""
import itertools, math, sys
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from quantity_tests_v1 import cascade, next_opening, E8

def handoffs(S):
    states, ended = cascade(S)
    rank = {d: i for i, d in enumerate(sorted(S))}
    hs = []  # (time of hand-off t_{j+1}, a = setter at j, K, b = setter at j+1, L)
    N = len(states) - 1
    for j in range(N - 1):
        t, B, st = states[j]; tn, Bn, stn = states[j + 1]
        a = min(st, key=lambda d: rank[d]); b = min(stn, key=lambda d: rank[d])
        K = math.ceil(a * t - E8); L = math.floor(b * tn + F(1, 2))
        hs.append((tn, a, K, b, L))
    return hs

def one(S):
    hs = handoffs(S); c = Counter(); ex = None
    seen = {}
    for (t, a, K, b, L) in hs:
        if (a, b) in seen:
            t0, K0, L0 = seen[(a, b)]
            g = math.gcd(a, b); r, s = K - K0, L - L0
            drift = 8 * (s - r * F(b, a))
            c['returns'] += 1
            c['elapsed < 1/gcd'] += (t - t0 < F(1, g))
            c['drift nonzero'] += (drift != 0)
            c['lap advance is a multiple of (a/g, b/g)'] += (r * b == s * a)
            if t - t0 >= F(1, g) and ex is None: ex = (S, a, b, str(t - t0), str(F(1, g)))
        seen[(a, b)] = (t, K, L)
    return c, ex

def work(sets):
    tot = Counter(); exs = []
    for S in sets:
        c, ex = one(S); tot.update(c)
        if ex and len(exs) < 3: exs.append(ex)
    return tot, exs

if __name__ == '__main__':
    sys.path.insert(0, '../band_cert_v1')
    from coverB_fine_v1 import late_shapes
    pops = {'Case B to 24': [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1]],
            'late band shapes': late_shapes()}
    with Pool(8) as pool:
        for name, sets in pops.items():
            tot = Counter(); exs = []
            for c, ex in pool.map(work, [sets[i::32] for i in range(32)]):
                tot.update(c); exs += ex
            print(name, dict(tot), 'first with elapsed >= 1/gcd:', exs[:3])
