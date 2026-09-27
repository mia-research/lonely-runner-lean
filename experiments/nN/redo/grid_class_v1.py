"""E128: the owner's reference, literally: at the AP scale R = 1 each reading is a grid position plus a deviation,
s_i = n_i + delta_i (n_i an integer near s_i; repeats allowed = doubled slots; n = 8 = a multiple of 8 captured by the grid).
Candidate: class c (odd, 1..15): reading i on lap floor(c n_i / 8), and a reading with c n_i = 0 mod 8 on the lap just
before or after.  Compatibility is exact and pairwise (lonely_eight_of_pairwise_laps) -- this allows the relocation.
Grid choices tried: n_i = floor or ceil of s_i (each reading independently: 2^6 grids, s_0 = 1 fixed).  Exact."""
import itertools, random, sys
from fractions import Fraction as F
from math import floor, ceil
from collections import Counter
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
def compat(s, k):
    return all((8 * k[i] + 1) * s[j] <= (8 * k[j] + 7) * s[i] for i in range(7) for j in range(7))
def grid_class(s):
    options = [[1]] + [sorted({floor(x), ceil(x)}) for x in s[1:]]
    for n in itertools.product(*options):
        for c in range(1, 16, 2):
            base = [(c * m) // 8 for m in n]
            amb = [i for i, m in enumerate(n) if (c * m) % 8 == 0]
            for adj in itertools.product(*[(-1, 0) if i in amb else (0,) for i in range(7)]):
                k = [b + a for b, a in zip(base, adj)]
                if min(k) < 0: continue
                if compat(s, k): return c
    return None
c = Counter()
for T in itertools.combinations(range(1, 33), 7):
    if not (7 * T[0] < T[-1] < 9 * T[0]): continue
    r = grid_class([F(d, T[0]) for d in T]); c[('band to 32', r is not None)] += 1
D1 = 27720; rnd = random.Random(41)
for sd in [(1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378), (1, 2.5302, 3.2218, 4.1563, 4.531, 5.6544, 7.0302)]:
    T = [int(round(x * D1)) for x in sd]
    for step in range(1500):
        L = list(T); i = rnd.randrange(1, 7); L[i] += rnd.randrange(-500, 501)
        U = sorted(set(L))
        if len(U) < 7 or U[0] != D1 or not (7 * D1 < U[-1] < 9 * D1): continue
        s = [F(d, D1) for d in U]
        if clear_set(s, F(1), F(7)): continue
        T = U
        if step % 10 == 0: c[('late band', grid_class(s) is not None)] += 1
for k, v in sorted(c.items()): print("   %7d  %s covered by a grid class: %s" % (v, k[0], k[1]))
