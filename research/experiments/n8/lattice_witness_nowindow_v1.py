"""The lattice route to Existence, without the first-window restriction. Threshold 1/n; subject's readings s_j = c_j/q
(nearest reading 1). Lattice L: instants u = p/(nL), p = 1, 2, ... (u = d_min·t). Positions s_j·p/(nL) are periodic in p
with period nLq, so one period decides the lattice exactly. Dead lattice: some s_j/(nL) is an integer (that runner sits on
the subject at every lattice instant). Reports, per runner: first live lattice L_live, least lattice with a lonely instant
L_lonely, the gap L_lonely - L_live, and whether L_live <= floor(s_max/n) + 1 (the proved bound). Exact rationals."""
from fractions import Fraction as F
import math, random, sys
from collections import Counter
def cdist(x):
    f = x - math.floor(x); return min(f, 1 - f)
def lattice_lonely(s, n, L, q):
    per = n * L * q
    for p in range(1, per + 1):
        u = F(p, n * L)
        if all(cdist(sj * u) >= F(1, n) for sj in s): return True
    return False
def dead(s, n, L): return any((sj / (n * L)).denominator == 1 for sj in s)
def run(n, trials, seed, qmax):
    rng = random.Random(seed); gaps = Counter(); bound_ok = 0; worst = (0, None); tot = 0
    for _ in range(trials):
        q = rng.randint(1, qmax)
        cs = set()
        while len(cs) < n - 2:
            cs.add(rng.randint(q + 1, q * rng.choice([3, 6, 10, 20])))
        s = [F(1)] + [F(c, q) for c in sorted(cs)]
        if rng.random() < 0.3:          # plant a slot-sharer to make low lattices dead
            s[-1] = F(n * rng.randint(1, 4))
        s = sorted(set(s))
        if len(s) != n - 1: continue
        smax = max(s); tot += 1
        Llive = next(L for L in range(1, 10**6) if not dead(s, n, L))
        if Llive <= math.floor(smax / n) + 1: bound_ok += 1
        L = 1
        while not lattice_lonely(s, n, L, q): L += 1
        g = L - Llive; gaps[g] += 1
        if g > worst[0]: worst = (g, [str(x) for x in s], Llive, L)
    return tot, bound_ok, gaps, worst
if __name__ == '__main__':
    for n, trials, qmax in ((5, 3000, 6), (8, 1500, 4)):
        tot, ok, gaps, worst = run(n, trials, n, qmax)
        print(f'n={n}: {tot} runners; first live lattice within floor(s_max/n)+1: {ok}; gap (lonely - first live): {dict(sorted(gaps.items()))}')
        print(f'   largest gap {worst[0]} at readings {worst[1]} (first live {worst[2]}, lonely at {worst[3]})')
