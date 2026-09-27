"""E127: landings against crowd run-outs.  Adjacent readings s_i < s_{i+1}, ratio rho: common clear blocks exist on laps
k <= K(rho) = floor((7 - rho)/(8(rho - 1))); the pair's run-out point is the end of its last common block,
R_out = (8K + 7)/s_{i+1} (units: R = 8 d_min t, readings / d_min).  For each set: the cascade landing R*, the first
run-out R_out,min over adjacent pairs (the first crowd to run out), and where R* sits.  Exhaustive Case B to 24 and the
late band shapes.  Exact."""
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
def runouts(s):
    out = []
    for i in range(6):
        rho = s[i + 1] / s[i]
        if rho >= 7: continue
        K = floor((7 - rho) / (8 * (rho - 1)))
        out.append(((8 * K + 7) / s[i + 1], i, K))
    return sorted(out)
def classify(s, R):
    ro = runouts(s)
    if not ro: return 'no adjacent pair within ratio 7'
    first = ro[0]
    if R <= first[0]: return 'landing before the first crowd runs out'
    # after: is R in the next common block of the first pair beyond its dead zone, or elsewhere
    return 'landing after the first run-out'
c = Counter()
for T in itertools.combinations(range(1, 25), 7):
    if not (7 * T[0] < T[-1] <= 24 * T[0]): continue
    s = [F(d, T[0]) for d in T]; R = cascade(T)
    c[('Case B to 24', classify(s, R))] += 1
D1 = 27720; rnd = random.Random(21)
for sd in [(1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378), (1, 2.5302, 3.2218, 4.1563, 4.531, 5.6544, 7.0302)]:
    T = [int(round(x * D1)) for x in sd]
    for step in range(1200):
        L = list(T); i = rnd.randrange(1, 7); L[i] += rnd.randrange(-500, 501)
        U = sorted(set(L))
        if len(U) < 7 or U[0] != D1 or not (7 * D1 < U[-1] < 9 * D1): continue
        R = cascade(tuple(U))
        if R > 7:
            T = U
            if step % 12 == 0: c[('late band', classify([F(d, D1) for d in U], R))] += 1
for k, v in sorted(c.items()): print("  %7d  %s" % (v, k))
