"""E130: the band sets needing the finer grid (m = 2, classes c <= 7): their working references (j, m, c), the landing R*,
and a perturbation of each through the cascade: one reading moved by +-1/d1-steps until m = 1 works again -- which reading,
and how the landing moves."""
import itertools
from fractions import Fraction as F
from math import floor, ceil
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
def compat(s, k):
    return all((8 * k[i] + 1) * s[j] <= (8 * k[j] + 7) * s[i] for i in range(7) for j in range(7))
def refs(s, M, cmax=7):
    out = []
    for m in range(1, M + 1):
        for j in range(7):
            lam = s[j] / m; options = [sorted({floor(x / lam), ceil(x / lam)}) for x in s]
            for c in range(1, cmax + 1, 2):
                R = c / lam
                if R < 1 or 7 < R < 9 or R > 15: continue
                for n in itertools.product(*options):
                    if min(n) < 1: continue
                    base = [(c * q) // 8 for q in n]; amb = [i for i, q in enumerate(n) if (c * q) % 8 == 0]
                    for adj in itertools.product(*[(-1, 0) if i in amb else (0,) for i in range(7)]):
                        k = [b + a for b, a in zip(base, adj)]
                        if min(k) >= 0 and compat(s, k): out.append((j, m, c, tuple(n))); break
    return out
ex = []
for T in itertools.combinations(range(1, 25), 7):
    if not (7 * T[0] < T[-1] <= 9 * T[0]): continue
    s = [F(d, T[0]) for d in T]
    if not refs(s, 1): ex.append(T)
print("band sets to 24 needing m = 2:", len(ex))
for T in ex[:10]:
    s = [F(d, T[0]) for d in T]; r = refs(s, 2)
    print("  ", T, "readings/d1", [round(float(v), 3) for v in s], " R* = %.3f" % float(cascade(T)), " refs(m=2):", r[:2])
# perturb: move each reading by +-1 (integer step), see if m = 1 returns and how the landing moves
moves = Counter()
for T in ex:
    for i in range(1, 7):
        for dv in (-1, 1):
            U = list(T); U[i] += dv
            if len(set(U)) < 7 or sorted(U) != U or not (7 * U[0] < U[-1] <= 9 * U[0]): continue
            if refs([F(d, U[0]) for d in U], 1): moves[('reading rank %d' % i)] += 1
print("single +-1 moves that restore m = 1, by the reading moved:", sorted(moves.items()))
