"""Move r8 from the AP (1..8) out past its band.  For each runner: its own d_min, and the least lattice L
(instants u = d_min*t = p/(8L), p odd, every lap in one period) at which it is lonely.  L = 1 is its own AP."""
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
E = F(1, 8)
def fr(x): return x - floor(x)
def dist(x): x = fr(x); return min(x, 1 - x)
def least_L(V, i, Lmax=12):
    ds = [abs(V[j] - V[i]) for j in range(8) if j != i]; m = min(ds)
    den = reduce(lambda a, b: a * b // gcd(a, b), [d.denominator for d in ds])
    g = F(reduce(gcd, [int(d * den) for d in ds]), den)
    laps = int(m / g) + 1                                  # one period of the reading in u
    for L in range(1, Lmax + 1):
        for p in range(1, 8 * L * laps, 2):
            if all(dist(d * F(p, 8 * L) / m) >= E for d in ds):
                return L, m, F(p, 8 * L)
    return None, m, None
speeds = [F(8)] + [F(x, 100) for x in (850, 890, 895, 899, 900, 901, 905, 910, 950)] + [F(x, 2) for x in range(20, 34)]
print("r8 speed | per runner: least lattice L (own AP = 1) @ u     [d_min]")
for s in speeds:
    V = [F(j + 1) for j in range(7)] + [s]
    cells = []
    for i in range(8):
        L, m, u = least_L(V, i)
        cells.append(f"{L}@{u}" + ("" if m == 1 else f"[{m}]"))
    print(f"{float(s):>7.2f}  | " + "  ".join(f"r{i+1}:{c:<14}" for i, c in enumerate(cells)))
