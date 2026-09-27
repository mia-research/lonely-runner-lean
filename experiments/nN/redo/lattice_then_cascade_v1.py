"""From the first live lattice's instants, run the cascade's move: how many moves to a lonely instant, minimised over the
L0 numerators j.  Exceptions of lattice_vs_cascade_v1 only (L0 does not clear).  Exact."""
from fractions import Fraction as F
from math import floor
from collections import Counter
from lattice_exceptions_v1 import rows
from lattice_vs_cascade_v1 import nd, E8
def moves_from(T, t, cap=60):
    for n in range(cap):
        way = [d for d in T if nd(d * t) < E8]
        if not way: return n, t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
    return None, t
h = Counter(); worst = []
for (k, T, L0, Ds, e, K) in rows:
    best = min(moves_from(T, F(8 * j + 1, 8 * L0))[0] for j in range(L0))
    h[best] += 1
    if best >= 3: worst.append((best, T, L0))
print("fewest cascade moves from an L0 instant to a lonely instant:", sorted(h.items()))
worst.sort(reverse=True)
for w in worst[:15]: print("  ", w)
