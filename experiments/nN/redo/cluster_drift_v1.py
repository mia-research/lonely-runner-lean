"""E118: can a near-lattice fast cluster push the isolation out of the slow runner's first window?
Cluster = c*(1..6) with one member moved by delta (grid + deviation); slow runner d0 with 6c > 24 d0.  Exact cascade."""
from fractions import Fraction as F
from math import floor
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def cascade(T):
    t = F(1, 8 * min(T)); n = 0
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return t, n
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way); n += 1
worst = []
for c in (40, 120, 400):
    for j in range(6):
        for delta in (1, 2, 3, -1, -2):
            clus = [c * (i + 1) + (delta if i == j else 0) for i in range(6)]
            for d0 in range(1, c // 4):
                T = sorted(set([d0] + clus))
                if len(T) < 7 or T[-1] <= 24 * T[0]: continue
                t, n = cascade(T); R = 8 * d0 * t
                worst.append((float(R), T, n))
worst.sort(reverse=True)
print("sets:", len(worst), " R* > 7:", sum(1 for w in worst if w[0] > 7), " largest R*:")
for w in worst[:8]: print("   R* = %.3f  moves %d  %s" % (w[0], w[2], w[1]))
