"""E121: anatomy of the band's supremum shape.  The full lonely set in R in [1, 16] (exact intervals), for the best
shape and for small perturbations of each reading; which pairs are tight at the landing."""
from fractions import Fraction as F
from math import floor, ceil
E8 = F(1, 8)
def lonely_intervals(s, Rmax=16):
    """R-set where every s_i R mod 8 in [1,7], as exact intervals; s = readings / d1 (Fractions)."""
    pts = {F(1), F(Rmax)}
    for x in s:
        for k in range(0, int(Rmax * x / 8) + 2):
            for e in (8 * k + 1, 8 * k + 7, 8 * k - 1):
                r = F(e) / x
                if 1 <= r <= Rmax: pts.add(r)
    pts = sorted(pts); out = []
    def ok(R): return all(1 <= (x * R) % 8 <= 7 for x in s)
    for a, b in zip(pts, pts[1:]):
        m = (a + b) / 2
        if ok(m): out.append([a, b])
        elif ok(a): out.append([a, a])
    merged = []
    for iv in out:
        if merged and merged[-1][1] >= iv[0]: merged[-1][1] = max(merged[-1][1], iv[1])
        else: merged.append(list(iv))
    return merged
D1 = 27720
best = (1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378)
s = [F(int(round(x * D1)), D1) for x in best]
L = lonely_intervals(s)
print("sup shape", best, "\n lonely set in [1,16]:", [(round(float(a), 4), round(float(b), 4)) for a, b in L])
R = L[0][0]
print(" landing R* = %.5f; positions mod 8:" % float(R), [round(float((x * R) % 8), 4) for x in s])
for i in range(1, 7):
    for dlt in (F(-1, 200), F(1, 200)):
        t = list(s); t[i] += dlt
        if sorted(t) != t: continue
        L2 = lonely_intervals(t)
        print("   reading %d %+.3f -> first lonely R %.4f" % (i, float(dlt), float(L2[0][0]) if L2 else -1))
