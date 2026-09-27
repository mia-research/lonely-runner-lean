"""E121: independent check and trace of the band's late cascades.  Independent check: the earliest lonely instant is an
opening (N + 1/8)/d of some reading; scan every opening with R = 8 d1 t <= 16 in increasing order.  Exact."""
from fractions import Fraction as F
from math import floor
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def lonely(T, t): return all(nd(d * t) >= E8 for d in T)
def first_by_scan(T, Rmax=16):
    c = sorted({F(8 * N + 1, 8 * d) for d in T for N in range(0, Rmax * d // T[0] + 2) if F(8 * N + 1, 8 * d) * 8 * T[0] <= Rmax})
    return next((8 * T[0] * t for t in c if lonely(T, t)), None)
def trace(T):
    t = F(1, 8 * T[0]); out = []
    while True:
        R = 8 * T[0] * t
        way = [(round(float(F(d, T[0])), 4), round(d * t)) for d in T if nd(d * t) < E8]
        out.append((float(R), way))
        if not way: return out
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in T if nd(d * t) < E8)
for T in [(2520, 5819, 7995, 10551, 13161, 14581, 18745), (2520, 6376, 8119, 10474, 11418, 14249, 17716),
          (2520, 7938, 10609, 11905, 13167, 14590, 18756)]:
    R1 = first_by_scan(T); tr = trace(T)
    print(T, " scan R* = %s (%.4f); cascade R* = %.4f; moves %d" % (R1, float(R1), tr[-1][0], len(tr) - 1))
    print("   positions at R = 1 (AP reference 1..7):", [round(float(F(d, T[0])), 4) for d in T])
    for R, w in tr: print("     R = %.4f  blockers (reading/d1, lap): %s" % (R, w))
