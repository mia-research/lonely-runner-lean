# How the four AP class instants R = 1, 3, 5, 7 (and the next period's 9) move as the speeds are deformed.
# R = 8*d_min*t; reading rho_x clear on R in [(8j+1)/rho, (8j+7)/rho], j >= 0.  Exact (Fractions, rho rational), R in (0, RMAX].
# Cascade from a = the first lonely R >= a ("fwd"); the mirror cascade = the last lonely R <= a ("bwd").
import sys
from fractions import Fraction as F
RMAX = F(19, 2)
def windows(rho):
    out = []; j = 0
    while F(8 * j + 1) / rho <= RMAX:
        out.append((F(8 * j + 1) / rho, min(F(8 * j + 7) / rho, RMAX))); j += 1
    return out
def inter(A, B):
    out = []; i = k = 0
    while i < len(A) and k < len(B):
        lo = max(A[i][0], B[k][0]); hi = min(A[i][1], B[k][1])
        if lo <= hi: out.append((lo, hi))
        if A[i][1] < B[k][1]: i += 1
        else: k += 1
    return out
def lonely(rhos):
    L = windows(rhos[0])
    for r in rhos[1:]:
        L = inter(L, windows(r))
        if not L: return []
    out = []
    for lo, hi in sorted(L):
        if out and lo <= out[-1][1]: out[-1] = (out[-1][0], max(out[-1][1], hi))
        else: out.append((lo, hi))
    return out
def fwd(L, a):
    for lo, hi in L:
        if hi >= a: return max(lo, a) - a
    return None
def bwd(L, a):
    best = None
    for lo, hi in L:
        if lo <= a: best = a - min(hi, a)
    return best
def fmt(x): return "  --  " if x is None else "%6.3f" % float(x)
def track(name, path, steps=20):
    print("=" * 100); print(name)
    print("   s    rho (rounded)                                   | fwd displacement of R=1,3,5,7,9      | bwd displacement of R=1,3,5,7,9       | components in (0,9.5]")
    for i in range(steps + 1):
        s = F(i, steps); rhos = [F(round(float(r) * 1000), 1000) for r in path(s)]
        L = lonely(rhos)
        print(" %4.2f  %-48s| %s | %s | %d" % (float(s), str([round(float(r), 3) for r in rhos]),
              " ".join(fmt(fwd(L, F(a))) for a in (1, 3, 5, 7, 9)), " ".join(fmt(bwd(L, F(a))) for a in (1, 3, 5, 7, 9)), len(L)))
AP = [F(k) for k in range(1, 8)]
def lin(T): return lambda s: [a + (b - a) * s for a, b in zip(AP, T)]
if __name__ == "__main__":
    track("P1: one mover, rho_7: 7 -> 8.5 (lapped into the subject's slot)", lin([F(k) for k in range(1, 7)] + [F(17, 2)]))
    track("P2: one mover, rho_4: 4 -> 4.6", lin([F(1), F(2), F(3), F(23, 5), F(5), F(6), F(7)]))
    track("P3: AP -> B1 #7 readings [1, 1.093, 4.666, 5.963, 6.348, 6.860, 8.117]", lin([F(1), F(1093, 1000), F(4666, 1000), F(5963, 1000), F(6348, 1000), F(686, 100), F(8117, 1000)]))
