"""E663 v2. v1's limit set K(r) kept every single-point component (two zones touching at T = a). At finite N the other
block's zone edges move earlier by G*Delta/(i b) (reading i), the own block's do not. So a touch point survives iff
min over zones ENDING at a of their shift >= max over zones STARTING at a of their shift (shift 0 for own readings): the
pair-law dichotomy (E627 pair_law_general). Delta_lim uses K'(r) = K(r) without the dying points (a point at
T = tau0 itself, Delta = 0, is exact and kept). Same checks as v1. Exact Fractions."""
import math
from fractions import Fraction as F
E = F(1, 8)
src = open('two_block_e558_v1.py').read().split('for p, b in')[0]
ns = {}; exec(compile(src, 'm', 'exec'), ns); shift = ns['shift']
def zones(p, b, r, T0, T1):
    Z = []
    for j in range(1, p):
        for m in range(math.floor(j * T0) - 1, math.floor(j * T1) + 2):
            Z.append(((m - E) / j, (m + E) / j, F(0)))
    for i in range(1, 8 - p):
        a = i * b
        for m in range(math.floor(E + a * (r + T0)) - 1, math.floor(E + a * (r + T1)) + 2):
            Z.append(((m - 2 * E) / a - r, m / a - r, 1 / a))     # shift weight 1/(i b) (times G*Delta)
    return Z
def Kprime(p, b, r, T0, T1, keep_point=None):
    Z = zones(p, b, r, T0, T1); Zs = sorted(Z)
    comps = []; cur = T0
    for lo, hi, w in Zs:
        if hi <= T0: continue
        if lo >= cur and lo <= T1: comps.append((cur, min(lo, T1)))
        cur = max(cur, hi)
        if cur > T1: break
    if cur <= T1: comps.append((cur, T1))
    out = []
    for a, c in comps:
        if a == c and a != keep_point:
            ending = [w for lo, hi, w in Z if hi == a]; starting = [w for lo, hi, w in Z if lo == a]
            if ending and starting and min(ending) < max(starting): continue   # dies
        out.append((a, c))
    return out
def dlim(p, b, r, tau0):
    for a, c in Kprime(p, b, r, F(0), F(8), keep_point=tau0):
        if tau0 <= c: return F(0) if tau0 >= a else a - tau0
fams = [(2, F(3, 2)), (4, F(3, 2)), (4, F(5, 3)), (6, F(2, 3)), (3, F(7, 4)), (5, F(4, 3))]
for p, b in fams:
    Q = b.denominator; worst = F(0); offbad = 0; offn = 0; ncell = 0
    for r in range(Q):
        ncell += 2 * sum(1 for a, c in Kprime(p, b, r, F(0), F(8)) if a < 1)
        for j in range(48):
            tau0 = F(j, 48); N = 100000 * Q + r; G = 1 / (8 * (N + tau0)); d, _ = shift(p, b, N, tau0, False)
            worst = max(worst, abs(d - dlim(p, b, r, tau0)) / G)
        for tau0 in [F(1, 97), F(13, 101), F(29, 103), F(1, 2) + F(1, 1009), F(61, 89), F(5, 7) + F(1, 997), F(96, 97)]:
            for N in (480 * Q + r, 4000 * Q + r):
                G = 1 / (8 * (N + tau0)); d, _ = shift(p, b, N, tau0, N < 1000 * Q); offn += 1
                if abs(d - dlim(p, b, r, tau0)) > 4 * G: offbad += 1
    print("p=%d b=%s: cells meeting [0,1) (all r): %d | grid: max |Delta - Delta_lim|/G = %s | off-grid beyond 4G: %d of %d" % (p, b, ncell, worst, offbad, offn))
