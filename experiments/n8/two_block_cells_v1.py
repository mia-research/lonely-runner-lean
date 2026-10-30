"""E663. Exact cells at the gap edge of the two-block template (derivation in the log entry). Limit set
K(r) = {T : j T clear (1 <= j < p) and 1/8 + i b (r + T) clear (1 <= i < 8-p)}, clear = distance >= 1/8 from Z.
Limit landing displacement: Delta_lim(tau0, r) = 0 if tau0 in K(r), else (next left end of K(r) after tau0) - tau0.
Built exactly from zone edges. Checks against the unchanged cascade (two_block_e558_v1.shift): (a) every 1/48-grid
cell of E662 at N = 100000Q + r: |Delta - Delta_lim| against the bound 4G (reported exactly as the max ratio
|Delta - Delta_lim| / G); (b) 7 off-grid tau0 per (family, r), N = 480Q + r and 4000Q + r, oracle C1 on. Cells reported:
the components of K(r) meeting [0,1) and the gaps between them. Exact Fractions."""
import math, importlib.util
from fractions import Fraction as F
src = open('two_block_e558_v1.py').read().split('for p, b in')[0]
ns = {}; exec(compile(src, 'm', 'exec'), ns); shift = ns['shift']; dist = ns['dist']
E = F(1, 8)
def K(p, b, r, T0, T1):
    # zones (open) of each limit reading, as T-intervals, on [T0, T1]
    zones = []
    for j in range(1, p):                      # phase j T
        for m in range(math.floor(j * T0) - 1, math.floor(j * T1) + 2):
            zones.append(((m - E) / j, (m + E) / j))
    for i in range(1, 8 - p):                  # phase 1/8 + i b (r + T)
        a = i * b
        for m in range(math.floor(E + a * (r + T0)) - 1, math.floor(E + a * (r + T1)) + 2):
            zones.append(((m - E - E) / a - r, (m + E - E) / a - r))
    zones.sort(); comps = []; cur = T0
    for lo, hi in zones:
        if hi <= T0: continue
        if lo >= cur:
            if lo <= T1: comps.append((cur, min(lo, T1)))
        cur = max(cur, hi)
        if cur > T1: break
    if cur <= T1: comps.append((cur, T1))
    return comps                               # closed components [a, b] (a = b allowed)
def dlim(comps, tau0):
    for a, b_ in comps:
        if tau0 <= b_:
            return F(0) if tau0 >= a else a - tau0
    raise RuntimeError('extend window')
fams = [(2, F(3, 2)), (4, F(3, 2)), (4, F(5, 3)), (6, F(2, 3)), (3, F(7, 4)), (5, F(4, 3))]
for p, b in fams:
    Q = b.denominator; worst = F(0); badB = 0; ncell = 0; offbad = 0; offn = 0
    for r in range(Q):
        comps = K(p, b, r, F(0), F(8))
        ncell += 2 * sum(1 for a, b_ in comps if a < 1) 
        for j in range(48):
            tau0 = F(j, 48); N = 100000 * Q + r; G = 1 / (8 * (N + tau0))
            d, _ = shift(p, b, N, tau0, False)
            ratio = abs(d - dlim(comps, tau0)) / G
            worst = max(worst, ratio)
        for tau0 in [F(1, 97), F(13, 101), F(29, 103), F(1, 2) + F(1, 1009), F(61, 89), F(5, 7) + F(1, 997), F(96, 97)]:
            for N in (480 * Q + r, 4000 * Q + r):
                G = 1 / (8 * (N + tau0)); d, _ = shift(p, b, N, tau0, N < 1000 * Q); offn += 1
                if abs(d - dlim(comps, tau0)) > 4 * G: offbad += 1
    print("p=%d b=%s: cells meeting [0,1) (components and gaps, all r): %d | grid: max |Delta - Delta_lim|/G = %s | off-grid checks beyond 4G: %d of %d" %
          (p, b, ncell, worst, offbad, offn))
p, b = 4, F(3, 2)
print("example K(r) components in [0, 2) for p=4, b=3/2:")
for r in range(2): print("  r=%d:" % r, [(str(a), str(c)) for a, c in K(p, b, r, F(0), F(2))])
