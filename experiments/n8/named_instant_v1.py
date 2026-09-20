"""The named instant: runner i lonely, flanked on the TRACK by its two SPEED-neighbours
-- next slowest behind, next quicker ahead.  Adjacency mod 8, so r1's neighbours are
r8 and r2 (SKETCH section 2: the speed line has no ends).

Not the first isolation.  One that occurs, with its specific time.

BSM: exact rationals, closed >= comparisons, candidates are the boundary set (openings
of the differences) plus nothing else.  Nobody is pinned.  No density anywhere.
"""
from fractions import Fraction as F
from math import gcd
from functools import reduce

def frac(x):
    r = x - int(x); return r + 1 if r < 0 else r
def nrm(x):
    f = frac(x); return min(f, 1-f)

def named(V, i, tmax=None):
    N = len(V)
    L, R = (i-1) % N, (i+1) % N           # speed-neighbours, mod 8
    ds = [abs(V[i]-V[j]) for j in range(N) if j != i]
    m = min(ds)
    if tmax is None: tmax = F(1)          # integer speeds: one period
    B = {F(0)}
    for d in ds:
        k = 0
        while F(8*k+1, 8*d) <= tmax:
            B.add(F(8*k+1, 8*d)); k += 1
    for t in sorted(B):
        if t == 0: continue
        if not all(nrm(F(V[i]-V[j])*t) >= F(1,8) for j in range(N) if j != i): continue
        P = [frac(F(v)*t) for v in V]
        o = sorted(range(N), key=lambda j: P[j]); z = o.index(i)
        if o[z-1] == L and o[(z+1) % N] == R:
            return t, P
    return None, None

def g_of(V): return reduce(gcd, [abs(V[i]-V[j]) for i in range(8) for j in range(i+1,8)])

for V, tag in (([1,2,3,4,5,6,7,8], 'the AP'),
               ([3,6,9,12,15,18,21,24], 'dilated AP k=3'),
               ([1,2,3,4,5,6,15,16], 'block grid'),
               ([1,2,3,4,5,6,7,16], 'grid, r8 has d_min > g'),
               ([10,65,101,126,159,222,256,271], 'section 7b example'),
               ([12,14,96,111,128,160,161,163], 'Case B')):
    g = g_of(V)
    print('%-28s g=%-3d  1/(8g)=%s' % (tag, g, F(1,8*g)))
    ts = []
    for i in range(8):
        t, P = named(V, i)
        ts.append(t)
        print('   r%d speed %-6d  named instant t = %-14s %s'
              % (i+1, V[i], t if t is not None else 'none found',
                 '= 1/(8g)' if t == F(1,8*g) else ''))
    good = [t for t in ts if t is not None]
    if len(good) == 8:
        print('   all eight named.  earliest %s  latest %s  ratio %.1fx'
              % (min(good), max(good), float(max(good)/min(good))))
    else:
        print('   %d of 8 named' % len(good))
    print()
