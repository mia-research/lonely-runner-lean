"""The named instant, with a COMPLETE boundary set.

v1 used only section 8's openings.  That is the right candidate set for the FIRST
isolation, but the flanking condition also changes at COINCIDENCES, which are not
openings -- so v1 reported "none found" for a runner that has 57 such instants.

Complete boundary set over one period: every t at which some pair sits at phase
0, 1/8, 1/2 or 7/8.  Between consecutive points nothing changes: no order change
(phase 0), no threshold crossing (1/8, 7/8), no kink (1/2).  Exact rationals,
closed >= comparisons, nobody pinned, no density.

Named instant for runner i: lonely, and flanked on the track by its two SPEED
neighbours -- r(i-1) behind, r(i+1) ahead, indices mod 8.
"""
from fractions import Fraction as F
from math import gcd
from functools import reduce

def frac(x):
    r = x - int(x); return r + 1 if r < 0 else r
def nrm(x):
    f = frac(x); return min(f, 1-f)

def boundary(V):
    D = sorted({abs(V[a]-V[b]) for a in range(8) for b in range(a+1,8)})
    B = set()
    for d in D:
        for num in (0,1,4,7):
            k = 0
            while F(8*k+num, 8*d) <= 1:
                B.add(F(8*k+num, 8*d)); k += 1
    return sorted(x for x in B if 0 < x <= 1)

def named_all(V):
    B = boundary(V); out = {}
    for t in B:
        P = [frac(F(v)*t) for v in V]
        o = sorted(range(8), key=lambda j: P[j])
        for z, i in enumerate(o):
            if i in out: continue
            if o[z-1] != (i-1) % 8 or o[(z+1) % 8] != (i+1) % 8: continue
            if all(nrm(F(V[i]-V[j])*t) >= F(1,8) for j in range(8) if j != i):
                out[i] = t
    return out

def g_of(V): return reduce(gcd, [abs(V[i]-V[j]) for i in range(8) for j in range(i+1,8)])

for V, tag in (([1,2,3,4,5,6,7,8], 'the AP'),
               ([1,2,3,4,5,6,7,16], 'grid, r8 d_min > g'),
               ([10,65,101,126,159,222,256,271], 'section 7b example'),
               ([12,14,96,111,128,160,161,163], 'Case B'),
               ([27,45,308,678,679,799,806,979], 'section 7c cascade failure')):
    g = g_of(V); out = named_all(V)
    ts = [out.get(i) for i in range(8)]
    print('%-30s g=%-3d  named for %d of 8' % (tag, g, sum(x is not None for x in ts)))
    print('    %s' % '  '.join('r%d:%s' % (i+1, ts[i] if ts[i] is not None else '-') for i in range(8)))
    good = [x for x in ts if x is not None]
    if len(good) == 8:
        print('    earliest %s   latest %s   ratio %.1fx' % (min(good), max(good), float(max(good)/min(good))))
    print()
