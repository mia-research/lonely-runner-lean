"""E407 (2026-10-06), descent_q_bound_check_v1: exact check, for every q in [3, 40] and every g = gcd(d, q) < q,
that the max over sigma of #{k<q: ||d sigma + d k/q|| < 1/8} is at most g*ceil(q/(4g)).
The count is piecewise constant in x = d*sigma mod 1, with breakpoints where x + j*g/q = +-1/8 (mod 1); every
breakpoint and every midpoint between consecutive breakpoints is tested (exact Fractions).
"""
from fractions import Fraction as F
from math import gcd, floor
def cd(x): x = x - floor(x); return min(x, 1 - x)
bad = 0; tight = 0
for q in range(3, 41):
    for g in sorted({gcd(d, q) for d in range(1, q + 1)}):
        if g == q: continue
        pts = sorted({(s - F(j * g, q)) % 1 for j in range(q // g) for s in (F(1, 8), F(-1, 8))})
        cand = pts + [(pts[i] + pts[(i + 1) % len(pts)] + (1 if i == len(pts) - 1 else 0)) / 2 % 1 for i in range(len(pts))]
        # count for d with gcd(d,q)=g: positions x + (multiples of g/q), each hit g times
        mx = max(g * sum(1 for j in range(q // g) if cd(x + F(j * g, q)) < F(1, 8)) for x in cand)
        bound = g * (-(-q // (4 * g)))
        if mx > bound: bad += 1; print('BAD', q, g, mx, bound)
        if mx == bound: tight += 1
msg = 'violations %d tight %d' % (bad, tight)
print(msg); open('descent_q_bound_check_v1.out', 'w').write(__doc__ + '\n' + msg + '\n')
