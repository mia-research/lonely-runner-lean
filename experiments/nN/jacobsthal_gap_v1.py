"""The Jacobsthal gap criterion at a rung.

Dilating a rung (e, N) by a unit u makes it runners of speed c_d = d*u mod N (centred) and phase
d/(8e) on the unit grid s/N; each d forbids |c_d| open arcs of width 1/(4|c_d|).  If some allowed arc
is at least j(N)/N long (j = Jacobsthal's function), it contains a unit.  Reports, on the [1,40]
sets left after the fields N | 8, 3, 5: reach of the criterion, of its counting form, and with the
plain rung budget.
"""
import itertools, sys, time
from fractions import Fraction as Fr
from math import gcd
from collections import Counter
__file__ = __file__.replace('jacobsthal_gap_v1.py', 'ladder_budget_v1.py')
_src = open(__file__).read(); exec(_src[:_src.index("t0 = time.time()\nR = [S")])
def jacobsthal(N):
    U = [s for s in range(N) if gcd(s, N) == 1]
    if N == 1: return 1
    gaps = [(U[(k + 1) % len(U)] - U[k]) % N or N for k in range(len(U))]
    return max(gaps)
J = {}
def centred(x, N): x %= N; return x - N if x > N // 2 else x
def forbidden_arcs(S, e, N, u):
    """open arcs of theta in [0,1) forbidden by some disparity; None if a multiple of N kills the rung"""
    arcs = []
    for d in S:
        if d == e: continue
        c = centred(d * u, N); ph = Fr(d, 8 * e)
        if c == 0:
            if min(ph % 1, 1 - ph % 1) < Fr(1, 8): return None
            continue
        a = abs(c); sg = 1 if c > 0 else -1
        # ||c t + ph|| < 1/8  <=>  a t  in  (-sg ph - 1/8, -sg ph + 1/8) + Z
        for k in range(a):
            lo = (-sg * ph - Fr(1, 8) + k) / a
            arcs.append((lo % 1, Fr(1, 4 * a)))
    return arcs
def longest_allowed(arcs):
    if not arcs: return Fr(1), Fr(1)
    iv = []
    for lo, w in arcs:
        hi = lo + w
        if hi <= 1: iv.append((lo, hi))
        else: iv += [(lo, Fr(1)), (Fr(0), hi - 1)]
    iv.sort(); merged = []
    for lo, hi in iv:
        if merged and lo <= merged[-1][1]: merged[-1] = (merged[-1][0], max(merged[-1][1], hi))
        else: merged.append((lo, hi))
    gaps = [merged[k + 1][0] - merged[k][1] for k in range(len(merged) - 1)] + [1 - merged[-1][1] + merged[0][0]]
    covered = sum(hi - lo for lo, hi in merged)
    return max(gaps), 1 - covered
def gap_ok(S, e, N, counting=False):
    if N not in J: J[N] = jacobsthal(N)
    for u in range(N):
        if gcd(u, N) != 1: continue
        arcs = forbidden_arcs(S, e, N, u)
        if arcs is None: return False
        L, mu = longest_allowed(arcs)
        if counting:
            if mu >= Fr(len(arcs) * J[N], N): return True
        elif L >= Fr(J[N], N): return True
    return False
t0 = time.time()
R40 = [S for S in itertools.combinations(range(1, 41), 7)
       if eight_residual(S) and not has_rational_opening(S) and not has_thirds(S) and not has_fifths(S)]
g = [S for S in R40 if any(gap_ok(S, e, N) for e, N in rungs(S))]
c = [S for S in R40 if any(gap_ok(S, e, N, True) for e, N in rungs(S))]
pb = [S for S in R40 if any(plain_budget(S, e, N) for e, N in rungs(S))]
print(f"[1,40] after N | 8, 3, 5: {len(R40)}. gap criterion (longest allowed arc >= j(N)/N): {len(g)};  counting form: {len(c)};  plain budget: {len(pb)};  gap or plain: {len(set(g) | set(pb))}   ({time.time()-t0:.0f}s)")
miss = [S for S in R40 if S not in set(g) | set(pb)]
print("  neither:", len(miss), miss[:10])
