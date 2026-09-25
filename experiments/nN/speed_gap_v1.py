"""A rung as a small lonely-runner problem, and the closed-form blocked interval.

Rung (e, N), M = e/N, openings a = 8*i*M + 1 over the units i mod N.  Choose a unit u (a dilation)
and put c_d = the centred residue of d*u mod N and s = i*u^-1 mod N; then d*i = c_d*s mod N, and d's
reading at s is ||c_d*s/N + d/(8e)||: runners of speed c_d and phase d/(8e) on the unit grid.

Write d = P*M + rho (P = floor(d/M), 0 <= rho < M).  Then d is blocked at s exactly when
t = c_d*s mod N lies in the interval (read mod N)

    T_d = [ ceil((1 - N - P)/8) - eps_d ,  floor((N - 1 - P)/8) ],   eps_d = [rho > 0 and 8 | N + P].

So a speed-+1 blocker blocks one interval of s, a speed-c blocker the preimage of T_d under c.
Between two speed-+1 intervals (d ending, d' starting) the free integers exist exactly when
(B - A)/8 + (alpha + beta)/8 >= 2 + eps_d', A = N - 1 - P_d, B = 1 - N - P_d' (+ 8N k),
alpha = (N - 1 - P_d) mod 8, beta = (N - 1 + P_d') mod 8: length plus a residue bonus mod 8.

Reports: the closed form against Theorem 10 on 400 residual sets of [1,30] (seed 3), every rung,
dilation and disparity; and on the [1,40] sets left after the fields N | 8, 3, 5, the sets with a
certificate at a rung where some dilation makes every active blocker's speed at most 1, 2, 3.
"""
import itertools, random, time
from math import gcd
from collections import Counter
_src = open(__file__.replace('speed_gap_v1.py', 'ladder_budget_v1.py')).read()
__file__ = __file__.replace('speed_gap_v1.py', 'ladder_budget_v1.py'); exec(_src[:_src.index("t0 = time.time()\nR = [S")])
def ceil8(x): return -((-x) // 8)
def T(d, e, N):
    """speed-one blocked interval (lo, hi) of t in Z (read mod N) for disparity d at rung (e, N)"""
    M = e // N; P, rho = d // M, d % M
    eps = 1 if (rho > 0 and (N + P) % 8 == 0) else 0
    return ceil8(1 - N - P) - eps, (N - 1 - P) // 8
def in_T(t, d, e, N):
    lo, hi = T(d, e, N)
    if hi < lo: return False
    return (t - lo) % N <= hi - lo or hi - lo >= N - 1
def centred(x, N): x %= N; return x - N if x > N // 2 else x
# 1. exactness of the closed form, against Theorem 10 directly
random.seed(3)
R30 = [S for S in itertools.combinations(range(1, 31), 7) if eight_residual(S)]
bad = checked = 0
for S in random.sample(R30, 400):
    for e, N in rungs(S):
        for u in (i for i in range(N) if gcd(i, N) == 1):
            for d in S:
                if d == e: continue
                c = centred(d * u, N)
                for s in range(N):
                    i = (s * u) % N if N > 1 else 0
                    direct = blocked(X(d, e, N, i), e)
                    closed = in_T((c * s) % N, d, e, N)
                    checked += 1; bad += (direct != closed)
print(f"closed-form blocked set vs Theorem 10: {checked} checks, {bad} disagreements")
# 2. speed-one rungs: a unit u making every active blocker speed +-1; certificate there, read off the intervals
def speed_one_cert(S, e, N):
    U = [s for s in range(N) if gcd(s, N) == 1]
    for u in U:
        cs = {d: centred(d * u, N) for d in S if d != e}
        act = [d for d in cs if any(in_T((cs[d] * s) % N, d, e, N) for s in U)]
        if any(abs(cs[d]) > 1 for d in act): continue
        free = [s for s in U if not any(in_T((cs[d] * s) % N, d, e, N) for d in act)]
        if free: return True
    return False
t0 = time.time()
R40 = [S for S in itertools.combinations(range(1, 41), 7)
       if eight_residual(S) and not has_rational_opening(S) and not has_thirds(S) and not has_fifths(S)]
pb = {S for S in R40 if any(plain_budget(S, e, N) for e, N in rungs(S))}
so = {S for S in R40 if any(speed_one_cert(S, e, N) for e, N in rungs(S))}
print(f"[1,40] after N | 8, 3, 5: {len(R40)}; certified at a speed-one rung: {len(so)}; of the 312 the plain budget misses: {len(so - pb)}; plain or speed-one: {len(pb | so)}  ({time.time()-t0:.0f}s)")
def speed_cert(S, e, N, cmax):
    U = [s for s in range(N) if gcd(s, N) == 1]
    for u in U:
        cs = {d: centred(d * u, N) for d in S if d != e}
        act = [d for d in cs if any(in_T((cs[d] * s) % N, d, e, N) for s in U)]
        if any(abs(cs[d]) > cmax for d in act): continue
        if any(not any(in_T((cs[d] * s) % N, d, e, N) for d in act) for s in U): return True
    return False
for cmax in (2, 3):
    sc = {S for S in R40 if any(speed_cert(S, e, N, cmax) for e, N in rungs(S))}
    print(f"speed <= {cmax}: {len(sc)}; of the 312 plain misses: {len(sc - pb)}; plain or speed <= {cmax}: {len(pb | sc)}")
