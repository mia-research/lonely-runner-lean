"""The rung budget, and the linked budget, on the order-eight residual.

A rung is a flank e and a divisor N of e; M = e/N.  Its openings are a = 8*i*M + 1, i in Z/N, and
its new instants are the units i (the others are rungs of smaller N).  Write X_d(i) = d*a mod 8e;
d blocks i when X_d(i) is within e of 0 (X < e or X > 7e), Theorem 10's band from the other side.

Rung budget: if the blocked units, counted with multiplicity over the disparities, number fewer
than phi(N), some unit is blocked by none -- a pigeonhole.  R4 is N = 8 at the largest multiple.

Links.  If N | d' - c*d then X_d'(i) = c*X_d(i) + (d' - c*d) mod 8e at every opening of the rung,
exactly: the (d' - c*d)*8*i*M part is a multiple of 8e.  So a group of disparities joined by such
links is blocked exactly where ONE progression X_r(i) lands in an explicit union of arcs.  The
linked budget counts each group's blocked units once (computed from X_r, and checked against the
direct union), summed over groups.

Reports: the plain budget on the v1 residual of [1,30]; the sets it misses; the linked budget on
them for |c| <= 1 and |c| <= 2; and both budgets on the [1,40] sets left after the rational-opening
fields N | 8, 3, 5 (eight_residual_count_v4's residual there).
"""
import itertools, sys, time
from math import gcd
sys.argv = [sys.argv[0], '30']
exec(open(__file__.replace('ladder_budget_v1.py', 'eight_residual_count_v5.py')).read().split('t0 = time.time()')[0])
exec(open(__file__.replace('ladder_budget_v1.py', 'shift_levels_six_eight_v1.py')).read().split('t0 = time.time()')[0])

def blocked(X, e): return X < e or X > 7 * e

def rung_units(e, N): return [i for i in range(N) if gcd(i, N) == 1]

def X(d, e, N, i): return d * (8 * i * (e // N) + 1) % (8 * e)

def plain_budget(S, e, N):
    U = rung_units(e, N)
    return sum(1 for d in S if d != e for i in U if blocked(X(d, e, N, i), e)) < len(U)

def linked_budget(S, e, N, cmax, check=False):
    U = rung_units(e, N); act = [d for d in S if d != e]
    rep = {}; total = 0
    for d0 in act:
        if d0 in rep: continue
        rep[d0] = (d0, 1, 0); comp = [d0]; stack = [d0]
        while stack:
            u = stack.pop(); r, mu, du = rep[u]
            for v in act:
                if v in rep: continue
                for c in [s * k for k in range(1, cmax + 1) for s in (1, -1)]:
                    if (v - c * u) % N == 0:
                        rep[v] = (r, c * mu, (c * du + v - c * u) % (8 * e)); comp.append(v); stack.append(v)
                        break
        r = d0
        st = {i for i in U if any(blocked((rep[d][1] * X(r, e, N, i) + rep[d][2]) % (8 * e), e) for d in comp)}
        if check:
            assert st == {i for i in U if any(blocked(X(d, e, N, i), e) for d in comp)}, (S, e, N)
        total += len(st)
    return total < len(U)

def rungs(S): return [(e, N) for e in S for N in range(1, e + 1) if e % N == 0]

t0 = time.time()
R = [S for S in itertools.combinations(range(1, 31), 7) if eight_residual(S)]
miss = [S for S in R if not any(plain_budget(S, e, N) for e, N in rungs(S))]
print(f"[1,30], EightResidual v1: {len(R)} sets; plain rung budget at some rung: {len(R) - len(miss)}; missed: {len(miss)}")
for cmax in (1, 2):
    left = [S for S in miss if not any(linked_budget(S, e, N, cmax, check=True) for e, N in rungs(S))]
    print(f"  linked budget, links d' = c d (mod N) with |c| <= {cmax}: reaches {len(miss) - len(left)} of the {len(miss)}; left {left}")
print(f"  ({time.time() - t0:.0f}s)")

t0 = time.time()
R40 = [S for S in itertools.combinations(range(1, 41), 7)
       if eight_residual(S) and not has_rational_opening(S) and not has_thirds(S) and not has_fifths(S)]
m40 = [S for S in R40 if not any(plain_budget(S, e, N) for e, N in rungs(S))]
print(f"[1,40], residual after the fields N | 8, 3, 5: {len(R40)} sets; plain budget misses {len(m40)}")
for cmax in (1, 2, 3):
    left = [S for S in m40 if not any(linked_budget(S, e, N, cmax) for e, N in rungs(S))]
    print(f"  linked budget |c| <= {cmax}: left {len(left)} {left[:8]}")
print(f"  ({time.time() - t0:.0f}s)")
