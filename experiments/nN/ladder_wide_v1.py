"""A ladder-wide count with the disparities decoupled.

For a flank e, the rungs are its divisors N, with phi(N) units each; beta_N(d) is the number of
units of rung N that d blocks.  For weights w_N >= 0 depending on e and N only: if
sum_d sum_N w_N beta_N(d) < sum_N w_N phi(N), some rung has a unit blocked by none.  The left side
is a sum over disparities of a quantity depending only on (d, e), so the disparities no longer
interact.  With w_N = 1/phi(N) the condition reads sum_d W(d, e) < tau(e), W(d, e) the average
blocked fraction of d across the ladder.

Reports, on the v1 residual of [1,30]: reach of several fixed weightings against the rung budget
(best single rung per set); the best flank's ratio sum W / tau; and W/tau by the size d/e.
"""
import itertools, time
from fractions import Fraction as Fr
from math import gcd
from collections import Counter
__file__ = __file__.replace('ladder_wide_v1.py', 'ladder_budget_v1.py')
_src = open(__file__).read(); exec(_src[:_src.index("t0 = time.time()\nR = [S")])
PHI = {}; 
def phi(N):
    if N not in PHI: PHI[N] = sum(1 for i in range(N) if gcd(i, N) == 1)
    return PHI[N]
WC = {}
def W(d, e):
    if (d, e) not in WC:
        WC[(d, e)] = sum(Fr(sum(1 for i in rung_units(e, N) if blocked(X(d, e, N, i), e)), phi(N)) for N in range(1, e + 1) if e % N == 0)
    return WC[(d, e)]
def tau(e): return sum(1 for N in range(1, e + 1) if e % N == 0)
def ladder_ok(S):
    return [e for e in S if sum(W(d, e) for d in S if d != e) < tau(e)]
t0 = time.time()
R30 = [S for S in itertools.combinations(range(1, 31), 7) if eight_residual(S)]
hits = [S for S in R30 if ladder_ok(S)]
pb = [S for S in R30 if any(plain_budget(S, e, N) for e, N in rungs(S))]
print(f"[1,30] residual v1 {len(R30)}: ladder-wide count (sum_d W(d,e) < tau(e) at some flank e in S): {len(hits)};  plain rung budget: {len(pb)}  ({time.time()-t0:.0f}s)")
# how far off is it: best ratio sum W / tau per set
ratios = sorted(min(sum(W(d, e) for d in S if d != e) / tau(e) for e in S) for S in R30)
print("  best flank's  sum_d W / tau  : min {:.3f}  10% {:.3f}  median {:.3f}  90% {:.3f}  max {:.3f}".format(*(float(ratios[int(q * (len(ratios) - 1))]) for q in (0, .1, .5, .9, 1))))
# W(d, e) itself: its distribution, against d/e
dist = Counter()
for (d, e), w in WC.items():
    dist[(min(round(d / e * 2) / 2, 4), round(float(w / tau(e)) * 20) / 20)] += 1
print("  W(d,e)/tau(e) by d/e (rounded to 1/2): mean")
by = {}
for (d, e), w in WC.items():
    k = min(round(d / e * 2) / 2, 4); by.setdefault(k, []).append(float(w / tau(e)))
for k in sorted(by): print(f"    d/e ~ {k:4}: mean {sum(by[k]) / len(by[k]):.3f}  max {max(by[k]):.3f}  (n = {len(by[k])})")
BC = {}
def beta(d, e, N):
    if (d, e, N) not in BC: BC[(d, e, N)] = sum(1 for i in rung_units(e, N) if blocked(X(d, e, N, i), e))
    return BC[(d, e, N)]
schemes = {
    "1/phi, all N":            lambda e, N: Fr(1, phi(N)),
    "1/phi, N >= 2":           lambda e, N: Fr(1, phi(N)) if N >= 2 else 0,
    "1/phi, N >= 3":           lambda e, N: Fr(1, phi(N)) if N >= 3 else 0,
    "1/phi, N >= e/2":         lambda e, N: Fr(1, phi(N)) if 2 * N >= e else 0,
    "1 (flank union bound)":   lambda e, N: 1,
    "N/phi, N >= 2":           lambda e, N: Fr(N, phi(N)) if N >= 2 else 0,
    "1/phi^2, N >= 2":         lambda e, N: Fr(1, phi(N) ** 2) if N >= 2 else 0,
}
for name, w in schemes.items():
    def ok(S):
        for e in S:
            Ns = [N for N in range(1, e + 1) if e % N == 0 and w(e, N)]
            if not Ns: continue
            if sum(w(e, N) * beta(d, e, N) for d in S if d != e for N in Ns) < sum(w(e, N) * phi(N) for N in Ns): return True
        return False
    print(f"  weights {name:24s}: {sum(1 for S in R30 if ok(S))} of {len(R30)}")
