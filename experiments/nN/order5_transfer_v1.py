"""Order five's last sub-case, transferred to order eight: dilation by the largest, then shifts k/8.

Order five (OrderFiveResidualN): lap points K/F of the fastest runner F, K a dilation, then shifts
k/5 with a budget.  At order eight, with D the largest disparity, the instants K/D + k/8 are all
the a/(8D).  Reports: for the sets no q <= 8 certifies (Case B) and for the whole v1 residual of
[1,40], whether some K leaves fewer than 8 blocked (runner, shift) pairs over k = 0..7 -- the
shift budget, a pigeonhole -- and each runner's cost at the best K.
"""
import itertools, time
from collections import Counter
from math import gcd
_rs = __file__.replace('order5_transfer_v1.py', 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])
def lonely_at(S, a, q):      # instant a/q, exact: every d*a mod q at distance >= q/8 from 0
    return all(q <= 8 * (d * a % q) <= 7 * q for d in S)
def grid_classes(S):
    D = max(S); q = 8 * D
    return sorted({a % 8 for a in range(1, q) if lonely_at(S, a, q)})
def shift_blocked(S, D, K):
    """blocked (runner, shift) pairs at t = K/D + k/8, k = 0..7; exact on the grid a/(8D), a = 8K + kD"""
    q = 8 * D; tot = 0; per = {}
    for r in S:
        b = [k for k in range(8) if not (q <= 8 * (r * (8 * K + k * D) % q) <= 7 * q)]
        per[r] = b; tot += len(b)
    return tot, per
def recipe(S):
    D = max(S); best = None
    for K in range(1, D):
        tot, per = shift_blocked(S, D, K)
        if best is None or tot < best[0]: best = (tot, K, per)
    return best
t0 = time.time()
R = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
caseB = [S for S in R if not any(rule(S, q, free_exact) for q in range(2, 9))]
bud = 0; small_m = Counter()
for S in caseB:
    tot, K, per = recipe(S); D = max(S)
    ok = tot < 8; bud += ok
    # is the best K an order-5 dilation: K = m * d^-1 mod D with m small, for some runner d coprime to D?
    ms = [((K * d) % D, d) for d in S if d != D and gcd(d, D) == 1]
    mbest = min(ms, key=lambda x: min(x[0], D - x[0])) if ms else None
    small_m[min(mbest[0], D - mbest[0]) if mbest else None] += 1
    print(f"  {S}: least blocked pairs over K = {tot} (budget 8) at K = {K};  as m*d^-1: m = {mbest[0] if mbest else None} for d = {mbest[1] if mbest else None};  per runner {({r: len(b) for r, b in per.items()})}")
print(f"Case B: shift budget (fewer than 8 blocked pairs at some K) holds for {bud} of {len(caseB)};  |m| at the best K: {sorted(small_m.items(), key=lambda x: (x[0] is None, x[0]))}")
whole = sum(1 for S in R if recipe(S)[0] < 8)
print(f"whole [1,40] residual v1: shift budget at some K for {whole} of {len(R)}  ({time.time()-t0:.0f}s)")
