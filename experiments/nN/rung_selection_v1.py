"""A rung-selection rule: R6 at q, rescued by R1 on the multiples of q.

For q >= 2 with a multiple of q in S, let e be the least multiple of q in S and take the rung
(e, q): the instants i/q + 1/(8e).  A multiple of q does not see the unit i, and reads as at e's
first opening, so it needs e's band: d mod 8e in [e, 7e] -- R1 applied to the multiples of q.  The
non-multiples then need a unit i they all leave clear (exact), or fewer blocked units than phi(q)
(the rung budget, a pigeonhole).  R6 is the case with no multiple of q at all.

At q = 2 the rule reads: e the least even disparity, every even one in [e, 7e] mod 8e, every odd one
outside (3e, 5e) mod 8e; the instant is 1/2 + 1/(8e).

Reports, on the v1 residual (EightResidual without the fields added since) of [1,30] and [1,40]:
how many sets the rule certifies for some q, exactly and by the budget, and the least q needed.
"""
import itertools, sys, time
from collections import Counter
_lb = __file__.replace('rung_selection_v1.py', 'ladder_budget_v1.py')
_src = open(_lb).read(); __file__ = _lb
exec(_src[:_src.index("t0 = time.time()\nR = [S")])

def free_exact(S, e, N):
    return any(all(not blocked(X(d, e, N, i), e) for d in S if d != e) for i in rung_units(e, N))

def rule(S, q, test):
    mult = [d for d in S if d % q == 0]
    if not mult: return False
    e = min(mult)
    if any(not (e <= d % (8 * e) <= 7 * e) for d in mult): return False
    return test(S, e, q)

for top in (30, 40):
    t0 = time.time(); n = ex = bu = 0; least = Counter(); miss = []
    for S in itertools.combinations(range(1, top + 1), 7):
        if not eight_residual(S): continue
        n += 1
        qe = [q for q in range(2, top + 1) if rule(S, q, free_exact)]
        if qe: ex += 1; least[min(qe)] += 1
        else: miss.append(S)
        bu += any(rule(S, q, plain_budget) for q in range(2, top + 1))
    print(f"[1,{top}] residual v1 {n}: rule + exact {ex}; rule + budget {bu}; least q {sorted(least.items())}; "
          f"no q {len(miss)} {miss[:5]}  ({time.time() - t0:.0f}s)")
