"""Descent at modulus q through order seven's margin -- a test that turned out VACUOUS.

For q <= 8: M = {d/q : q | d} has at most six elements and is lonely at 1/7 (order seven); the test
asks for t with q*t mod 1 in M's lonely set at 1/7 and S lonely at 1/8.  Every set of the v1
residual of [1,40] passes at q = 2.  That says nothing: the condition is S lonely with its even
disparities at least 1/7 from the subject, which delta(S) >= 1/7 already gives for all but two
sets (ideal_events_v1).  Kept so the result is not mistaken for evidence.
"""
import itertools, time
from fractions import Fraction as Fr
from collections import Counter
_rs = __file__.replace('descent_q_v1.py', 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])
def lonely_cells(S, n):
    """closed lonely cells of integer set S at threshold 1/n in [0, 1)"""
    if not S: return [(Fr(0), Fr(1))]
    z = sorted(((Fr(n * k - 1, n * d), Fr(n * k + 1, n * d)) for d in S for k in range(0, d + 1)))
    out = []; hi = None
    for lo, h in z:
        if hi is not None and lo >= hi and hi < 1: out.append((hi, min(lo, Fr(1))))
        if hi is None or h > hi: hi = h
    return out
def descent_q(S, q):
    M = sorted({d // q for d in S if d % q == 0})
    X = [d for d in S if d % q]
    if not M or not X: return None
    CM = lonely_cells(M, 7)                     # M lonely at 1/7 (order seven), in tau
    CS = lonely_cells(S, 8)                     # S lonely at 1/8, in t
    # need t in a CS cell with q t mod 1 in a CM cell: preimages (c + i)/q
    for i in range(q):
        for a, b in CM:
            lo, hi = (a + i) / q, (b + i) / q
            for c, dd in CS:
                if max(lo, c) <= min(hi, dd): return True
    return False
t0 = time.time()
R = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
ok = 0; byq = Counter(); miss = []; Mlonely = Counter()
for S in R:
    qs = [q for q in range(2, 9) if descent_q(S, q)]
    if qs: ok += 1; byq[min(qs)] += 1
    else: miss.append(S)
print(f"[1,40] residual v1 {len(R)}: descent at some q <= 8 (M = multiples/q lonely at 1/7, S lonely at 1/8 over it): {ok}  ({time.time()-t0:.0f}s)")
print("  least q:", sorted(byq.items()), "  none:", len(miss), miss[:8])
