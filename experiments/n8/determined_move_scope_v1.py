"""Scope of the determined move (Construction8.blocked_lands_on_threshold + unblocked_stays_clear), in BSM terms.
Integer readings s = d/d_min.  Hypothesis at unit p: every non-sharer reading has 1 <= s*p mod 8 <= 6, and the sharer
reading is the largest.  Move time: t = p/(8 d_min) + 1/(8 D_sharer).  Compare with the BSM framework time."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from collections import Counter
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from full_transit_positions_v2 import first_time
def analyse(V, c):
    V = [F(v) for v in V]
    for i in range(8):
        ds = [abs(V[j] - V[i]) for j in range(8) if j != i]; m = min(ds)
        s = [d / m for d in ds]
        if any(x.denominator != 1 for x in s): continue
        s = [int(x) for x in s]
        sh = [x for x in s if x % 8 == 0]
        if len(sh) != 1: continue
        t = first_time(V, i)
        hyp_times = []
        for p in (1, 3, 5, 7):
            if max(s) == sh[0] and all(1 <= (x * p) % 8 <= 6 for x in s if x % 8):
                hyp_times.append(F(p, 8 * m) + F(1, 8 * sh[0] * m))
        hyp = bool(hyp_times)
        eq = t in hyp_times
        c[("lemma hypothesis holds at some p", hyp, "BSM time = that move", eq)] += 1
        if not hyp:
            c[("hypothesis fails", "BSM time = 1/(8m) + 1/(8D) anyway", t == F(1, 8 * m) + F(1, 8 * sh[0] * m))] += 1
c = Counter()
for x in range(8, 201):
    for V in [(1,2,3,4,5,6,7,x), (1,2,3,4,5,6,x-1,x), (1,2,3,4,5,x-2,x-1,x)]:
        if len(set(V)) == 8 and sorted(V) == list(V): analyse(V, c)
rng = random.Random(22)
for _ in range(4000): analyse(sorted(rng.sample(range(1, 150), 8)), c)
for k, v in sorted(c.items(), key=str): print(k, v)
