"""Slot-sharers in integer push-out families.  Runner i shares its slot with partner j when |v_j - v_i| = 8q (q>=1)
and d_min(i) = 1.  Predicted framework time (BSM, unchanged): t = 1/8 + 1/(8*|v_j - v_i|), with j exactly 1/8 ahead
(or behind).  Checked over (1..7,x), (1..6,x-1,x), (1..5,x-2,x-1,x), x = 8..200, and random integer sets."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from math import floor
from collections import Counter
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from full_transit_positions_v2 import first_time
def fr(x): return x - floor(x)
def check(V, c, ex):
    V = [F(v) for v in V]
    for i in range(8):
        ds = {j: abs(V[j] - V[i]) for j in range(8) if j != i}
        m = min(ds.values())
        sharers = [j for j, d in ds.items() if d.denominator == 1 and d.numerator % (8 * m) == 0]
        if not sharers: continue
        t = first_time(V, i)
        key = f"{len(sharers)} slot-sharer(s), d_min={m if m==1 else '>1'}"
        c[key] += 1
        preds = sorted({F(1, 8 * m) + 1 / (8 * ds[j]) for j in sharers})
        if t in preds: c[key + ": t = 1/(8 d_min) + 1/(8 D) for a sharer"] += 1
        elif len(ex) < 6: ex.append(([str(v) for v in V], i + 1, str(t), [str(p) for p in preds]))
c = Counter(); ex = []
for x in range(8, 201):
    for V in [(1,2,3,4,5,6,7,x), (1,2,3,4,5,6,x-1,x), (1,2,3,4,5,x-2,x-1,x)]:
        if len(set(V)) == 8 and sorted(V) == list(V): check(V, c, ex)
print("push-out families x = 8..200:"); [print("  ", k, v) for k, v in sorted(c.items())]
print("  exceptions e.g.:", ex)
c = Counter(); ex = []
rng = random.Random(21)
for _ in range(3000): check(sorted(rng.sample(range(1, 200), 8)), c, ex)
print("random integers [1,200], 3000 arrangements:"); [print("  ", k, v) for k, v in sorted(c.items())]
print("  exceptions e.g.:", ex)
