"""Is the cascade's fixed point the FIRST lonely instant?  (Theorem 11(b), first_isolation_of_fixed)

Exact check: the earliest lonely point in (0, 1] from a full enumeration of the zone endpoints
(every (N +- 1/8)/d, and midpoints between consecutive endpoints; one-point cells included), against
the cascade run from the bound 1/(8 d_min).  On 3,000 random residual sets of [1,60], all 1,436
hard sets with largest 41..60, and 2,000 random 7-sets of [1,60] with no filter.
"""
import json, os, random, math
from fractions import Fraction as F
HERE = os.path.dirname(os.path.abspath(__file__))
H = [tuple(S) for S in json.load(open(os.path.join(HERE, 'hard_sets_41_60.json')))]
_rs = os.path.join(HERE, 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])
E = F(1, 8)
def nd(x): x = x % 1; return min(x, 1 - x)
def lonely(S, t): return all(nd(d * t) >= E for d in S)
def cascade(S):
    t = E / min(S)
    while True:
        way = [d for d in S if nd(d * t) < E]
        if not way: return t
        nx = []
        for d in way:
            N = math.floor(d * t - E); o = (N + E) / d
            if o < t: o = (N + 1 + E) / d
            nx.append(o)
        t = max(nx)
def earliest(S):
    pts = sorted({F(8 * N + s, 8 * d) for d in S for N in range(d + 1) for s in (1, -1) if F(8 * N + s, 8 * d) > 0})
    cand = []
    for a, b in zip(pts, pts[1:]): cand += [a, (a + b) / 2]
    cand.append(pts[-1])
    for t in sorted(cand):
        if t <= 1 and lonely(S, t): return t
    return None
random.seed(21)
res = []
while len(res) < 3000:
    S = tuple(sorted(random.sample(range(1, 61), 7)))
    if eight_residual(S): res.append(S)
raw = [tuple(sorted(random.sample(range(1, 61), 7))) for _ in range(2000)]
for label, sets in (("random residual [1,60]", res), ("hard sets 41..60", H), ("random 7-sets [1,60]", raw)):
    diff = [(S, cascade(S), earliest(S)) for S in sets]
    bad = [(S, float(c), float(e)) for S, c, e in diff if c != e]
    print(f"{label} ({len(sets)}): cascade fixed point == earliest lonely instant in {len(sets) - len(bad)}; differs in {len(bad)} {bad[:5]}")
