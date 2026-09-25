"""Per-lap budget.  grid_budget_v1 pools the laps r = 0..R, and extra laps can add cost.  Here the
budget is taken lap by lap: for some q <= 8, flank e (q | e) and lap r <= R valid for the multiples
of q, the non-multiples block fewer than |I| of the grid points i/q + (r + 1/8)/e, I = units or
all residues mod q.  Also: a FREE lap (no non-multiple blocks any point: an R6 at the pushed
vertex), and the union over the two groups.  On the hard sets of [1,40] and largest 41..60.
"""
import itertools, json, os, time
from math import gcd
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
H = [tuple(S) for S in json.load(open(os.path.join(HERE, 'hard_sets_41_60.json')))]
_rs = os.path.join(HERE, 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])
def ok(d, e, j): return e <= d * (8 * j + 1) % (8 * e) <= 7 * e
def per_lap(S, R):
    """(budget closes at some lap: units, all i, free lap, least R for either budget)"""
    res = {'units': None, 'all': None, 'free': None}
    for q in range(2, 9):
        for e in S:
            if e % q: continue
            M = e // q; non = [d for d in S if d % q]
            for r in range(min(R + 1, M)):
                if not all(ok(d, e, r) for d in S if d % q == 0): continue
                for name, I in (('units', [i for i in range(q) if gcd(i, q) == 1]), ('all', list(range(q)))):
                    cost = sum(1 for d in non for i in I if not ok(d, e, i * M + r))
                    if cost < len(I) and (res[name] is None or r < res[name]): res[name] = r
                    if cost == 0 and (res['free'] is None or r < res['free']): res['free'] = r
    return res
t0 = time.time()
R40 = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
H40 = [S for S in R40 if not any(rule(S, q, free_exact) for q in range(2, 9))]
for label, sets in (("[1,40]", H40), ("largest 41..60", H)):
    for R in (1, 2, 3, 5):
        res = [per_lap(S, R) for S in sets]
        u = sum(x['units'] is not None for x in res); a = sum(x['all'] is not None for x in res)
        f = sum(x['free'] is not None for x in res); either = sum(x['units'] is not None or x['all'] is not None for x in res)
        miss = [S for S, x in zip(sets, res) if x['units'] is None and x['all'] is None][:5]
        print(f"{label}, R = {R}: per-lap budget closes: units {u}, all i {a}, either {either} of {len(sets)}; free lap {f}; neither e.g. {miss}", flush=True)
print(f"total {time.time()-t0:.0f}s")
