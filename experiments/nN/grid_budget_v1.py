"""The two-dimensional budget: units (or all residues) mod q  x  laps r = 0..R.

For q <= 8 and a flank e with q | e, M = e/q, the candidates are the openings j = i*M + r of e,
instants i/q + (r + 1/8)/e.  A multiple d = q*k reads k*(8r + 1)/(8M) mod 1: it depends on r only,
so the multiples of q decide which laps are VALID.  A non-multiple reads d*(8j + 1)/(8e) and depends
on (i, r).  Budget: over the valid laps, the blocked (non-multiple, grid point) pairs number fewer
than the grid points -> some grid point is blocked by none: a pigeonhole certificate.

Reported on the hard sets ([1,40]: 28; largest 41..60: 1,436), for R = 0..3 and both groups:
  exact  -- some grid point is lonely (the search, for reference);
  budget -- the pigeonhole closes for some (q, e);
and the cost structure where it fails: the largest single-disparity share of the grid.
"""
import itertools, json, os, time
from math import gcd
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
H = [tuple(S) for S in json.load(open(os.path.join(HERE, 'hard_sets_41_60.json')))]
_rs = os.path.join(HERE, 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])

def ok(d, e, j): return e <= d * (8 * j + 1) % (8 * e) <= 7 * e

def grid(S, q, e, R, units):
    M = e // q
    I = [i for i in range(q) if not units or gcd(i, q) == 1]
    laps = [r for r in range(min(R + 1, M)) if all(ok(d, e, r) for d in S if d % q == 0)]
    non = [d for d in S if d % q]
    pts = [(i, r) for r in laps for i in I]
    blocked = {d: {(i, r) for (i, r) in pts if not ok(d, e, i * M + r)} for d in non}
    exact = any(all((p not in blocked[d]) for d in non) for p in pts)
    cost = sum(len(b) for b in blocked.values())
    return pts, exact, cost, max((len(b) for b in blocked.values()), default=0)

def study(sets, label):
    print(f"{label}: {len(sets)} hard sets", flush=True)
    for units in (True, False):
        for R in range(4):
            ex = bu = 0; slack = Counter()
            for S in sets:
                e_ok = b_ok = False; best = None
                for q in range(2, 9):
                    for e in S:
                        if e % q: continue
                        pts, exact, cost, mx = grid(S, q, e, R, units)
                        if not pts: continue
                        e_ok |= exact
                        if cost < len(pts): b_ok = True
                        ratio = cost / len(pts)
                        if best is None or ratio < best: best = ratio
                ex += e_ok; bu += b_ok
                if best is not None: slack[round(best, 1)] += 1
            print(f"   {'units' if units else 'all i'}, R = {R}: exact {ex}, budget closes {bu}; "
                  f"best blocked/grid ratio {sorted(slack.items())[:6]}", flush=True)

t0 = time.time()
R40 = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
H40 = [S for S in R40 if not any(rule(S, q, free_exact) for q in range(2, 9))]
study(H40, "[1,40]")
study(H, "largest 41..60")
print(f"total {time.time()-t0:.0f}s")
