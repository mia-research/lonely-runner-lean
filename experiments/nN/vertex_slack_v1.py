"""The vertex-slack condition: a rule with no flank and no lap.

At t = i/q + eps a multiple d of q reads d*eps; a non-multiple with residue s reads s*i/q + d*eps.
Over the units i, the vertex s*i/q nearest 0 is at gcd(d, q)/q.  So:

  VS(q): some eps has ||d eps|| >= 1/8 for every multiple d of q (a lower-order lonely problem in
         eps, at 1/8), and ||d eps|| <= gcd(d, q)/q - 1/8 for every non-multiple d (each stays in
         its vertex's safe zone).  Then t = i/q + eps is lonely for EVERY unit i.

Exact: every condition is a finite union of closed intervals in eps (period 1, integer speeds), so a
feasible eps exists iff some interval endpoint is feasible.  Endpoints: (N +- 1/8)/d for the
multiples, (N +- b_d)/d for the non-multiples, 0 <= N <= d.
Reported: on the whole [1,40] residual and on the hard sets with largest 41..60, how many satisfy
VS(q) for some q in 3..7 (q = 2 has one unit: VS(2) is loneliness itself) (q = 8 leaves a coprime d no slack: gcd/q - 1/8 = 0), and which q.
Also q = 1 as the control: VS(1) is just "S is lonely" (no non-multiples).
"""
import itertools, json, os, time
from fractions import Fraction as F
from math import gcd
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
H = [tuple(S) for S in json.load(open(os.path.join(HERE, 'hard_sets_41_60.json')))]
_rs = os.path.join(HERE, 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])

def vs(S, q):
    """Integer arithmetic.  eps = n/D; ||d eps|| = min(r, D - r)/D with r = d n mod D.
    Multiples: 8*min >= D.  Non-multiple, slack b = (8g - q)/(8q): 8q*min <= (8g - q)*D."""
    mult = [d for d in S if d % q == 0]; non = [(d, 8 * gcd(d, q) - q) for d in S if d % q]
    if any(c < 0 for _, c in non): return None
    cands = set()
    for d in mult:
        D = 8 * d
        for N in range(d + 1): cands.add((8 * N + 1, D)); cands.add((8 * N - 1, D))
    for d, c in non:
        D = 8 * q * d
        for N in range(d + 1): cands.add((8 * q * N + c, D)); cands.add((8 * q * N - c, D))
    for n, D in cands:
        n %= D
        good = True
        for d in mult:
            r = d * n % D
            if 8 * min(r, D - r) < D: good = False; break
        if not good: continue
        for d, c in non:
            r = d * n % D
            if 8 * q * min(r, D - r) > c * D: good = False; break
        if good: return (n, D)
    return None
def cover(S):
    return [q for q in range(3, 8) if vs(S, q) is not None]

t0 = time.time()
R40 = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
c = Counter(); first = Counter(); miss = []
for S in R40:
    qs = cover(S); c[bool(qs)] += 1
    if qs: first[qs[0]] += 1
    elif len(miss) < 10: miss.append(S)
print(f"[1,40] residual {len(R40)}: VS(q) for some q in 3..7 (q = 2 has one unit: VS(2) is loneliness itself): {c[True]}; not {c[False]}; least q {sorted(first.items())}; misses e.g. {miss}  ({time.time()-t0:.0f}s)", flush=True)
c = Counter(); first = Counter(); miss = []
for S in H:
    qs = cover(S); c[bool(qs)] += 1
    if qs: first[qs[0]] += 1
    elif len(miss) < 10: miss.append(S)
print(f"hard sets, largest 41..60 ({len(H)}): VS(q) some q in 3..7: {c[True]}; not {c[False]}; least q {sorted(first.items())}; misses e.g. {miss}  ({time.time()-t0:.0f}s)")
