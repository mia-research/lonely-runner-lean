"""E144: the owner's finiteness claim, tested at the landing with laps dropped (grid: only the place in the lap
matters).  Type of a landing = per rank, the eighth-slot of the runner's position (1..6; the flank at exactly 1 marked
'F'), plus the flank rank.  Count distinct types as the readings' range grows (N = 12, 16, 20, 24), by spread class.
Exact."""
import itertools, sys
from fractions import Fraction as F
from math import floor
from collections import defaultdict
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def cascade(T):
    t = F(1, 8 * T[0])
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
def ltype(T):
    t = cascade(T); out = []
    for d in T:
        p = (8 * d * t) % 8
        out.append('F' if p == 1 else str(floor(p)))
    return ''.join(out)
seen = defaultdict(set)
for N in (12, 16, 20, 24):
    for T in itertools.combinations(range(1, N + 1), 7):
        S = F(T[-1], T[0])
        cls = 'A (<=7)' if S <= 7 else 'band (7,9]' if S <= 9 else 'B (9,24]'
        seen[(N, cls)].add(ltype(T))
    print("N = %2d:" % N, {cls: len(seen[(N, cls)]) for cls in ('A (<=7)', 'band (7,9]', 'B (9,24]')},
          " all:", len(set().union(*[seen[(N, c)] for c in ('A (<=7)', 'band (7,9]', 'B (9,24]')])))
    sys.stdout.flush()
