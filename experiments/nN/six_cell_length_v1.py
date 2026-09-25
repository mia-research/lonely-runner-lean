"""The induction statement on the six alone, in their own scale.

cell_lengths_v1 (B): the six other disparities of every hard set have a lonely cell at 1/8 at least
1/(4 d_max) long, so d_max is clear somewhere inside it.  Since d_6 < d_max, it suffices that
    L6: every set of six positive disparities has a lonely cell at 1/8 of length >= 1/(4 d_6),
d_6 its largest (the six's own scale: a quarter of the fastest one's lap).  Checked exhaustively on
every 6-subset of [1, N], with the least ratio (longest cell) * 4 d_6 and the sets attaining it.
"""
import itertools, sys, time
from fractions import Fraction as F
N = int(sys.argv[1]) if len(sys.argv) > 1 else 24
E = F(1, 8)
def nd(x): x = x % 1; return min(x, 1 - x)
def longest(S):
    pts = sorted({F(8 * n + s, 8 * d) % 1 for d in S for n in range(d + 1) for s in (1, -1)} | {F(0)})
    pts.append(F(1)); best = F(0); run = None
    for a, b in zip(pts, pts[1:]):
        if all(nd(d * (a + b) / 2) >= E for d in S):
            run = a if run is None else run
            best = max(best, b - run)
        else: run = None
    return best
t0 = time.time(); worst = []
for S in itertools.combinations(range(1, N + 1), 6):
    r = longest(S) * 4 * max(S)
    worst.append((r, S))
worst.sort()
fails = [x for x in worst if x[0] < 1]
print(f"all 6-subsets of [1,{N}] ({len(worst)}): ratio < 1 for {len(fails)}; least ratios {[(float(r), S) for r, S in worst[:8]]}  ({time.time()-t0:.0f}s)")
