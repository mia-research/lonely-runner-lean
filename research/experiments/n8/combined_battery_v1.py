"""Combined battery: scale jumps and neighbour structure, recorded together per runner.
Per runner i (own d_min m, least lonely lattice L, dead-lattice prediction P):
  sig      neighbours at its time, by speed rank (cyclic): '+-1', '+-3', 'other'
  tie_at1  at the first own-AP instant u = 1/8 (t = 1/(8m)), some other runner sits exactly on the subject
           (circle distance 0)  -- a shared slot
  nbr_tie  at its own time, the runner behind or ahead is a tie of two or more runners
Cross-tabulated against the scale outcome: L == 1; L == P > 1 (jump as predicted); L > P (extra step)."""
import sys, random
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
from itertools import combinations
from collections import Counter, defaultdict
from multiprocessing import Pool
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/experiments/n8")
    from scale_jump_battery_v1 import least_L, predicted_L, sides, dist, fr
def job(V):
    out = []
    for i in range(8):
        L, u, m = least_L(V, i); P = predicted_L(V, i)
        if L is None: out.append(None); continue
        t = u / m; b, a = sides(V, i, t)
        s = "other"
        for c in (1, 3):
            if len(a) == len(b) == 1 and {min(a), min(b)} == {(i - c) % 8, (i + c) % 8}: s = f"+-{c}"
        tie1 = any(dist((V[j] - V[i]) / (8 * m)) == 0 for j in range(8) if j != i)
        outcome = "scale 1" if L == 1 else ("jump = prediction" if L == P else "jump > prediction")
        out.append(dict(outcome=outcome, sig=s, tie_at1=tie1, nbr_tie=len(a) > 1 or len(b) > 1, extra=L - P))
    return out
if __name__ == "__main__":
    rng = random.Random(17)
    fams = [("all 8-subsets of [1,16], gcd 1", [tuple(F(v) for v in c) for c in combinations(range(1, 17), 8) if reduce(gcd, c) == 1]),
            ("random [1,100]", [tuple(F(v) for v in sorted(rng.sample(range(1, 101), 8))) for _ in range(1500)]),
            ("random [1,1000]", [tuple(F(v) for v in sorted(rng.sample(range(1, 1001), 8))) for _ in range(400)])]
    with Pool(8) as pool:
        for name, arrs in fams:
            recs = [x for r in pool.map(job, arrs, chunksize=16) for x in r if x]
            print(f"\n=== {name}: {len(recs)} runners")
            tab = defaultdict(Counter)
            for x in recs:
                tab[x["outcome"]]["runners"] += 1
                tab[x["outcome"]][f"neighbours {x['sig']}"] += 1
                tab[x["outcome"]]["a runner shares its slot at u=1/8"] += x["tie_at1"]
                tab[x["outcome"]]["tied neighbour at its time"] += x["nbr_tie"]
            for k in ("scale 1", "jump = prediction", "jump > prediction"):
                print(f"  {k:>18}: {dict(tab[k])}")
            sys.stdout.flush()
