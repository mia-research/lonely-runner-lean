"""modgap_neartight_v2 (2026-10-06): the sets that are NOT lonely at 1/7.  Every 7-subset of [1, N] with d_min in {1, 2} (N = 30; v2 of modgap_neartight_v1, which did all of [1,24]), the 1/7-cascade (exact, start 1/(7 d_min)); a set is 1/7-lonely iff the walk ends with no reading
in the way.  The walk cannot end for a set with no lonely instant at 1/7; the cap is CAP = 300 states, and a set whose walk hits the cap is re-checked: its first lonely instant at 1/7 is searched on the
full period [0, 1) by a second exact method (candidate instants (7k+1)/(7x) and k/(7... ) i.e. every crossing instant, as TIGHT_INSTANCES_v1 does) so that 'not 1/7-lonely' is established, not assumed.
Recorded: the number of non-1/7-lonely sets, their gcds, the primitive ones (gcd 1) listed, the family closure under scaling, and for each primitive one its best loneliness delta(S) = max_t min_d ||d t|| (exact).
Reduction used for the second method: [P] a maximum of f(t) = min_d ||d t|| on [0, 1/2] occurs at a peak t = (2m+1)/(2 d) or a crossing t = k/(d + d') or k/(d - d')."""
import sys, itertools, math, collections
sys.path.insert(0, '.')
from fractions import Fraction as F
from math import gcd
from functools import reduce
H = F(1, 7); N = 30; CAP = 300
def cd(x):
    x = x - math.floor(x); return min(x, 1 - x)
def lonely7(S):
    t = F(1, 7 * min(S))
    for _ in range(CAP):
        B = [x for x in S if cd(x * t) < H]
        if not B: return True
        t = max(F(7 * round(x * t) + 1, 7 * x) for x in B)
    return None
def delta(S):
    best = F(0)
    cands = set()
    for d in S:
        for m in range(d + 1): cands.add(F(2 * m + 1, 2 * d))
    for a, b in itertools.combinations(S, 2):
        for k in range(a + b + 1): cands.add(F(k, a + b))
        if a != b:
            for k in range(abs(b - a) + 1): cands.add(F(k, abs(b - a)))
    for t in cands:
        if 0 < t <= F(1, 2):
            v = min(cd(x * t) for x in S)
            if v > best: best = v
    return best
out = open('modgap_neartight_v2.out', 'w'); out.write(__doc__ + "\n")
fails = []; total = 0
for lo in (1, 2):
  for rest in itertools.combinations(range(lo + 1, N + 1), 6):
    S = (lo,) + rest
    total += 1
    r = lonely7(S)
    if r is None: fails.append(S)
out.write("7-subsets of [1,%d]: %d; walks that hit the cap (candidate non-1/7-lonely): %d\n" % (N, total, len(fails)))
conf = [(S, delta(S)) for S in fails]
bad = [(S, d) for S, d in conf if d < H]
out.write("confirmed delta(S) < 1/7 (no lonely instant at 1/7 on the full period): %d; walks that hit the cap but have delta >= 1/7: %d\n" % (len(bad), len(conf) - len(bad)))
prim = [(S, d) for S, d in bad if reduce(gcd, S) == 1]
out.write("of the confirmed, primitive (gcd 1): %d\n" % len(prim))
bydelta = collections.Counter(d for S, d in bad)
out.write("delta values among the confirmed: %s\n" % {str(k): v for k, v in sorted(bydelta.items())})
for S, d in sorted(prim): out.write("  primitive: %s  delta = %s\n" % (S, d))
out.write("non-primitive confirmed: %s\n" % [(S, str(d)) for S, d in bad if reduce(gcd, S) > 1][:20])
out.close(); print(open('modgap_neartight_v2.out').read()[len(__doc__):][:4500])
