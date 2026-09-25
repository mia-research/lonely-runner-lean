"""The bound on t_pred, by collapsing the train.  Subject readings: core C and a fast train {N + e : e in E},
|C| + |E| = 7, N >= 56 * max(C u E).  Take two ADJACENT train offsets i < j and put the fast phase at
y = (i + j) * tau: the train's condition becomes ||(2e - i - j) tau|| >= 1/8, and i, j give the SAME reading
j - i.  So R = {2c} u {|2e - i - j|} has at most 6 readings: an order-seven object, lonely at 1/7 (native).
At its instant tau, t0 = 2 tau has the core clear at 1/7 and the train's offsets 1/7 from y; within one turn
1/N the fast phase reaches y (sync_block), and the margin 1/7 - 1/8 = 1/56 absorbs the drift.
Claim checked here: t* <= B + 1/N, B = min over adjacent pairs of 2 * tau7(R), tau7 = R's first instant clear
at 1/7 (cascade at threshold 1/7).  B depends on C and E only, never on N.  Exact."""
import random
from fractions import Fraction as F
from math import floor
from arrangement_lib import readings, nd
from isolated_persistence_v1 import cascade_cap
from handoff_directed_v1 import run

def cascade_q(ds, q, cap=200000):
    t = F(1, q * min(ds))
    for _ in range(cap):
        way = [d for d in ds if nd(d * t) < F(1, q)]
        if not way: return t
        t = max((F(floor(d * t - F(1, q)) + 1) + F(1, q)) / d for d in way)
    raise RuntimeError('cap')

def bound(C, E):
    Es = sorted(E); best = None
    for i, j in zip(Es, Es[1:]):
        R = sorted({2 * c for c in C} | {abs(2 * e - i - j) for e in Es})
        assert len(R) <= 6 and 0 not in R
        b = 2 * cascade_q(R, 7)
        best = b if best is None or b < best else best
    return best

rows = []
for b in (61, 63, 65, 67, 68, 69):
    for d in (12, 14, 16, 18, 20):
        for f in (4, 5):
            for N in (10**4, 10**5, 10**6):
                C, E = [10, b], [j * d for j in range(f)]
                rows.append(('handoff family', C, E, N, run(10, b, d, f, N)['t']))
rnd = random.Random(61)
while len(rows) < 180 + 600:
    f = rnd.choice((2, 3, 4, 5, 6)); C = sorted(rnd.sample(range(1, 90), 7 - f)); E = [0] + sorted(rnd.sample(range(1, 90), f - 1))
    N = rnd.choice((56 * 90, 10**4, 10**5)); s = 1000
    V = [s] + [s + c for c in C] + [s + N + e for e in E]
    if len(set(V)) < 8: continue
    rows.append(('random', C, E, N, cascade_cap(readings(V, 0))[0]))
viol = 0; ratios = []
for kind, C, E, N, t in rows:
    B = bound(C, E)
    if t > B + F(1, N): viol += 1; print("  VIOLATION", kind, C, E, N, t, B)
    ratios.append(float(B / t))
ratios.sort()
print(f"{len(rows)} arrangements (180 handoff-family, {len(rows)-180} random, f = 2..6): violations of t* <= B + 1/N: {viol}")
print(f"  B / t*: min {ratios[0]:.3f}, median {ratios[len(ratios)//2]:.3f}, 90th pct {ratios[int(.9*len(ratios))]:.3f}, max {ratios[-1]:.3f}")
