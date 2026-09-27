"""E125: the cascade as a chain of windows; its junctions and their orientation.  A window of runner i, lap k: the open
R-interval ((8k-1)/s_i, (8k+1)/s_i).  The cascade's moves are the chain: at each move the latest-ending window among the
blockers ends at the next R.  A junction (a, k) -> (b, l): the chain passes because b's window l contains the end of a's
window k.  At the landing R*, the chain breaks: a runner a leaves (R* = (8k+1)/s_a) and no window contains R*.
For each late shape: the breaking pair (a, next runner b to enter after R*), and whether the same unordered pair {a, b}
appears in the chain as a passing junction, and in which orientation (a -> b or b -> a).  Exact."""
import random
from fractions import Fraction as F
from math import floor
from collections import Counter
D1 = 27720
def chain(s):
    R = F(1); J = []
    while True:
        win = [(i, round(x * R / 8)) for i, x in enumerate(s) if abs(x * R - 8 * round(x * R / 8)) < 1]
        if not win: return R, J
        ends = [(F(8 * k + 1) / s[i], i, k) for i, k in win]
        Rn, a, k = max(ends)
        nxt = [(i, round(x * Rn / 8)) for i, x in enumerate(s) if abs(x * Rn - 8 * round(x * Rn / 8)) < 1]
        for b, l in nxt: J.append((a, k, b, l))
        R = Rn
def next_entry(s, R):
    best = None
    for i, x in enumerate(s):
        k = floor(x * R / 8 + F(1, 8)) + 1 if (x * R) % 8 >= 7 else floor(x * R / 8) + 1
        st = F(8 * k - 1) / x
        while st <= R: k += 1; st = F(8 * k - 1) / x
        if best is None or st < best[0]: best = (st, i, k)
    return best
SEEDS = [(1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378), (1, 2.5302, 3.2218, 4.1563, 4.531, 5.6544, 7.0302),
         (1, 3.15, 4.2099, 4.7242, 5.225, 5.7897, 7.4429)]
rnd = random.Random(12); c = Counter(); shapes = []
for sd in SEEDS:
    T = [int(round(x * D1)) for x in sd]
    for step in range(1500):
        L = list(T); i = rnd.randrange(1, 7); L[i] += rnd.randrange(-500, 501)
        U = sorted(set(L))
        if len(U) < 7 or U[0] != D1 or not (7 * D1 < U[-1] < 9 * D1): continue
        s = [F(d, D1) for d in U]; R, J = chain(s)
        if R > 7:
            T = U
            if step % 15 == 0: shapes.append((s, R, J))
for s, R, J in shapes:
    a = next(i for i, x in enumerate(s) if ((x * R - 1) / 8).denominator == 1)
    st, b, l = next_entry(s, R)
    same = [(x, y) for (x, k, y, l2) in J if {x, y} == {a, b}]
    orient = 'no passing junction of this pair' if not same else ('same orientation a->b passed' if any(x == a for x, y in same) and not any(x == b for x, y in same) else ('opposite b->a passed' if all(x == b for x, y in same) else 'both orientations passed'))
    c[orient] += 1
print("late shapes:", len(shapes)); [print("   %4d  %s" % (v, k)) for k, v in c.most_common()]
