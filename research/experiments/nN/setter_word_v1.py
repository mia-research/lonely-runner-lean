"""Why n=4 and not n=5: the n=4 proof EXHAUSTS the setter pool.

`four_stops_within_three_moves` runs: the nearest runner `a` is clear on the whole window
[1/4,3/4] (`aclear`), so no move is ever set by `a`; move 1 has setter x1 != a; move 2 has
x2 != a and x2 != x1.  With card ds <= 3 that leaves NOTHING for move 3, so the cascade is fixed.
Pool size = (n-1) - 1 = 2 at n=4.

At n=5 the pool is 3.  Consecutive setters still differ, and `no_four_alternation` (W2) forbids
a 2-cycle y,z,y -- but nothing in the tree forbids a 3-CYCLE x,y,z,x.  So the question that
decides whether the same argument transfers is simply: DO setters repeat at n=5?
"""
from fractions import Fraction as F
from itertools import combinations
import math, collections
def circ(x):
    fl = x - (x.numerator // x.denominator)
    return min(fl, 1 - fl)
def cascade(ds, n):
    """exact cascade from 1/(n*d_min); returns the setter word"""
    m = min(ds); t = F(1, n * m); word = []
    for _ in range(200):
        inway = [d for d in ds if circ(F(d) * t) < F(1, n)]
        if not inway: return word, t, True
        best = None; setter = None
        for d in inway:
            k = math.ceil(F(d) * t - F(1, n))
            op = (F(k) + F(1, n)) / F(d)
            while op < t: k += 1; op = (F(k) + F(1, n)) / F(d)
            if best is None or op > best: best, setter = op, d
        t = best; word.append(setter)
    return word, t, False
for n, k, HI in ((4, 3, 40), (5, 4, 40)):
    lens = collections.Counter(); rep = 0; tot = 0; maxlen = 0; examples = []
    poolmax = 0
    for c in combinations(range(1, HI + 1), k):
        g = c[0]
        for x in c[1:]: g = math.gcd(g, x)
        if g != 1: continue
        tot += 1
        w, t, done = cascade(c, n)
        lens[len(w)] += 1; maxlen = max(maxlen, len(w))
        poolmax = max(poolmax, len(set(w)))
        if len(w) != len(set(w)):
            rep += 1
            if len(examples) < 5: examples.append((c, w))
    print(f"n={n}, {k} disparities, primitive sets in [1,{HI}]: {tot}")
    print(f"  setter-pool size available (card - 1)      : {k-1}")
    print(f"  cascade length distribution                : {dict(sorted(lens.items()))}")
    print(f"  longest cascade                            : {maxlen}")
    print(f"  distinct setters ever used in one cascade  : max {poolmax}")
    print(f"  cascades where a setter REPEATS            : {rep}")
    if examples: print(f"    e.g. {examples[:3]}")
    print()
