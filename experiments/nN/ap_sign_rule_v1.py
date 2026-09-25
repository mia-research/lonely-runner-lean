"""Small deformations of the AP: which global instant a/8 survives (Theorems 4-6).

Disparities k + e_k (k = 1..7), e_k small.  At t = a/8 (a a unit mod 8) runner k sits at the vertex
k*a/8 displaced by e_k*a/8; the two runners on the boundary are k = a^-1 (at 1/8, needs e_k >= 0)
and k = -a^-1 (at 7/8, needs e_k <= 0).  Prediction:
    a = 1 survives iff e1 >= 0 >= e7;   a = 7 iff e7 >= 0 >= e1;
    a = 3 survives iff e3 >= 0 >= e5;   a = 5 iff e5 >= 0 >= e3;
so every global instant is lost iff (e1, e7) are both nonzero of one sign and (e3, e5) likewise.
Checked exactly against the instants a/8 on random deformations with |e_k| <= 10^-3 (some zero).
"""
import random
from fractions import Fraction as F
def nd(x): x = x % 1; return min(x, 1 - x)
random.seed(3); agree = 0; N = 20000; lost = 0
for _ in range(N):
    e = {k: random.choice([0, F(random.randint(-1000, 1000), 10 ** 6)]) for k in range(1, 8)}
    ds = [k + e[k] for k in range(1, 8)]
    actual = {a for a in (1, 3, 5, 7) if all(nd(d * F(a, 8)) >= F(1, 8) for d in ds)}
    pred = set()
    if e[1] >= 0 >= e[7]: pred.add(1)
    if e[7] >= 0 >= e[1]: pred.add(7)
    if e[3] >= 0 >= e[5]: pred.add(3)
    if e[5] >= 0 >= e[3]: pred.add(5)
    agree += actual == pred; lost += not actual
print(f"{N} random small deformations of 1..7: predicted surviving instants match exactly in {agree}; all four lost in {lost}")

# Where does the isolation go when all four global instants are lost?
from collections import Counter
import math
def cascade(ds):
    t = F(1, 8) / min(ds); m = 0
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t, m
        nxt = []
        for d in way:
            N = math.floor(d * t - F(1, 8)); o = (N + F(1, 8)) / d
            if o < t: o = (N + 1 + F(1, 8)) / d
            nxt.append(o)
        t = max(nxt); m += 1
random.seed(5); where = Counter(); ex = []
while sum(where.values()) < 200:
    e = {k: F(random.randint(1, 1000), 10 ** 6) * random.choice([-1, 1]) for k in range(1, 8)}
    if not ((e[1] > 0) == (e[7] > 0) and (e[3] > 0) == (e[5] > 0)): continue
    ds = [k + e[k] for k in range(1, 8)]
    t, m = cascade(ds)
    near = min((abs(t - F(j, 8)), j) for j in range(0, 17))
    where[(near[1], m)] += 1
    if len(ex) < 4: ex.append((float(t), m, {k: float(v) for k, v in e.items()}))
print("all four lost -- first isolation near j/8 (j, cascade moves):", sorted(where.items()))
for x in ex: print("   e.g. T =", x[0], "moves", x[1])
