"""Does the cascade arrive for four differences at n = 5?

The Lean result `FourDifferences.four_diffs_stop_ge_six` gives arrival within 7 moves for
`ds.card <= 4` at every `n >= 6`.  Its counting bound `g n 1 * (g n 3)^2 <= n - 1` fails at
n = 5, so the case (k = 4, n = 5) is not covered.  A subject at order 5 has at most 4
differences, so this is exactly what closing order 5 natively requires.

Exact rational arithmetic throughout (`fractions.Fraction`): an opening puts a runner at
circle distance exactly 1/n, so the `< 1/n` test is decided ON the boundary and floating
point would misjudge it.

`move` commutes with positive scaling of `ds`, so integer difference sets cover every
rational difference set.  Irrational ratios are NOT covered by this sweep.
"""
import random, math, sys
from fractions import Fraction as F
from itertools import combinations

N = 5
INV = F(1, N)
CAP = 200   # move cap; a cap-hit is reported as NON-ARRIVAL, never as arrival

def circDist(x):
    fr = x - math.floor(x)
    return min(fr, 1 - fr)

def inWay(d, t):
    return circDist(d * t) < INV

def nextOpening(d, t):
    return (F(math.ceil(d * t - INV)) + INV) / d

def cascade(ds):
    """Return (arrived, moves). arrived False means the cap was hit, not that it loops."""
    a = min(ds)
    t = F(1, 1) / (N * a)
    for j in range(CAP):
        act = [d for d in ds if inWay(d, t)]
        if not act:
            return True, j
        t = max(nextOpening(d, t) for d in act)
    return False, CAP

def run(name, sets):
    worst, worst_set, fails, cnt = -1, None, [], 0
    for ds in sets:
        cnt += 1
        ok, mv = cascade(ds)
        if not ok:
            fails.append(ds)
        elif mv > worst:
            worst, worst_set = mv, ds
    print(f"{name:<34} tested {cnt:>7}   max moves {worst:>3}   at {worst_set}   NON-ARRIVAL {len(fails)}")
    for f in fails[:5]:
        print(f"    !! non-arrival: {f}")
    return worst, fails

random.seed(20260920)
allworst, allfails = -1, []

def note(w, f):
    global allworst, allfails
    allworst = max(allworst, w); allfails += f

# 1. exhaustive: all 4-subsets of 1..34 with gcd 1
ex = [c for c in combinations(range(1, 35), 4) if math.gcd(math.gcd(c[0], c[1]), math.gcd(c[2], c[3])) == 1]
note(*run("exhaustive 4-subsets of 1..34", [tuple(F(x) for x in c) for c in ex]))

# 2. shuffled random over a wide range (not lexicographic)
rs = []
for _ in range(200000):
    hi = random.choice([50, 200, 1000, 10**4, 10**6])
    c = tuple(sorted(random.sample(range(1, hi + 1), 4)))
    rs.append(tuple(F(x) for x in c))
note(*run("random, mixed scales to 1e6", rs))

# 3. near arithmetic progressions
ap = []
for _ in range(60000):
    a0 = random.randint(1, 500); d = random.randint(1, 500)
    c = sorted({a0 + i * d + random.randint(-2, 2) for i in range(4)})
    if len(c) == 4 and all(x > 0 for x in c):
        ap.append(tuple(F(x) for x in c))
note(*run("near arithmetic progressions", ap))

# 4. ratios near the values that make the counting bound tight (8/7, 6/5, 5/4, 4/3)
rt = []
for _ in range(60000):
    base = random.randint(20, 5000)
    r = random.choice([F(8,7), F(6,5), F(5,4), F(4,3), F(7,6), F(9,8), F(11,10)])
    c = [F(base)]
    for _ in range(3):
        c.append(c[-1] * r + F(random.randint(-1, 1)))
    c = sorted(set(x for x in c if x > 0))
    if len(c) == 4:
        rt.append(tuple(c))
note(*run("ratios near 8/7, 6/5, 5/4, 4/3", rt))

# 5. one very small difference against three large (extreme spread)
sp = []
for _ in range(60000):
    a0 = random.randint(1, 3)
    rest = sorted(random.sample(range(1000, 10**6), 3))
    sp.append(tuple(F(x) for x in (a0, *rest)))
note(*run("extreme spread (1 tiny, 3 large)", sp))

# 6. tight clusters just above the minimum
cl = []
for _ in range(60000):
    a0 = random.randint(100, 10000)
    c = sorted({a0 + random.randint(1, 6) for _ in range(6)} | {a0})
    if len(c) >= 4:
        cl.append(tuple(F(x) for x in c[:4]))
note(*run("tight clusters", cl))

print()
print(f"OVERALL   max moves observed: {allworst}    total non-arrivals: {len(allfails)}")
print(f"CAP was {CAP}; a cap-hit would be reported as NON-ARRIVAL.")
