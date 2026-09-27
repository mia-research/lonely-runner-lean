"""E116: what one move of one runner contains.  Exact arithmetic only.

first_lonely(ds, delta): earliest t > 0 with ||d t|| >= delta for every d (boundary set method:
the earliest lonely instant is an opening (N + delta)/d of some reading, or t with every reading
clear; lonely set closed, so its infimum is attained at an opening).
"""
from fractions import Fraction as F
import math, random

def dist(x):
    f = x - math.floor(x)
    return min(f, 1 - f)

def lonely(ds, t, delta):
    return all(dist(d * t) >= delta for d in ds)

def first_lonely(ds, delta, tmax):
    cands = []
    for d in ds:
        N = 0
        while True:
            t = (N + delta) / d
            if t > tmax: break
            cands.append(t); N += 1
    for t in sorted(set(cands)):
        if lonely(ds, t, delta):
            return t
    return None

# (1) positive control for the escape: X = readings 1..7 is lonely at 1/8 only at the tight instants;
#     at threshold 1/8 + 1/1000 X is NOT lonely.  Move reading 7 to 7 + eps.
print("(1) moving reading 7 of (1..7) by eps; first lonely time")
for delta, name in ((F(1, 8), "delta = 1/8 (X lonely)"), (F(1, 8) + F(1, 1000), "delta = 1/8 + 1/1000 (X not lonely)")):
    print("  ", name)
    for eps in (F(1, 10), F(1, 100), F(1, 1000), F(1, 10000)):
        ds = [F(1), F(2), F(3), F(4), F(5), F(6), F(7) + eps]
        t = first_lonely(ds, delta, F(2000))
        print("     eps = %-8s first lonely t = %s (%.3f)" % (eps, t, float(t) if t else -1))

# (2) the one-free lemma: six fixed rational readings, lonely at 1/7 at t7 (found by scan),
#     x with x*P0 not an integer  =>  lonely at t7 + m P0 for some m <= ceil(1/(4 ||x P0||)).
print("(2) one-free lemma on random six-sets")
random.seed(1)
bad = 0; tested = 0
for trial in range(3000):
    six = sorted(random.sample(range(1, 40), 6))
    six = [F(d) for d in six]
    g = math.gcd(*[int(d) for d in six])
    P0 = F(1, g)
    t7 = first_lonely(six, F(1, 7), F(10))
    assert t7 is not None
    den = random.choice([3, 5, 7, 8, 11, 16, 97])
    x = F(random.randint(1, 60 * den), den)
    a = x * P0
    if a.denominator == 1: continue
    alpha = dist(a)
    M = math.ceil(1 / (4 * alpha))
    ok = any(lonely(six + [x], t7 + m * P0, F(1, 8)) for m in range(M + 1))
    tested += 1
    if not ok: bad += 1; print("  FAIL", six, x)
print("   tested %d, failures %d" % (tested, bad))
