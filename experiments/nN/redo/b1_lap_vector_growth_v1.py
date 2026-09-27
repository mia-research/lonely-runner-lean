"""E120: do the band's landing lap vectors saturate as shapes get finer?  Exhaustive to N = 20, 24, 30, 36, 40;
plus random fine shapes (d1 up to 2000).  The set of ALL compatible lap vectors per set is not needed: the cascade's
landing lap vector is its least one."""
import itertools, random, sys
from fractions import Fraction as F
from math import floor
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def land(T):
    t = F(1, 8 * T[0])
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return tuple(int(d * t) for d in T)
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
seen = set()
for N in (20, 24, 30, 36, 40):
    for T in itertools.combinations(range(1, N + 1), 7):
        if 7 * T[0] < T[-1] < 9 * T[0]: seen.add(land(T))
    print("exhaustive to", N, ": lap vectors so far", len(seen)); sys.stdout.flush()
rnd = random.Random(7); new = set()
for trial in range(40000):
    d1 = rnd.randrange(40, 2000); top = rnd.randrange(7 * d1 + 1, 9 * d1)
    T = tuple(sorted([d1, top] + rnd.sample(range(d1 + 1, top), 5)))
    v = land(T)
    if v not in seen: new.add(v)
print("random fine shapes (40,000, d1 in [40, 2000)): new lap vectors not seen to 40:", len(new), sorted(new)[:20])
