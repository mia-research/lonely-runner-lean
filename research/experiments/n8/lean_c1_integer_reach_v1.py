import random
from math import gcd, floor
from functools import reduce
from itertools import combinations
from fractions import Fraction as F
from collections import Counter
def dist(x): x = x - floor(x); return min(x, 1-x)
def classify(V, i):
    v = V[i]; ds = [abs(v-w) for w in V if w != v]; m = min(ds)
    if any(d % m for d in ds): return "non-integral readings", None
    s = [d//m for d in ds]
    blocked = [x for x in s if x % 8 == 0]
    if not blocked: return "unblocked (spine u=1/8 works)", None
    if len(blocked) > 1 or max(s) not in blocked: return "integral, blocked, outside the lemma's hypotheses", None
    Sb = max(s); unb = [x for x in s if x % 8]
    for p in (1, 3, 5, 7):
        if all(1 <= (x*p) % 8 <= 6 for x in unb):
            u = F(p, 8) + F(1, 8*Sb); t = u / m
            ok = all(dist(d*t) >= F(1, 8) for d in ds)
            return "construction applies", (p, u, t, ok)
    return "integral, one blocked (largest), no unit p fits", None
V = (1,2,3,4,5,6,7,9)
print("(1..7,9) runner 1:", classify(V, 0))
c = Counter(); bad = 0
arrs = [x for x in combinations(range(1, 21), 8) if reduce(gcd, x) == 1]
for W in arrs:
    for i in range(8):
        k, res = classify(W, i); c[k] += 1
        if res and not res[3]: bad += 1
print("all 8-subsets of [1,20], every runner:")
for k, n in c.most_common(): print(f"   {k}: {n}")
print("instants produced by the construction that fail the exact check:", bad)
