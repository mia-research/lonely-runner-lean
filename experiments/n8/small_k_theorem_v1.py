"""Would a theorem for small k close ExistenceAt8, or does coverage saturate?

The mirror of Theorem 4.8: at flank e's k-th opening, every runner is clear iff every ratio
d/e lies in  U_M [(8M+1)/(8k+1), (8M+7)/(8k+1)].  k = 0 is Theorem 4.8 itself.

A theorem 'all ratios in the k-th band -> lonely' is immediate for any fixed k. The real
question is what the DISJUNCTION over k <= K covers, and whether it tends to 100%.
Measured at the flank d_min, and then allowing ANY flank.
"""
import random
from fractions import Fraction as F

def circd(x):
    f = x - (x.numerator // x.denominator)
    return min(f, 1 - f)

def clear_at(ds, e, k):
    t = (F(k) + F(1, 8)) / e
    return all(circd(d * t) >= F(1, 8) for d in ds)

rng = random.Random(20260917)
def gen(kind):
    while True:
        if kind == "real":
            s = {F(rng.randint(1, 10**6), 1000) for _ in range(7)}
        elif kind == "int":
            s = set(F(x) for x in rng.sample(range(1, 200), 7))
        else:
            s = {F(rng.randint(1, 60), rng.choice([1, 2, 3, 4, 6, 8])) for _ in range(7)}
        if len(s) == 7: return sorted(s)

KS = [0, 1, 2, 3, 5, 10, 20, 50, 200, 1000, 5000]
for kind, N in (("real", 2500), ("int", 2500), ("small-denominator", 2500)):
    dmin_cov = {K: 0 for K in KS}
    anyf_cov = {K: 0 for K in KS}
    for _ in range(N):
        ds = gen(kind)
        e0 = min(ds)
        first_dmin = None; first_any = None
        for k in range(KS[-1] + 1):
            if first_dmin is None and clear_at(ds, e0, k): first_dmin = k
            if first_any is None:
                for e in ds:
                    if clear_at(ds, e, k): first_any = k; break
            if first_dmin is not None and first_any is not None: break
        for K in KS:
            if first_dmin is not None and first_dmin <= K: dmin_cov[K] += 1
            if first_any is not None and first_any <= K: anyf_cov[K] += 1
    print(f"=== {kind}, {N} difference sets ===")
    print(f"   {'K':>6} {'flank d_min':>14} {'any flank':>12}")
    for K in KS:
        print(f"   {K:>6} {100*dmin_cov[K]/N:>13.1f}% {100*anyf_cov[K]/N:>11.1f}%")
    print()
