"""Is the required denominator BOUNDED?  A range sweep says 19 and is stable over [1,30]..[1,50],
but the condition at q depends only on d mod q, so range stability is weak evidence.  This builds
tuples designed to fail small q -- a d divisible by q kills q outright -- and pushes the budget."""
from fractions import Fraction as F
import random, math
n = 5
def min_q(ds, Q=400):
    for q in range(2, Q+1):
        for a in range(1, q):
            if math.gcd(a,q) != 1: continue
            ok = True
            for d in ds:
                r = (d*a) % q
                if not (F(1,n) <= min(F(r,q), 1 - F(r,q))): ok = False; break
            if ok: return q
    return None
random.seed(11)
pool = [2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32]
print(f"{'budget':>9} {'max min-q':>10}   witness")
best = (0, None)
for budget in (2000, 10000, 40000, 160000):
    for _ in range(budget):
        parts = [[] for _ in range(4)]
        for q in pool: parts[random.randrange(4)].append(q)
        ds = []
        for p in parts:
            v = 1
            for q in p: v = v*q//math.gcd(v,q)
            ds.append(v*random.randint(1,12))
        ds = tuple(sorted(ds))
        if len(set(ds)) < 4: continue
        q = min_q(ds)
        if q is None: print("  NO q <= 400 at", ds); break
        if q > best[0]: best = (q, ds)
    print(f"{budget:>9} {best[0]:>10}   {best[1]}")
print()
print("The hard tuples are each divisible by a DIFFERENT set of small moduli -- a CRT spread.")
print("gcd of the witness:", math.gcd(math.gcd(best[1][0],best[1][1]), math.gcd(best[1][2],best[1][3])))
print("factorisations:", [ [p for p in (2,3,5,7,11,13,17,19,23,29,31) if d%p==0] for d in best[1]])
