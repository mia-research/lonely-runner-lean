"""What in the n=8 Spec layer does NOT generalise.

Every THEOREM ported (105/105 axiom-clean).  What cannot port is (a) an arithmetic role a
theorem plays at n=8, and (b) the n=8 measurements attached to particular doors.  Three checks.
"""
import math, random
from fractions import Fraction as F
from itertools import combinations

# ---------- CHECK 1: the excess of the difference-set form over the conjecture ----------
# A value d occurs as |v i - v k| for at most TWO runners (v k +- d).  So a difference set
# realised by an arrangement of n runners needs 2*card >= n-1, i.e. card >= ceil((n-1)/2).
# The EXCESS that ExistenceAtN asks beyond the conjecture is card < ceil((n-1)/2).
# At n=8 that is card <= 3, settled by three_diffs (n>=4).  Does it stay settled?
print("=== CHECK 1: is the excess case still covered by a termination theorem? ===")
print(f"{'n':>3} {'excess card <=':>14} {'covering theorem':>34} {'covered':>8}")
def covers(k, n):
    if k <= 2 and n >= 3: return "two_diffs (n>=3)"
    if k <= 3 and n >= 4: return "three_diffs (n>=4)"
    if k <= 4 and n >= 6: return "four_diffs (n>=6)"
    if 2**(k-1) <= n and n >= 9: return f"slowest_recursion (n>=max(9,2^{k-1}))"
    return None
first_fail = None
for n in range(5, 21):
    E = -(-(n-1)//2) - 1          # ceil((n-1)/2) - 1
    c = covers(E, n) if E >= 1 else "vacuous"
    ok = c is not None
    if not ok and first_fail is None: first_fail = n
    print(f"{n:>3} {E:>14} {str(c):>34} {str(ok):>8}")
print(f"\n  -> excess case first UNCOVERED at n = {first_fail}")

# ---------- machinery ----------
def mk(N):
    INV = F(1, N)
    def circDist(x):
        fr = x - math.floor(x); return min(fr, 1 - fr)
    def lonely(ds, t): return all(circDist(d*t) >= INV for d in ds)
    def inWay(d, t): return circDist(d*t) < INV
    def nextOpening(d, t): return (F(math.ceil(d*t - INV)) + INV)/d
    def flankOpening(e, j): return (F(j) + INV)/e
    def cascade(ds, cap=100000):
        a = min(ds); t = F(1,1)/(N*a)
        for _ in range(cap):
            act = [d for d in ds if inWay(d, t)]
            if not act: return t
            t = max(nextOpening(d, t) for d in act)
        return None
    return circDist, lonely, flankOpening, cascade

# ---------- CHECK 2: door 5 -- is "one of the THREE largest" still the right number? ----------
print("\n=== CHECK 2: door 5, best flank rank from the large end (n=8 claim: never worse than 3) ===")
random.seed(3)
for N in [5, 6, 7, 8]:
    circDist, lonely, flankOpening, cascade = mk(N)
    k = N - 1                      # a subject has n-1 differences
    worst, wset, dist = 0, None, {}
    tested = 0
    for _ in range(4000):
        hi = random.choice([20, 30, 45, 70])
        c = tuple(sorted(random.sample(range(1, hi+1), k)))
        if math.gcd(*c) != 1: continue
        ds = [F(x) for x in c]
        tested += 1
        srt = sorted(ds, reverse=True)     # rank 1 = largest
        best = None
        for r, e in enumerate(srt, 1):
            if any(lonely(ds, flankOpening(e, j)) for j in range(int(e)+1)):
                best = r; break
        if best is None: best = 99
        dist[best] = dist.get(best, 0) + 1
        if best > worst: worst, wset = best, c
    print(f"  n={N}  k={k}  tested {tested:>5}   worst rank {worst}   distribution {dict(sorted(dist.items()))}   witness {wset}")

# ---------- CHECK 3: DoorFirstLap -- is tau = e*t <= 1? (REFUTED at n=8) ----------
print("\n=== CHECK 3: DoorFirstLap, tau = leastDisp * arrival (n=8: REFUTED, tau=2401/1872) ===")
for N in [5, 6, 7, 8]:
    circDist, lonely, flankOpening, cascade = mk(N)
    k = N - 1
    worst, wset = F(0), None
    tested = 0
    for _ in range(6000):
        hi = random.choice([20, 40, 80, 200, 500])
        c = tuple(sorted(random.sample(range(1, hi+1), k)))
        if math.gcd(*c) != 1: continue
        ds = [F(x) for x in c]
        tested += 1
        t = cascade(ds)
        if t is None: continue
        tau = min(ds) * t
        if tau > worst: worst, wset = tau, c
    verdict = "REFUTED (tau > 1 found)" if worst > 1 else "no counterexample in this sample"
    print(f"  n={N}  tested {tested:>5}   max tau {str(worst):>12} = {float(worst):.5f}   {verdict}   witness {wset}")
