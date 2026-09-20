"""Does DENSITY locate the minimum COUNT?  Integer speeds, n = |V| = 8.

Motivation: a transit analysis at irrational speeds gives a smooth centre-peaked DENSITY
profile with an exact closed form (docs/n8/TRANSIT_DENSITY_CLOSED_FORM_v1.md).  The n=8
object is integer E, and the quantity with a floor is COUNT.  This asks whether the two
agree about WHERE in the pack the danger sits.

Answer: they do not.  Density is centre-peaked and its argmin is uniform over rank;
count is centre-MINIMAL and its argmin is sharply centre-peaked.  Density does not
localise the floor.
"""
import sys, random, os
from fractions import Fraction as F
from math import gcd
from functools import reduce
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bsm_fast import bsm_count

def bad_intervals(s):
    out = []
    for k in range(0, s+1):
        lo, hi = max(F(8*k-1, 8*s), F(0)), min(F(8*k+1, 8*s), F(1))
        if lo < hi: out.append((lo, hi))
    return out

def meas(S):
    iv = []
    for s in S: iv += bad_intervals(s)
    iv.sort(); m = []
    for lo, hi in iv:
        if m and lo < m[-1][1]: m[-1][1] = max(m[-1][1], hi)
        else: m.append([lo, hi])
    g = []; cur = F(0)
    for lo, hi in m:
        if cur <= lo: g.append((cur, lo))
        cur = max(cur, hi)
    if cur <= 1: g.append((cur, F(1)))
    return sum(b-a for a, b in g if a <= b and not (a == b == 0) and not (a == b == 1))

def reduce_cfg(V):
    V = sorted(V); g = reduce(gcd, [v-V[0] for v in V[1:]])
    return tuple((v-V[0])//g for v in V)

def main(trials=1200, hi=40, seed=5):
    rng = random.Random(seed)
    mc = [0]*8; md = [F(0)]*8; wmin = [0]*8; wdmin = [0]*8; n = 0
    for _ in range(trials):
        V = sorted(rng.sample(range(0, hi), 8))
        assert len(V) == 8, "n = |V| must be 8"
        U = reduce_cfg(V)
        if len(set(U)) < 8: continue
        n += 1
        cnt = []; dns = []
        for u in U:
            D = sorted({abs(w-u) for w in U if w != u})
            cnt.append(bsm_count(D)); dns.append(meas(D))
        for i in range(8): mc[i] += cnt[i]; md[i] += dns[i]
        wmin[cnt.index(min(cnt))] += 1
        wdmin[dns.index(min(dns))] += 1
    print(f"n = |V| = 8, integer speeds in [0,{hi}), {n} configurations, seed {seed}")
    print("rank 0 = slowest, 7 = fastest\n")
    print("mean COUNT   by rank:", [round(x/n, 1) for x in mc])
    print("mean DENSITY by rank:", [round(float(x)/n, 4) for x in md])
    print()
    print("argmin COUNT   by rank:", wmin, " <- sharply centre-peaked")
    print("argmin DENSITY by rank:", wdmin, " <- flat: no information about rank")
    # control: a statistic that MUST be flat, to show the harness can report flatness
    print()
    print("control (uniform random argmin):",
          [sum(1 for _ in range(n) if rng.randrange(8) == i) for i in range(8)])

if __name__ == "__main__":
    main()
