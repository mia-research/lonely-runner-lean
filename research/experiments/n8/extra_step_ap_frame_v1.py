"""Extra-step cases (actual scale > dead-lattice prediction P), integer speeds, in the AP-deviation frame.
Subject i, own d_min m (integer).  At scale P the AP instants are t = p/(8 P m), p odd, one period (p < 8Pm/g... use
p < 8P*m).  Runner j (difference e) is displaced e*p/(8Pm) laps; it blocks p when that is within 1/8 of an integer.
Types, with N = 8Pm, h = gcd(e,N), m' = N/h:
  whole wrap   m' = 1              (displacement integer at every instant; cannot happen at a live P)
  partial wrap m' odd > 1          (displacement exactly integer at the instants p = 0 mod m')
  near slot    m' even             (never exactly integer; only within 1/8)
Report per extra-step case: how many runners of each type block something, whether the instants are covered
without the partial wraps, and the smallest number of runners that cover all instants."""
import sys, random
from fractions import Fraction as F
from math import gcd
from functools import reduce
from itertools import combinations
from collections import Counter
from multiprocessing import Pool
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/experiments/n8")
    from scale_jump_battery_v1 import least_L, predicted_L
def blocked(e, p, N):
    R = (e * p) % N
    return 8 * min(R, N - R) < N
def job(V):
    V = [int(v) for v in V]; out = []
    Vf = [F(v) for v in V]
    for i in range(8):
        L, u, mm = least_L(Vf, i); P = predicted_L(Vf, i)
        if L is None or L == P: continue
        ds = [abs(V[j] - V[i]) for j in range(8) if j != i]; m = min(ds)
        N = 8 * P * m
        ps = list(range(1, N, 2))
        cover = {}; types = {}
        for e in ds:
            h = gcd(e, N); mp = N // h
            types[e] = "whole" if mp == 1 else ("partial wrap" if mp % 2 else "near slot")
            cover[e] = frozenset(p for p in ps if blocked(e, p, N))
        allp = frozenset(ps)
        assert frozenset().union(*cover.values()) == allp, "P should be fully covered"
        blockers = [e for e in ds if cover[e]]
        tc = Counter(types[e] for e in blockers)
        without_partial = frozenset().union(*[cover[e] for e in ds if types[e] != "partial wrap"]) == allp
        minimal = next(k for k in range(1, 8) if any(frozenset().union(*[cover[e] for e in c]) == allp
                                                      for c in combinations(blockers, k)))
        has_wrap_partner = any(e % (8 * m) == 0 for e in ds)
        out.append(dict(extra=L - P, types=tuple(sorted(tc.items())), without_partial=without_partial,
                        minimal=minimal, wrap=has_wrap_partner, P=P))
    return out
if __name__ == "__main__":
    rng = random.Random(20)
    fams = [("all 8-subsets of [1,16], gcd 1", [c for c in combinations(range(1, 17), 8) if reduce(gcd, c) == 1]),
            ("random [1,100]", [tuple(sorted(rng.sample(range(1, 101), 8))) for _ in range(1500)])]
    with Pool(8) as pool:
        for name, arrs in fams:
            recs = [x for r in pool.map(job, arrs, chunksize=16) for x in r]
            print(f"\n=== {name}: {len(recs)} extra-step runners")
            print("   the subject also has a whole-wrap partner (a jump was needed at all):", Counter(x["wrap"] for x in recs))
            print("   predicted scale P:", dict(sorted(Counter(x["P"] for x in recs).items())))
            print("   covered WITHOUT any partial-wrap runner:", Counter(x["without_partial"] for x in recs))
            print("   fewest runners that cover every instant at P:", dict(sorted(Counter(x["minimal"] for x in recs).items())))
            print("   blocker types present (type, count):", Counter(x["types"] for x in recs).most_common(6))
